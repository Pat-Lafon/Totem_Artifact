import Lean
import ProofAutomation.Helpers
import ProofAutomation.RefineExistsEq

open Lean Elab Tactic Meta

/-! # SimpGoal — iteratively decompose a compound goal

  Goal-side analogue of `simp_hyps`. Each phase tries to make local progress
  on the main target; the loop drives every open goal to fixpoint and then
  closes whatever remains with `grind`.

  Phases (in order):
    - `trySimpIdentities`  — collapse `P ∨ False` / `False ∨ P` / `P ∧ True` /
                             `True ∧ P` so the structural phases below see
                             the simplified outermost connective
    - `tryAndIntro`        — `apply And.intro` on conjunctive goals
    - `tryRefineExistsEq`  — refine `∃ x, P[x]` when P pins x to a closed expr
    - `tryPickDisjunct`    — for `A ∨ B`, pick the branch whose complement
                             reduces to `False`; otherwise no progress

  New phases must match the `Expr → TacticM Bool` shape and be appended to
  the `phases` array in `simpGoalOnce`. -/

namespace ProofAutomation

private def trySimpIdentities (_target : Expr) : TacticM Bool := do
  tryTacticStep (evalTactic
    (← `(tactic| simp only [or_false, false_or, and_true, true_and])))

private def tryAndIntro (target : Expr) : TacticM Bool := do
  match_expr target with
  | And _ _ => tryTacticStep (evalTactic (← `(tactic| apply And.intro)))
  | _ => return false

private def tryRefineExistsEq (target : Expr) : TacticM Bool := do
  match_expr target with
  | Exists _ _ => tryTacticStep (evalTactic (← `(tactic| refine_exists_eq)))
  | _ => return false

private def tryPickDisjunct (target : Expr) : TacticM Bool := do
  match_expr target with
  | Or A B =>
    match ← reducedExpr A with
    | some false => tryTacticStep (evalTactic (← `(tactic| right)))
    | _ =>
      match ← reducedExpr B with
      | some false => tryTacticStep (evalTactic (← `(tactic| left)))
      | _ => return false
  | _ => return false

/-! ## Public entry points -/

-- Take a single step on the current main goal. Returns true on progress.
def simpGoalOnce : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let phases : Array (Expr → TacticM Bool) :=
    #[trySimpIdentities, tryAndIntro, tryRefineExistsEq, tryPickDisjunct]
  for phase in phases do
    if ← phase target then return true
  return false

-- One pass over every open goal. Returns true if any advanced.
private def simpGoalPass : TacticM Bool := do
  let gs ← getGoals
  let mut progressed := false
  let mut remaining : List MVarId := []
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    if ← simpGoalOnce then progressed := true
    remaining := remaining ++ (← getGoals)
  setGoals remaining
  return progressed

-- Drive all goals to fixpoint, then finish with `grind` on anything left.
partial def simpGoalLoop : TacticM Unit := do
  if (← getGoals).isEmpty then return
  if ← simpGoalPass then simpGoalLoop
  else
    try evalTactic (← `(tactic| any_goals grind))
    catch e => rethrowIfFatal e; pure ()

end ProofAutomation
