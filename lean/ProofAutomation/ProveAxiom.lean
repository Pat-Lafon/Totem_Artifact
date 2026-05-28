import Lean
import ProofAutomation.Helpers

open Lean Elab Tactic Meta

/-! # ProveAxiom — auto-prove axioms using grind/cases/induction strategies

Strategies are tried in order, cheapest first. Each backtracks on failure.

0. **intro-only + grind**: flatten foralls *without* refining existentials,
   then grind. Handles `… → ∃ x, P[x] → Q[x]` shapes where the implication
   premise pins the witness — eager `refine ⟨_, ?_⟩` (used by later
   strategies) would commit `x` to a metavariable before the premise is
   intro'd.
1. **grind**: flatten goal (intro all + destruct ∧/∃, refine ⟨_, ?_⟩ for
   leading ∃), then grind.
2. **simp_all + grind**: same, but simp_all first to unfold wrappers in
   hypotheses so grind's E-matching triggers fire on the impl-level terms.
3. **cases + simp_all + grind**: flatten, case-split each inductive variable,
   then simp_all + grind per branch. Handles non-recursive definitions.
4. **early induction + simp_all + grind**: intro just the first inductive
   variable, induct on it (so the IH is properly quantified), intro the
   rest, then simp_all + grind. Handles recursive properties like
   num_black height non-negativity.
-/

def proveAxiomImpl : TacticM Unit := do
  let inductiveHyps ← withMainContext do
    let env ← getEnv
    let target ← instantiateMVars (← getMainTarget)
    let (_, inductiveNames) := scanForallIntros env target "_pax"
    return inductiveNames
  let tryGlobal (tac : TSyntax `tactic) : TacticM Bool :=
    withBacktrack do flattenGoal; evalTactic tac
  let tryPerHyp (prep : TacticM Unit) (mkTac : Ident → TacticM (TSyntax `tactic))
      : TacticM Bool := do
    for h in inductiveHyps do
      if ← withBacktrack do
        prep; evalTactic (eraseMacroScopesFromSyntax (← mkTac h))
      then return true
    return false
  let flatNoExists : TacticM Unit := flattenGoal (refineExists := false)
  -- Strategy 0: intro-only flatten + grind (leave existentials for grind)
  if ← withBacktrack do
    flatNoExists; evalTactic (← `(tactic| all_goals grind (splits := 20)))
  then return
  -- Strategy 1: flatten + grind
  if ← tryGlobal (← `(tactic| all_goals grind (splits := 20))) then return
  -- Strategy 2: flatten + simp_all + grind
  if ← tryGlobal (← `(tactic| all_goals (simp_all; try grind (splits := 20)))) then return
  -- Strategies 3-4 case-split / induct on user-inductive intro vars; if
  -- the goal has none, they're guaranteed no-ops. Stop here with a more
  -- informative error than "all strategies failed".
  if inductiveHyps.isEmpty then
    throwError "prove_axiom: grind and simp_all failed; \
      no inductive variables in goal, so cases/induction strategies were skipped"
  -- Strategy 3: cases + simp_all + grind
  if ← tryPerHyp flatNoExists fun h =>
    `(tactic| cases $h:ident <;> (simp_all; try grind (splits := 20))) then return
  -- Strategy 4: early induction + simp_all + grind
  if ← tryPerHyp (pure ()) fun h =>
    `(tactic| (intro $h:ident; induction $h:ident <;>
              (intros; simp_all; try grind (splits := 20)))) then return
  throwError "prove_axiom: all strategies failed"
