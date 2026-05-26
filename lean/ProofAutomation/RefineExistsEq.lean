import Lean
import ProofAutomation.Helpers

open Lean Elab Tactic Meta

/-! # RefineExistsEq — auto-witness an existential pinned by an equality conjunct

If the goal is `∃ x, P[x]` and `P` (under any nesting of `And`) contains a conjunct of the
form `x = e`, `e = x`, `(x == e) = true`, or `(e == x) = true` — where `e` does not mention
`x` — refine the existential with `e`. -/

namespace ProofAutomation

private def isBVarIdx (e : Expr) (idx : Nat) : Bool :=
  match e with
  | .bvar n => n == idx
  | _ => false

-- bvar at `depth` on one side, the other side closed over `depth`
private def tryEqSides (depth : Nat) (a b : Expr) : Option Expr :=
  if isBVarIdx a depth && !b.hasLooseBVar depth then some b
  else if isBVarIdx b depth && !a.hasLooseBVar depth then some a
  else none

partial def findEqWitness (depth : Nat) (e : Expr) : Option Expr :=
  match_expr e with
  | And a b => (findEqWitness depth a).orElse fun _ => findEqWitness depth b
  | Eq _ lhs rhs =>
    -- Plain `Eq`: x = e or e = x
    match tryEqSides depth lhs rhs with
    | some w => some w
    | none =>
      -- Bool form: `(a == b) = true` (in either argument order)
      match isBEqEq e with
      | some (true, a, b) => tryEqSides depth a b
      | _ => none
  | _ => none

def refineExistsEqImpl : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match_expr target with
  | Exists ty p =>
    match p with
    | .lam _ _ body _ =>
      match findEqWitness 0 body with
      | some witness =>
        -- `tryEqSides` already ruled out bvar 0 in the witness. The goal target
        -- should be closed, so the witness should have no loose bvars at all.
        -- Any remaining loose bvar (≥ 1) would get silently shifted by
        -- `lowerLooseBVars 1 1` into a malformed term — throw instead.
        if witness.hasLooseBVars then
          throwError "refine_exists_eq: witness has loose bvars (target not closed?): {witness}"
        let witness' := witness.lowerLooseBVars 1 1
        let goal ← getMainGoal
        let bodyApplied := body.instantiate1 witness'
        let newMVar ← mkFreshExprSyntheticOpaqueMVar bodyApplied
        let proof ← mkAppOptM ``Exists.intro
          #[some ty, some p, some witness', some newMVar]
        goal.assign proof
        replaceMainGoal [newMVar.mvarId!]
      | none =>
        throwError "refine_exists_eq: no equality conjunct pins the existential variable"
    | _ => throwError "refine_exists_eq: existential body is not a lambda"
  | _ => throwError "refine_exists_eq: goal is not ∃"

end ProofAutomation

elab "refine_exists_eq" : tactic => ProofAutomation.refineExistsEqImpl
