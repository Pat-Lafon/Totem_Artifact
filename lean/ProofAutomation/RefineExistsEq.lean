import Lean
import ProofAutomation.Helpers

open Lean Elab Tactic Meta

/-! # RefineExistsEq — auto-witness an existential pinned by an equality conjunct

If the goal is `∃ x, P[x]` and `P` contains a sub-formula of the form `x = e`, `e = x`,
`(x == e) = true`, or `(e == x) = true` — where `e` does not mention `x` — refine the
existential with `e`. The search recurses through `And`, nested `Exists`, and `→`
(picking witnesses from implication premises is sound because instantiating with the
witness reduces the equality premise to `e = e`; conclusion-side picks would not be). -/

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
  | Exists _ p =>
    match p with
    | .lam _ _ body _ => findEqWitness (depth + 1) body
    | _ => none
  | Eq _ lhs rhs =>
    -- Plain `Eq`: x = e or e = x
    match tryEqSides depth lhs rhs with
    | some w => some w
    | none =>
      -- Bool form: `(a == b) = true` (in either argument order)
      match isBEqEq e with
      | some (true, a, b) => tryEqSides depth a b
      | _ => none
  | _ =>
    -- Implication: recurse into both sides. Domain stays at the same depth;
    -- body sits under the implication binder so the outer bvar shifts by 1.
    -- Picking a witness from either side is sound — instantiating reduces a
    -- premise equality `x = e` to `e = e`, and from a conclusion equality
    -- still produces a stronger goal we can attempt.
    match e with
    | .forallE _ dom body _ =>
      (findEqWitness depth dom).orElse fun _ =>
        findEqWitness (depth + 1) body
    | _ => none

/-- True if `e` is an equality (plain `Eq` or BEq `(a == b) = true`) where
one side is the literal bound variable `bvar depth`. Used by
`bvarHasNegatedEq` to decide whether a `Not` subterm encodes a
*polarity-flipped pin* on the existential variable (the bivalued case
this check exists to catch) vs. an unrelated negated proposition (e.g.
`¬ res_0 > res_1`, which doesn't constrain `res_0` to any value). -/
private def isEqOnBVar (depth : Nat) (e : Expr) : Bool :=
  match_expr e with
  | Eq _ lhs rhs =>
    if isBVarIdx lhs depth || isBVarIdx rhs depth then true
    else
      match isBEqEq e with
      | some (true, a, b) => isBVarIdx a depth || isBVarIdx b depth
      | _ => false
  | _ => false

/-- True if `bvar depth` appears under a syntactic negation as one side of
an *equality*. Both negation encodings are checked: `Not P` (the surface
form before unfolding) and `forallE _ P False` (the unfolded definition).
Signals a bivalued existential — if the variable shows up as `x = e → …`
(a premise hint) and also as `¬ x = e → …` (opposite-polarity hint) in
the same body, the existential is case-split, not pinned, so
`refine_exists_eq` must not commit to a witness.

Crucially, this only fires when the negated subterm is itself an equality
on the bvar. Negations of unrelated predicates (e.g. `¬ res_0 > res_1`)
don't represent a polarity conflict and are ignored — `refine_exists_eq`
should still pick `res_0` from an unconditional `depth l res_0` conjunct
in such cases. -/
partial def bvarHasNegatedEq (depth : Nat) (e : Expr) : Bool :=
  match_expr e with
  | Not p => isEqOnBVar depth p || bvarHasNegatedEq depth p
  | _ =>
    match e with
    | .forallE _ dom body _ =>
      if body.isConstOf ``False && isEqOnBVar depth dom then
        true
      else
        bvarHasNegatedEq depth dom || bvarHasNegatedEq (depth + 1) body
    | .app f a => bvarHasNegatedEq depth f || bvarHasNegatedEq depth a
    | .lam _ d b _ => bvarHasNegatedEq depth d || bvarHasNegatedEq (depth + 1) b
    | .letE _ t v b _ =>
      bvarHasNegatedEq depth t || bvarHasNegatedEq depth v
        || bvarHasNegatedEq (depth + 1) b
    | .mdata _ e => bvarHasNegatedEq depth e
    | .proj _ _ e => bvarHasNegatedEq depth e
    | _ => false

def refineExistsEqImpl : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  match_expr target with
  | Exists ty p =>
    match p with
    | .lam _ _ body _ =>
      if bvarHasNegatedEq 0 body then
        throwError "refine_exists_eq: existential variable appears under \
          negation as an equality; bivalued constraint, not a pinning equality"
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
