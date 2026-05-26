import Lean
import ProofAutomation.Helpers
import ProofAutomation.Z3Tactic

/-! # Z3Local — tactic-mode SMT dispatch. Folds lctx + main target into a
closed conjecture, dispatches to Z3, closes via `z3SmtTrusted` on `unsat`.
See `lean/CLAUDE.md` for the surrounding tactic catalog. -/

open Lean Elab Tactic Meta

namespace Z3Local

/-- Fold the local context into `goal` as `∀ data, hyp₁ → ... → goal`.
    Returns `(closed, dataFVars, hypFVars)` so the caller can rebuild
    `(z3SmtTrusted closed) dataFVars… hypFVars… : goal` and let the kernel
    verify the `closed → goal` link. -/
def lctxToClosedExpr (goal : Expr) :
    TacticM (Expr × Array FVarId × Array FVarId) := do
  let lctx ← getLCtx
  let hypFVars ← lctx.foldlM (init := (#[] : Array FVarId)) fun acc decl => do
    if decl.isAuxDecl || decl.isImplementationDetail then return acc
    if decl.binderInfo == .instImplicit then return acc
    if decl.isLet then
      throwError m!"z3_local: let-binding '{decl.userName}' not supported. \
        Use `clear {decl.userName}` first, or inline the let manually."
    if (← Meta.isProp decl.type) then return acc.push decl.fvarId
    return acc
  -- Dependent abstraction over hypotheses: a hyp fvar referenced inside
  -- a later hyp's type is bound in place, not left free for collectFVars
  -- to scoop up into the data residue.
  let hypsClosed ← mkForallFVars (hypFVars.map mkFVar) goal
  let dataFVarSet := (Lean.collectFVars {} hypsClosed).fvarSet
  let dataFVars ← lctx.foldlM (init := (#[] : Array FVarId)) fun acc decl => do
    if !dataFVarSet.contains decl.fvarId then return acc
    if decl.binderInfo == .instImplicit then return acc
    return acc.push decl.fvarId
  let closed ← mkForallFVars (dataFVars.map mkFVar) hypsClosed
  -- hasFVar fires when a hypothesis references an instImplicit fvar we
  -- deliberately don't abstract over; hasMVar when the main target still
  -- has unassigned `?_` placeholders.
  if closed.hasFVar then
    throwError m!"z3_local: internal error — closed conjecture still has free variables: {closed}"
  if closed.hasMVar then
    throwError m!"z3_local: internal error — closed conjecture still has metavariables: {closed}"
  return (closed, dataFVars, hypFVars)

def z3LocalImpl (verbose : Bool) (axiomFilter : Option (Array Name)) : TacticM Unit :=
  withMainContext do
    let mainGoal ← getMainGoal
    let goal ← instantiateMVars (← getMainTarget)
    let (closed, dataFVars, hypFVars) ← lctxToClosedExpr goal
    let kept ← if axiomFilter.any (·.isEmpty) then pure #[] else
      Z3Check.gatherUserAxioms "z3_local" (excludeName := none) (filter? := axiomFilter)
    let output ← Z3Check.dispatchZ3 "z3_local" kept closed verbose
    match output.result with
    | .unsat =>
      let closedProof :=
        mkApp (mkConst ``ProofAutomation.Trusted.z3SmtTrusted) closed
      let proofTerm := mkAppN closedProof ((dataFVars ++ hypFVars).map mkFVar)
      let proofType ← inferType proofTerm
      unless ← isDefEq proofType goal do
        throwError m!"z3_local: internal — proof term type does not match goal.\n\
          proof type: {proofType}\n\
          goal:       {goal}"
      mainGoal.assign proofTerm
    | _ =>
      dispatchExceptMsg
        (Z3Check.z3ResultMessage "z3_local" none verbose false output none)

end Z3Local

syntax "z3_local"  ("only" "[" ident,* "]")? : tactic
syntax "z3_local?" ("only" "[" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| z3_local  $[only [$as,*]]?) =>
      Z3Local.z3LocalImpl false (as.map fun ids => ids.getElems.map (·.getId))
  | `(tactic| z3_local? $[only [$as,*]]?) =>
      Z3Local.z3LocalImpl true  (as.map fun ids => ids.getElems.map (·.getId))
