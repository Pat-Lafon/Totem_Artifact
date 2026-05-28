/-
  PBT.lean — Type-agnostic Plausible setup for counterexample search.

  Re-exports `Plausible` and ships the universal low-priority Shrinkable
  fallback so custom datatypes don't need per-type opt-in. Plausible's
  specific shrinkers (`Int`, `Bool`, …) keep their default priority and
  still win where declared.

  For the common case of `def f (... : <user-inductive>) ... : Prop := <impl> = res`
  wrappers, the `auto_pbt_decidable` command below sweeps the current
  module and registers `Decidable` instances. Hand-written instances
  (e.g. when a recursive predicate needs a custom decision procedure)
  still live in the test file.
-/
import Plausible

instance (priority := low) {α : Type _} : Plausible.Shrinkable α := {}

/- Forward `Decidable` / `PrintableProp` through `Plausible.NamedBinder`.

`Plausible.NamedBinder n p` is semantically `p`, but the wrapper is a `def`
(not `abbrev`), so instance resolution does not unfold it. Without these
two forwarders, `decGuardTestable`'s `[Decidable p]` premise cannot be
discharged when `p` itself is a propositional implication, even though
`Decidable.implies` exists for `Decidable P → Decidable Q → Decidable (P → Q)`.
Diagnostic walk: see `TODO_Counterexamples.md` "T2" entry. -/

instance (n : String) (p : Prop) [d : Decidable p] :
    Decidable (Plausible.NamedBinder n p) := d

instance (n : String) (p : Prop) [pr : Plausible.PrintableProp p] :
    Plausible.PrintableProp (Plausible.NamedBinder n p) := pr

/-! ## auto_pbt_decidable

Sweep the current module for `def f ... : Prop := ...` whose argument
signature mentions a module-local inductive, and register
`Decidable (f args)` instances when synthesis succeeds on the unfolded
body.

Call once near the bottom of a scenario file (after the Prop-returning
wrappers, before the first PBT use). The inductive itself still needs
`deriving Plausible.Arbitrary, Repr` at its declaration site — both are
real `deriving` handlers and live there, not here. -/

namespace ProofAutomation.AutoPBT

open Lean Meta Elab Command

/-- Defined in this file iff `getModuleIdxFor?` returns none (the imported-
    constant index doesn't include current-module decls). -/
private def isCurrentModule (env : Environment) (n : Name) : Bool :=
  (env.getModuleIdxFor? n).isNone && !n.isInternal

private def collectUserInds (env : Environment) : NameSet :=
  env.constants.fold (init := {}) fun acc n ci => match ci with
    | .inductInfo _ => if isCurrentModule env n then acc.insert n else acc
    | _ => acc

private def collectCandidates (userInds : NameSet) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, ci) in env.constants do
    unless isCurrentModule env n do continue
    let .defnInfo di := ci | continue
    let isCand ← try Meta.forallTelescope di.type fun args body => do
      unless body.isProp do return false
      for a in args do
        if let some c := (← Meta.inferType a).getAppFn.constName? then
          if userInds.contains c then return true
      return false
    catch _ => pure false
    if isCand then out := out.push n
  return out

/-- Returns `some instName` when a fresh Decidable instance was registered,
    `none` otherwise. Throws nothing — caller can summarize. -/
private def tryRegister (c : Name) : TermElabM (Option Name) := do
  let env ← getEnv
  let instName := c.str "autoDecidable"
  if env.find? instName |>.isSome then return none
  let some ci := env.find? c | return none
  Meta.forallTelescopeReducing ci.type fun args body => do
    unless body.isProp do return none
    let lvls := ci.levelParams.map mkLevelParam
    let appExpr := mkAppN (Expr.const c lvls) args
    let some unfolded ← Meta.unfoldDefinition? appExpr | return none
    let some inst ← Meta.synthInstance? (mkApp (mkConst ``Decidable) unfolded)
      | return none
    let finalDecType := mkApp (mkConst ``Decidable) appExpr
    let instType ← Meta.mkForallFVars args finalDecType
    let instValue ← Meta.mkLambdaFVars args inst
    try
      addAndCompile (logCompileErrors := false) <| .defnDecl {
        name := instName
        levelParams := ci.levelParams
        type := instType
        value := instValue
        hints := .regular 0
        safety := .safe
      }
      Meta.addInstance instName .global (eval_prio default)
      return some instName
    catch _ => return none

elab "auto_pbt_decidable" : command => do
  let userInds := collectUserInds (← getEnv)
  if userInds.isEmpty then
    logWarning "auto_pbt_decidable: no module-local inductives found"
    return
  let candidates ← liftTermElabM <| collectCandidates userInds
  let mut registered : Array Name := #[]
  let mut skipped : Array Name := #[]
  for c in candidates do
    match ← liftTermElabM (tryRegister c) with
    | some _ => registered := registered.push c
    | none => skipped := skipped.push c
  let summary :=
    s!"auto_pbt_decidable: registered {registered.size}/{candidates.size}"
  if skipped.isEmpty then
    logInfo m!"{summary} ({registered.toList})"
  else
    logInfo m!"{summary} (registered: {registered.toList}; skipped: {skipped.toList})"

end ProofAutomation.AutoPBT
