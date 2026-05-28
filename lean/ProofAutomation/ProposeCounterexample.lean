import Lean
import Plausible
import ProofAutomation.Helpers

/-! # ProposeCounterexample — emit a `¬ outer` proof scaffold from a PBT witness

Run at a stuck/sorry site mid-proof:
  `propose_counterexample failed_subtyping_12`

PBT runs on the local goal; on a witness, the tactic emits a paste-ready
`example : ¬ <outer> := by ...` scaffold whose leaves are `sorry`. The user
completes by hand. When the outer's binders aren't all locatable in the
current local context (typical of case-split positions), the tactic throws
rather than emit an unusable scaffold.
-/

open Lean Elab Tactic Meta
open Std (Format)

namespace ProposeCounterexample

/-! ## PBT witness extraction helper

Monomorphic `PBTOutcome` so `evalExpr` doesn't trip on universe-polymorphic
`Option`/`List`. -/

structure PBTOutcome where
  /-- True iff Plausible returned `.failure`. When false, `witnesses` is empty. -/
  found     : Bool
  /-- Witness strings (one per `NamedBinder` in the closed prop) when `found`. -/
  witnesses : List String
  deriving Inhabited

unsafe def extractWitnessIO {p : Prop} (action : IO (Plausible.TestResult p)) :
    IO PBTOutcome := do
  match ← action with
  | .failure _ xs _ => return { found := true, witnesses := xs }
  | _ => return { found := false, witnesses := [] }

/-! ## In-flight outer-theorem lookup

Recovers the enclosing declaration's type when the tactic is invoked inside
the body of the very theorem it's refuting (`env.find?` returns `none` then
because the decl isn't committed yet). -/

/-- Stable mvarId ordering: numeric suffix first, then full name compare as
    tie-break so non-`.num` names and ties produce a deterministic pick. -/
private def mvarRank (id : MVarId) : Nat × Name :=
  let n := match id.name with
    | .num _ k => k
    | _ => 0
  (n, id.name)

private def rankLT (a b : Nat × Name) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && a.2.lt b.2)

/-- Locate the syntheticOpaque Prop mvar that represents the enclosing
    theorem's root goal. Two-phase: rank by `mvarRank`, then check `isProp`
    on the survivor only (the `withLCtx`+`isProp` call is the expensive bit). -/
private def pickRootGoalMVar : TacticM (Option MetavarDecl) := do
  let mctx ← getMCtx
  let mut best? : Option ((Nat × Name) × MetavarDecl) := none
  for (id, decl) in mctx.decls do
    unless decl.kind matches .syntheticOpaque do continue
    let r := mvarRank id
    match best? with
    | none => best? := some (r, decl)
    | some (bestR, _) => if rankLT r bestR then best? := some (r, decl)
  let some (_, decl) := best? | return none
  let isPropVal ← try withLCtx decl.lctx decl.localInstances (Meta.isProp decl.type)
                  catch _ => pure false
  return if isPropVal then some decl else none

/-- Filter out the self-recursion fvar from a decl's lctx. The self fvar
    is the one whose `userName` is either the decl's basename or a suffix
    of the full qualified name. -/
private def filterSelfFVars (declName? : Option Name) (lctx : LocalContext) :
    Array Expr :=
  let isSelf (uname : Name) : Bool := match declName? with
    | none => false
    | some dn =>
      uname == dn ||
      uname.isSuffixOf dn ||
      (match dn, uname with
       | .str _ s, .str _ s' => s == s'
       | _, _ => false)
  lctx.foldl (init := #[]) fun acc d =>
    if isSelf d.userName then acc else acc.push d.toExpr

def findRootOuterType : TacticM (Option Expr) := do
  let some decl ← pickRootGoalMVar | return none
  let declName? ← Term.getDeclName?
  let fvars := filterSelfFVars declName? decl.lctx
  let outerType ← withLCtx decl.lctx decl.localInstances do
    Meta.mkForallFVars fvars decl.type
  return some outerType

/-! ## Outer-type decomposition

An "argument slot" is a value binder (we plug in a witness term) or a
non-dependent premise (we discharge via `(by native_decide)`). Order matters
— slots are emitted in source order. `ForallSlot` / `classifyForall?` live
in `Helpers.lean`, shared with `SearchAxioms.decomposeAxiom`. -/

partial def decomposeOuter (e : Expr) : Array ForallSlot × Expr :=
  let rec loop (e : Expr) (slots : Array ForallSlot) : Array ForallSlot × Expr :=
    match classifyForall? e with
    | some (slot, body) => loop body (slots.push slot)
    | none => (slots, e)
  loop e #[]

/-! ## Witness map from PBT output

Plausible emits each witness as a `"<var> := <value>"` string (via `addVarInfo`).
Split on the *first* `:= ` only, so witness values that themselves contain
`:= ` (lambdas, Pi types, struct literals) round-trip intact. Keyed by `Name`
on the bare binder identifier. -/

abbrev WitnessMap := Lean.NameMap String

private def splitOnceOn (sep : String) (s : String) : Option (String × String) :=
  let parts := s.splitOn sep
  match parts with
  | [] | [_] => none
  | first :: rest => some (first, String.intercalate sep rest)

/-- Collapse a multi-line witness value into one space-joined line: structured
    Plausible outputs (e.g. `Rbtnode\n  true\n  (Rbtleaf)\n  1\n  (Rbtleaf)`)
    would otherwise both render unreadably in the error block AND break the
    `have H1 := H <witness>` scaffold splice. -/
private def collapseValue (s : String) : String :=
  let parts := s.splitOn "\n" |>.map (·.trimAscii.toString) |>.filter (· ≠ "")
  String.intercalate " " parts

def parseWitnesses (xs : List String) : WitnessMap :=
  xs.foldl (init := {}) fun acc s =>
    match splitOnceOn " := " s with
    | some (name, value) =>
      acc.insert (Name.mkSimple name.trimAscii.toString) (collapseValue value)
    | none => acc

/-! ## PBT runner

Reverts all locals on a saved state, runs Plausible, returns the witness
map. State is restored before returning so the caller's context is unchanged.
We revert everything (not a goal-dependency subset) because outer binders
typically appear as locals after `intro`s, and PBT needs them as ∀-binders
to vary; a `False`-conclusion goal with no fvars would otherwise leave the
test running on a vacuous proposition. -/

unsafe def synthTestable (prop' : Expr) : TacticM (Option Expr) := do
  let testableTy ← mkAppM ``Plausible.Testable #[prop']
  -- Each reverted hyp adds a `varTestable` step; nested `→`s add forwarders
  -- through `NamedBinder`. Default 256 is too tight on rbtree-shaped reverted
  -- contexts; 1024 covers depth-tree / rbtree / list and bails ~4× faster than
  -- 4096 when a `Decidable` is missing for some sub-prop.
  try
    withOptions (fun o => o.insert `synthInstance.maxSize (.ofNat 1024)) <|
      synthInstance? testableTy
  catch e => do rethrowIfFatal e; pure none

unsafe def evalCheckIO (prop' inst cfgExpr : Expr) : TacticM (IO PBTOutcome) := do
  let checkExpr ← mkAppOptM ``Plausible.Testable.checkIO
    #[some prop', some inst, some cfgExpr]
  let extractExpr ← mkAppOptM ``extractWitnessIO #[some prop', some checkExpr]
  let resultTyExpr := mkApp (mkConst ``IO) (mkConst ``PBTOutcome)
  evalExpr (IO PBTOutcome) resultTyExpr extractExpr (safety := .unsafe)

unsafe def runPBTUnsafe (seed : Option Nat := none) :
    TacticM (Option WitnessMap) := do
  -- Budget: 1000 instances × max-size 15 ≈ a few seconds when no
  -- counterexample exists. Genuine refutations are usually witnessed in the
  -- first ~100 instances (e.g. `s := 1, v := Leaf` for depth_gen_spec); the
  -- previous 10000 × 30 was paying ~10× for the long-tail tries that almost
  -- never matter. Raise via custom invocation if a specific case needs it.
  let cfg : Plausible.Configuration :=
    { numInst := 1000, maxSize := 15, randomSeed := seed }
  withoutModifyingState do
    let (_, g) ← (← getMainGoal).revert ((← getLocalHyps).map (Expr.fvarId!))
    g.withContext do
      let prop ← instantiateMVars (← g.getType)
      let prop' ← Plausible.Decorations.addDecorations prop
      let some inst ← synthTestable prop'
        | throwError "propose_counterexample: could not synthesize\n  Plausible.Testable {prop'}"
      let action ← evalCheckIO prop' inst (Lean.toExpr cfg)
      let outcome ← action
      if outcome.found then
        return some (parseWitnesses outcome.witnesses)
      else
        return none

@[implemented_by runPBTUnsafe]
opaque runPBT (seed : Option Nat := none) :
    TacticM (Option WitnessMap)

/-! ## σ builder (local-context based)

For each outer binder, look for a local with the same `userName`
(macro-scope-insensitive) whose type is defEq. Resolve the witness term:
the PBT witness when present, else the local FVar name. -/

structure SigmaEntry where
  name    : Name
  type    : Expr
  /-- Witness term to splice into the specialize line. -/
  witness : String
  deriving Inhabited

/-- Find a local decl by userName ignoring macro scopes on both sides. -/
private def findLocalByName (lctx : LocalContext) (n : Name) : Option LocalDecl :=
  let nClean := n.eraseMacroScopes
  lctx.decls.foldl (init := none) fun acc d? => match acc, d? with
    | some _, _ => acc
    | none, some d => if d.userName.eraseMacroScopes == nClean then some d else none
    | _, _ => acc

/-! ### Case-split witness recovery

When a binder is missing from the current lctx, it has typically been
consumed by a `cases` split. The case tag on the current goal (set by the
`with | CtorName => ...` clause) names the constructor; for 0-arity
constructors we can reconstruct the witness directly. For positive-arity
constructors we scan the current lctx for a contiguous run of fvars whose
types match the constructor's argument signature — this catches the common
pattern where the user just wrote `cases v with | Ctor a b c => ...` and
no other tactic added intervening fvars before `propose_counterexample`. -/

/-- The simple (last) component of `n`, e.g. `Foo.Bar.Baz → "Baz"`. -/
private def lastComponentStr (n : Name) : String :=
  match n.eraseMacroScopes with
  | .str _ s => s
  | other => other.toString

/-- Render a witness term as a parenthesized splice-ready string. -/
private def renderCtorWitness (ctorName : Name) (fieldNames : Array String) :
    String :=
  if fieldNames.isEmpty then toString ctorName
  else s!"({ctorName} {String.intercalate " " fieldNames.toList})"

/-- Walk the constructor's type, peeling `numParams` parameters using
    `binderType`'s head arguments, then check the next `numFields` ∀-arg
    types defEq the supplied `fields`. Returns `true` iff the field
    signature lines up. -/
private def fieldsMatchCtor (ctorName : Name) (indInfo : InductiveVal)
    (binderType : Expr) (fields : Array LocalDecl) : TacticM Bool := do
  let mut ctorTy ← inferType (mkConst ctorName (indInfo.levelParams.map mkLevelParam))
  let typeArgs := binderType.getAppArgs
  if typeArgs.size < indInfo.numParams then return false
  for i in [:indInfo.numParams] do
    ctorTy ← instantiateForall ctorTy #[typeArgs[i]!]
  for d in fields do
    ctorTy ← whnf ctorTy
    let .forallE _ expected _ _ := ctorTy | return false
    unless (← isDefEq expected d.type) do return false
    ctorTy ← instantiateForall ctorTy #[d.toExpr]
  return true

/-- Scan `lctx` for any contiguous window of `numFields` fvars whose types
    line up with `ctorName`'s signature. Returns the matching userNames in
    order, or `none` if no window matches. -/
private def findCtorFieldWindow (ctorName : Name) (indInfo : InductiveVal)
    (binderType : Expr) (numFields : Nat) (lctx : LocalContext) :
    TacticM (Option (Array String)) := do
  let decls : Array LocalDecl :=
    lctx.decls.foldl (init := #[]) fun acc d? =>
      match d? with | some d => acc.push d | none => acc
  if decls.size < numFields then return none
  for start in [:decls.size - numFields + 1] do
    let window := decls.extract start (start + numFields)
    if (← fieldsMatchCtor ctorName indInfo binderType window) then
      return some (window.map (·.userName.toString))
  return none

/-- Attempt to reconstruct a witness for an outer binder that's been case-
    split out of the local context. Returns `none` when recovery isn't
    possible (binder type isn't an inductive, current goal tag doesn't
    match a constructor, or — for positive-arity constructors — no run of
    fvars in the lctx matches the constructor's signature).

    Scans every component of the case tag (not just the last): subsequent
    `refine`/`rotate_left` calls after `cases` append `.left`/`.right`
    that bury the ctor name mid-tag.

    Field-window fvars are substituted with their PBT witness values when
    available — emitted scaffolds reference local fvars otherwise, which
    don't exist in the standalone `¬ outer` proof the user pastes out. -/
def recoverCaseSplitWitness (binderName : Name) (binderType : Expr)
    (witnesses : WitnessMap) : TacticM (Option String) := do
  let _ := binderName  -- name kept for future scoping/diagnostics
  let env ← getEnv
  let some indName := binderType.getAppFn.constName? | return none
  let some (.inductInfo indInfo) := env.find? indName | return none
  let tag ← (← getMainGoal).getTag
  let tagParts : List String := tag.eraseMacroScopes.components.map lastComponentStr
  let some ctorName := indInfo.ctors.find? (fun c => tagParts.contains (lastComponentStr c))
    | return none
  let some (.ctorInfo ctorInfo) := env.find? ctorName | return none
  if ctorInfo.numFields == 0 then
    return some (toString ctorName)
  let some fieldNames ← findCtorFieldWindow ctorName indInfo binderType
                          ctorInfo.numFields (← getLCtx)
    | return none
  let resolved := fieldNames.map fun n =>
    (witnesses.find? (Name.mkSimple n)).getD n
  return some (renderCtorWitness ctorName resolved)

/-- Build σ entries for binder slots only (premises are discharged with
    `(by native_decide)` at scaffold-render time). Falls back to
    `recoverCaseSplitWitness` for binders that have been consumed by a
    `cases` split. Throws if a binder is missing and recovery can't
    reconstruct it; the error lists the unresolved binders alongside the
    PBT witnesses we did find so the user can hand-construct the
    refutation. -/
def buildSigma (slots : Array ForallSlot) (witnesses : WitnessMap)
    (outerName : Name) : TacticM (Array SigmaEntry) := do
  let lctx ← getLCtx
  let mut entries : Array SigmaEntry := #[]
  let mut missing : Array Name := #[]
  for slot in slots do
    match slot with
    | .premise _ => continue
    | .binder n ty => do
      match findLocalByName lctx n with
      | some decl => do
        if (← isDefEq decl.type ty) then
          let key := Name.mkSimple n.eraseMacroScopes.toString
          let w := (witnesses.find? key).getD decl.userName.toString
          entries := entries.push { name := n, type := ty, witness := w }
        else
          match ← recoverCaseSplitWitness n ty witnesses with
          | some w => entries := entries.push { name := n, type := ty, witness := w }
          | none => missing := missing.push n
      | none =>
        match ← recoverCaseSplitWitness n ty witnesses with
        | some w => entries := entries.push { name := n, type := ty, witness := w }
        | none => missing := missing.push n
  unless missing.isEmpty do
    let missingList := String.intercalate ", " (missing.toList.map (·.toString))
    let witnessLines := witnesses.toList.map fun (k, v) => s!"    {k} := {v}"
    let witnessBlock :=
      if witnessLines.isEmpty then "  (PBT produced no witness lines)"
      else "  PBT witnesses available:\n" ++ String.intercalate "\n" witnessLines
    throwError "propose_counterexample: outer binders not present in local \
      context (likely case-split during proof): {missingList}\n\
      The outer is `{outerName}`. Either `intro`/rename to expose these binders \
      locally, or hand-construct the refutation using the witnesses below.\n\
      {witnessBlock}"
  return entries

/-! ## Conclusion-body pretty-printer

`simp_hyps` destructures `∃`/`∧`/`Iff` itself, so the scaffold only needs
explicit destructuring for `∨` positions (which `simp_hyps` leaves intact). -/

private def existsArgs? (e : Expr) : Option (Name × Expr) :=
  match_expr e with
  | Exists _ body => match body with
    | .lam n _ b _ => some (n, b)
    | _ => none
  | _ => none

private def andArgs? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | And a b => some (a, b)
  | _ => none

private def orArgs? (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | Or a b => some (a, b)
  | _ => none

/-- `e` reaches an `∨` through nested `∃`/`∧`. Renamed from `hasOr` for
    clarity: this gates whether the renderer must emit an `rcases` ladder. -/
partial def needsOrCascade : Expr → Bool := fun e =>
  if (orArgs? e).isSome then true
  else if let some (l, r) := andArgs? e then needsOrCascade l || needsOrCascade r
  else if let some (_, body) := existsArgs? e then needsOrCascade body
  else false

private def mkFreshName (prefix_ : String) : StateM Nat String := do
  let i ← get; modify (· + 1); pure s!"{prefix_}_{i}"

/-- Build a nested `obtain` pattern peeling `∃`/`∧` down to leaves and `∨`
    positions. Returns the pattern string plus in-order `(orHypName, orExpr)`
    pairs for downstream `rcases` processing. -/
partial def buildPattern (e : Expr) :
    StateM Nat (String × Array (String × Expr)) := do
  if let some (n, body) := existsArgs? e then
    let v ← mkFreshName n.eraseMacroScopes.toString
    let (bp, bo) ← buildPattern body
    return (s!"⟨{v}, {bp}⟩", bo)
  if let some (l, r) := andArgs? e then
    let (lp, lo) ← buildPattern l
    let (rp, ro) ← buildPattern r
    return (s!"⟨{lp}, {rp}⟩", lo ++ ro)
  if (orArgs? e).isSome then
    let h ← mkFreshName "hOr"
    return (h, #[(h, e)])
  let h ← mkFreshName "h"
  return (h, #[])

/-- The leaf closer for branches that don't contain `∨` reachable through
    `∃`/`∧` — `simp_hyps` handles destructuring; failure falls through to
    `sorry` for the user to complete. -/
private def closerLine : Format := .text "first | (simp_hyps; done) | sorry"

mutual

partial def fmtOrCascade (ors : List (String × Expr)) : StateM Nat Format := do
  match ors with
  | [] => return closerLine
  | (hName, e) :: rest =>
    let some (l, r) := orArgs? e | fmtOrCascade rest
    let lh ← mkFreshName "h"
    let rh ← mkFreshName "h"
    let lBranch ← fmtFromHyp l lh rest
    let rBranch ← fmtFromHyp r rh rest
    return .text s!"rcases {hName} with {lh} | {rh}" ++ .line ++
           .text "·" ++ .nest 2 (.line ++ lBranch) ++ .line ++
           .text "·" ++ .nest 2 (.line ++ rBranch)

partial def fmtFromHyp (e : Expr) (hypName : String)
    (rest : List (String × Expr)) : StateM Nat Format := do
  if !needsOrCascade e then
    fmtOrCascade rest
  else if (orArgs? e).isSome then
    fmtOrCascade ((hypName, e) :: rest)
  else
    let (pat, branchOrs) ← buildPattern e
    let cascade ← fmtOrCascade (branchOrs.toList ++ rest)
    return .text s!"obtain {pat} := {hypName}" ++ .line ++ cascade

end

/-! ## Scaffold assembly -/

private def hypName : String := "H1"

/-- Pretty-print an expression with bumped pp depth so deeply-nested
    Cobb premise/outer types come back without `⋯` truncation. -/
private def ppDeep (e : Expr) : MetaM String :=
  withOptions (fun o =>
      o.insert `pp.maxDepth (.ofNat 200)
       |>.insert `pp.deepTerms (.ofBool true)
       |>.insert `pp.deepTerms.threshold (.ofNat 200)) do
    pure (toString (← Meta.ppExpr e))

/-- Walk the outer's forall-telescope in source order, emitting a `let`
    binding for each binder slot (named after the binder, value is the PBT
    witness) and a `have hp_i : <premise> := by …` line for each premise
    slot. Premise types are pretty-printed *after* the binder fvars are in
    scope, so they read `0 ≤ s` rather than `0 ≤ #0`. Each premise is its
    own goal, so the user can attack hard ones (e.g. Cobb-shaped `∃` chains
    pinned by equality conjuncts) with `simp_goal` / `refine_exists_eq` /
    hand-construction without touching the rest of the scaffold. -/
def renderScaffold (outerName : String) (outerType : Expr) (slots : Array ForallSlot)
    (sigma : Array SigmaEntry) (concl : Expr) : MetaM Format := do
  let outerTypeStr ← ppDeep outerType
  Meta.forallTelescope outerType fun args _body => do
    let mut lines : Array String := #[]
    let mut applyArgs : Array String := #[]
    let mut sigmaIdx := 0
    let mut hpIdx := 0
    for h : i in [:slots.size] do
      let slot := slots[i]!
      let arg := args[i]!
      match slot with
      | .binder _ _ => do
        let entry := sigma[sigmaIdx]!
        let nm := entry.name.toString
        let typeStr ← ppDeep entry.type
        lines := lines.push s!"let {nm} : {typeStr} := {entry.witness}"
        applyArgs := applyArgs.push nm
        sigmaIdx := sigmaIdx + 1
      | .premise _ => do
        let ty ← Meta.inferType arg
        let tyStr ← ppDeep ty
        let hpName := s!"hp{hpIdx}"
        lines := lines.push
          s!"have {hpName} : {tyStr} := by first | native_decide | simp_goal | sorry"
        applyArgs := applyArgs.push hpName
        hpIdx := hpIdx + 1
    let body : Format := Id.run (fmtFromHyp concl hypName [] |>.run' 0)
    let setupBlock : Format :=
      lines.foldl (fun acc l => acc ++ .line ++ .text l) (.text "")
    return (
      .text s!"-- spec-bug refutation candidate for `{outerName}`" ++ .line ++
      .text s!"example : ¬ ({outerTypeStr}) := by" ++
      .nest 2 (
        .line ++ .text "intro H" ++
        setupBlock ++
        .line ++ .text s!"have {hypName} := H {String.intercalate \" \" applyArgs.toList}" ++
        .line ++ body))

/-! ## Tactic frontend -/

def proposeCounterexampleImpl (outer? : Option Name)
    (seed : Option Nat := none) :
    TacticM Unit :=
  withMainContext do
    let (outerName, outerType) ← match outer? with
      | some n =>
        let env ← getEnv
        let some ci := env.find? n
          | throwError "propose_counterexample: '{n}' not in environment"
        pure (n, ← instantiateMVars ci.type)
      | none =>
        let some n ← Term.getDeclName?
          | throwError "propose_counterexample: no outer ident provided and no enclosing declaration; pass the name explicitly"
        let some ty ← findRootOuterType
          | throwError "propose_counterexample: could not infer the enclosing theorem's type; pass the name explicitly"
        pure (n, ← instantiateMVars ty)
    let (slots, conclusion) := decomposeOuter outerType
    let some witnesses ← runPBT seed
      | throwError "propose_counterexample: PBT did not find a counterexample within budget"
    let sigma ← buildSigma slots witnesses outerName
    let scaffold ← renderScaffold outerName.toString outerType slots sigma conclusion
    logInfo m!"propose_counterexample produced scaffold:\n\n{scaffold.pretty}"

end ProposeCounterexample
