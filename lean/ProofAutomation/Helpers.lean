import Lean

open Lean Elab Tactic Meta

/-! ## Trust axiom for SMT-dispatching tactics

`ProofAutomation.Trusted.z3SmtTrusted` is the load-bearing trust axiom for
tactics that close goals based on Z3's `unsat` verdict (currently
`z3_local`). Any proof closed via this axiom places Z3 in the trusted
computing base of that proof; `#print axioms <thm>` will surface the
dependency. -/

namespace ProofAutomation.Trusted
axiom z3SmtTrusted {p : Prop} : p
end ProofAutomation.Trusted

/-! ## Result dispatch -/

/-- Dispatch an `Except`-encoded pure-message result: `.ok` ⇒ `logInfo`,
    `.error` ⇒ `throwError`. Shared by command-mode (`z3`) and tactic-mode
    (`z3_local`) Z3 result reporting — both route through
    `Z3Check.z3ResultMessage` which produces this exact shape. -/
def dispatchExceptMsg {m : Type → Type}
    [Monad m] [MonadLog m] [Lean.AddMessageContext m] [Lean.MonadOptions m]
    [MonadError m]
    (e : Except MessageData MessageData) : m Unit :=
  match e with
  | .ok msg    => Lean.logInfo msg
  | .error msg => throwError msg

/-! ## Tactic-step helpers -/

/-- `true` on success, `false` on ordinary "tactic failed". Interrupts,
max-heartbeat, and max-recDepth always rethrow. -/
def tryTacticStep (act : TacticM Unit) : TacticM Bool := do
  try act; pure true
  catch e =>
    if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
    pure false

/-- Rethrow interrupt / max-heartbeat / max-recDepth; swallow ordinary
tactic-failure errors. Use in catch blocks where `tryTacticStep` doesn't fit. -/
def rethrowIfFatal {m : Type → Type} [Monad m] [MonadExcept Exception m]
    (e : Exception) : m Unit := do
  if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e

/-! ## Syntax helpers -/

partial def eraseMacroScopesFromSyntax : Syntax → Syntax
  | .ident info rawVal name preresolved =>
    .ident info rawVal name.eraseMacroScopes preresolved
  | .node info kind args =>
    .node info kind (args.map eraseMacroScopesFromSyntax)
  | other => other

def freshAccessibleName (base : Name) (avoid : Array Name := #[]) : TacticM Name := do
  let lctx ← getLCtx
  if (lctx.findFromUserName? base).isNone && !avoid.contains base then return base
  let start := lctx.decls.size
  -- Pigeonhole: among (lctx.size + avoid.size + 1) consecutive candidates,
  -- at least one is neither in lctx nor in avoid.
  let bound := lctx.decls.size + avoid.size + 1
  for i in [start : start + bound] do
    let candidate := Name.mkSimple s!"{base.eraseMacroScopes}_{i}"
    if (lctx.findFromUserName? candidate).isNone && !avoid.contains candidate then
      return candidate
  throwError "freshAccessibleName: failed to find unique suffix for '{base}' \
    after {bound} attempts (lctx size {lctx.decls.size}, avoid size {avoid.size}); \
    local-context invariant is broken."

/-! ## ∀-chain classification

  Shared by `ProposeCounterexample.decomposeOuter` and
  `SearchAxioms.decomposeAxiom` so both agree on what counts as a
  dependent binder vs. a non-dependent premise. -/

inductive ForallSlot where
  | binder  (name : Name) (type : Expr)
  | premise (type : Expr)
  deriving Inhabited

/-- Classify a `forallE` head. Returns `(slot, body)` where `body` is the
    original `forallE` body — for binder slots it still carries loose bvar 0,
    so MetaM callers that want a closed body must instantiate it themselves
    (typically with a fresh mvar). `none` when `e` is not a `forallE`. -/
@[inline] def classifyForall? : Expr → Option (ForallSlot × Expr)
  | .forallE n ty body _ =>
    if body.hasLooseBVar 0 then
      some (.binder n.eraseMacroScopes ty, body)
    else
      some (.premise ty, body)
  | _ => none

/-! ## Environment introspection -/

def isUserInductive (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.inductInfo _) => (env.getModuleIdxFor? name).isNone
  | _ => false

-- Check if any ancestor in the name's parent chain is a specific kind of constant
private def hasAncestorOfKind (env : Environment) (n : Name)
    (pred : ConstantInfo → Bool) : Bool :=
  let rec checkParent : Name → Bool
    | .str parent _ =>
      match env.find? parent with
      | some ci => pred ci || checkParent parent
      | none => checkParent parent
    | _ => false
  checkParent n

private def isGeneratedFromInductive (env : Environment) (n : Name) : Bool :=
  hasAncestorOfKind env n fun
    | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
    | _ => false

private def isGeneratedFromDef (env : Environment) (n : Name) : Bool :=
  hasAncestorOfKind env n fun
    | .defnInfo _ => true
    | _ => false

-- Check if a name has any internal component: .num indices or _-prefixed strings
private def hasInternalComponent : Name → Bool
  | .num _ _ => true
  | .str parent s => s.startsWith "_" || hasInternalComponent parent
  | .anonymous => false

/-- "Lives in the current file, isn't compiler-synthesized machinery from
    an inductive/def, has no `.num`/`_`-prefixed internal components." Shared
    base for the `theorem`-side and `def`-side composites below. -/
private def isUserOriginInModule (env : Environment) (n : Name) : Bool :=
  (env.getModuleIdxFor? n).isNone &&
  !isGeneratedFromInductive env n &&
  !isGeneratedFromDef env n &&
  !hasInternalComponent n

def isUserDef (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo _) => isUserOriginInModule env n
  | _ => false

/-- Recognize Cobb-Totem-generated axiom theorems. A name counts if any
    component of its prefix chain is the literal `Axioms`. Cobb's preamble
    wraps emitted axioms in `namespace Axioms`, and `propose_axiom`
    registers under the same namespace. Nested namespaces are allowed:
    `Tests.Z3Command.Axioms.ax_zero` matches just as `Axioms.ax_0` does. -/
def isAxiomName : Name → Bool
  | .str p s => s == "Axioms" || isAxiomName p
  | .num p _ => isAxiomName p
  | .anonymous => false

/-- Composite predicate for "current-file user-authored axiom theorem".
    Canonical filter for axiom-pool collection across `Z3Tactic` and
    `SearchAxioms` — both must agree on what counts as a pool axiom. -/
def isUserTheorem (env : Environment) (n : Name) : Bool :=
  isUserOriginInModule env n && isAxiomName n

/-- Apply an optional axiom-name filter to a gathered axiom pool, resolving
    each requested name through `resolveGlobalConstNoOverloadCore`. -/
def applyAxiomFilter {m : Type → Type}
    [Monad m] [MonadResolveName m] [MonadEnv m] [MonadOptions m] [MonadLog m]
    [AddMessageContext m] [MonadError m]
    (cmdName : String) (kept : Array (Name × Expr)) (filter? : Option (Array Name)) :
    m (Array (Name × Expr)) := do
  match filter? with
  | none => return kept
  | some names =>
    let keptMap : Std.HashMap Name Expr :=
      kept.foldl (init := {}) fun acc (n, e) => acc.insert n e
    -- Sort for stable `#guard_msgs` across env-hash shifts.
    let available := (kept.map (·.1)).qsort Name.lt
    let mut result : Array (Name × Expr) := #[]
    let mut seen : Std.HashSet Name := {}
    for n in names do
      let resN ← try
        resolveGlobalConstNoOverloadCore n
      catch e =>
        throwError m!"{cmdName}: failed to resolve axiom name '{n}': {e.toMessageData}\n\
          Available axioms: {available}"
      match keptMap[resN]? with
      | none =>
        throwError m!"{cmdName}: name '{n}' resolves to '{resN}' but isn't in \
          the current-file Axioms namespace.\n\
          Available axioms: {available}"
      | some e =>
        if seen.contains resN then
          throwError m!"{cmdName}: axiom '{resN}' listed more than once in `only [...]` \
            (would emit a duplicate `:named` assertion and crash Z3). Remove the duplicate."
        seen := seen.insert resN
        result := result.push (resN, e)
    return result

/-! ## Tactic combinators -/

private def ensureNoGoals : TacticM Unit := do
  let gs ← getGoals
  if !gs.isEmpty then throwError "has {gs.length} remaining goals"

/-- Try a tactic action and check no goals remain. Restores state on failure. -/
def withBacktrack (action : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try action; ensureNoGoals; return true
  catch e => rethrowIfFatal e; restoreState s; return false

/-! ## destructCore: recursively split ∧ and ∃ in hypotheses -/

partial def destructCore (hypName : Name) : TacticM Unit :=
  withMainContext do
    let some decl := (← getLCtx).findFromUserName? hypName | return ()
    let hypType ← instantiateMVars decl.type
    let hi := mkIdent hypName
    match_expr hypType with
    | And _ _ => do
      let ln ← freshAccessibleName `h
      let rn ← freshAccessibleName `h (avoid := #[ln])
      let stx ← `(tactic| obtain ⟨$(mkIdent ln), $(mkIdent rn)⟩ := $hi)
      evalTactic (eraseMacroScopesFromSyntax stx)
      withMainContext do destructCore ln; destructCore rn
    | Exists _ body => do
      let baseName := match body with | .lam n .. => n.eraseMacroScopes | _ => `w
      let wn ← freshAccessibleName baseName
      let pn ← freshAccessibleName `h (avoid := #[wn])
      let stx ← `(tactic| obtain ⟨$(mkIdent wn), $(mkIdent pn)⟩ := $hi)
      evalTactic (eraseMacroScopesFromSyntax stx)
      withMainContext do destructCore pn
    | Iff _ _ => do
      let fn ← freshAccessibleName `h
      let bn ← freshAccessibleName `h (avoid := #[fn])
      let stx ← `(tactic|
        have $(mkIdent fn) := Iff.mp $hi;
        have $(mkIdent bn) := Iff.mpr $hi;
        clear $hi)
      evalTactic (eraseMacroScopesFromSyntax stx)
    | _ => pure ()

/-! ## Shared proof helpers -/

-- Scan a forall chain, producing intro idents and inductive-variable idents.
def scanForallIntros (env : Environment) (e : Expr) (pfx : String := "_pa") :
    Array (TSyntax `ident) × Array (TSyntax `ident) := Id.run do
  let mut intros : Array (TSyntax `ident) := #[]
  let mut inductives : Array (TSyntax `ident) := #[]
  let mut cur := e
  while true do
    match cur with
    | .forallE _ ty body _ =>
      let id := mkIdent (Name.mkSimple s!"{pfx}{intros.size}")
      intros := intros.push id
      if let .const tyName _ := ty.getAppFn then
        if isUserInductive env tyName then
          inductives := inductives.push id
      cur := body
    | _ => break
  return (intros, inductives)

-- Flatten a goal: intro named binders. If refineExists, also refine ⟨_, ?_⟩ for ∃.
partial def flattenGoal (refineExists := true) : TacticM Unit := do
  let mut counter := 0
  repeat
    let target ← withMainContext (instantiateMVars (← getMainTarget))
    match target with
    | .forallE .. =>
      let name := mkIdent (Name.mkSimple s!"_pax{counter}")
      counter := counter + 1
      evalTactic (eraseMacroScopesFromSyntax (← `(tactic| intro $name:ident)))
    | _ =>
      if refineExists then
        match_expr target with
        | Exists _ _ => evalTactic (← `(tactic| refine ⟨_, ?_⟩))
        | _ => break
      else break
  withMainContext do
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let shouldDestruct := match_expr ty with
        | And _ _ => true | Exists _ _ => true | Iff _ _ => true | _ => false
      if shouldDestruct then destructCore d.userName

-- Collect all constant names referenced in an expression
private def exprConsts (e : Expr) : Array Name :=
  e.foldConsts (init := #[]) fun n acc => acc.push n

-- Transitive closure: starting from seed names, expand via `expand` until fixpoint.
-- `accept` filters which names enter the result set and get expanded.
private partial def transitiveClosure (accept : Name → Bool) (expand : Name → Array Name)
    (seeds : Array Name) : Lean.NameHashSet := Id.run do
  let mut result : Lean.NameHashSet := {}
  let mut worklist : Array Name := #[]
  for n in seeds do
    if accept n && !result.contains n then
      result := result.insert n
      worklist := worklist.push n
  while !worklist.isEmpty do
    let n := worklist.back!
    worklist := worklist.pop
    for m in expand n do
      if accept m && !result.contains m then
        result := result.insert m
        worklist := worklist.push m
  return result

-- Collect user-defined constants transitively through definition bodies
def collectUserDefs (env : Environment) (e : Expr) : Lean.NameHashSet :=
  transitiveClosure (isUserDef env) (fun n =>
    match env.find? n with
    | some (.defnInfo di) => exprConsts di.value
    | _ => #[])
  (exprConsts e)

/-! ## BEq-shape recognizer -/

/-- Recognize `(a == b) = bool_lit` or `bool_lit = (a == b)`, returning the
    polarity (the boolean compared against) and the two `==` operands. -/
def isBEqEq (e : Expr) : Option (Bool × Expr × Expr) :=
  let boolLit? (x : Expr) : Option Bool :=
    if x.isConstOf ``Bool.true then some true
    else if x.isConstOf ``Bool.false then some false
    else none
  let beqArgs? (x : Expr) : Option (Expr × Expr) :=
    match_expr x with
    | BEq.beq _ _ a b => some (a, b)
    | _ => none
  match_expr e with
  | Eq _ lhs rhs =>
    match beqArgs? lhs, boolLit? rhs with
    | some (a, b), some pol => some (pol, a, b)
    | _, _ =>
      match boolLit? lhs, beqArgs? rhs with
      | some pol, some (a, b) => some (pol, a, b)
      | _, _ => none
  | _ => none

/-! ## Truth-value reduction -/

/-- Evaluate `e` via its `Decidable` instance. Catches ground arithmetic
    like `0 ≥ 0` that `Meta.reduce` won't reduce. -/
private def tryDecide (e : Expr) : MetaM (Option Bool) := do
  let saved ← saveState
  try
    if !(← isProp e) then restoreState saved; return none
    let decTy ← mkAppM ``Decidable #[e]
    let some inst ← synthInstance? decTy | restoreState saved; return none
    let reduced ← withTransparency .all (whnf inst)
    restoreState saved
    match reduced.getAppFn with
    | .const ``Decidable.isTrue _ => return some true
    | .const ``Decidable.isFalse _ => return some false
    | _ => return none
  catch e =>
    rethrowIfFatal e
    restoreState saved
    return none

/-- Reduce `e` under `.all` transparency and classify as `True`/`False`.
    Recurses through `Not`/`And`/`Or`, handles stuck `Eq Bool` between
    distinct ctors, falls back to `tryDecide`. State is restored before
    returning. -/
partial def reducedExpr (e : Expr) : MetaM (Option Bool) := do
  let saved ← saveState
  let structural : MetaM (Option Bool) := do
    try
      let r ← withTransparency .all do
        Meta.reduce e (skipProofs := true) (skipTypes := true)
      if r.isConstOf ``True then return some true
      if r.isConstOf ``False then return some false
      match_expr r with
      | Eq _ a b =>
        let aR ← withTransparency .all (whnf a)
        let bR ← withTransparency .all (whnf b)
        if aR.isConstOf ``Bool.true && bR.isConstOf ``Bool.false then return some false
        if aR.isConstOf ``Bool.false && bR.isConstOf ``Bool.true then return some false
        if aR.isConstOf ``Bool.true && bR.isConstOf ``Bool.true then return some true
        if aR.isConstOf ``Bool.false && bR.isConstOf ``Bool.false then return some true
        -- BEq reflexivity: `(x == y) = true` is True when `x` is defEq to `y`.
        -- Match on the *un-reduced* original `e` because `.all` reduce will
        -- have unfolded `BEq.beq` past its surface form.
        if bR.isConstOf ``Bool.true then
          let eOrig ← instantiateMVars e
          match_expr eOrig with
          | Eq _ aOrig _ =>
            match_expr aOrig with
            | BEq.beq _ _ x y =>
              if ← (try isDefEq x y catch ex => do rethrowIfFatal ex; pure false) then return some true
            | _ => pure ()
          | _ => pure ()
        return none
      | Not p =>
        match ← reducedExpr p with
        | some true => return some false
        | some false => return some true
        | none => return none
      | And a b =>
        let aRed ← reducedExpr a
        let bRed ← reducedExpr b
        match aRed, bRed with
        | some false, _ | _, some false => return some false
        | some true, some true => return some true
        | _, _ => return none
      | Or a b =>
        let aRed ← reducedExpr a
        let bRed ← reducedExpr b
        match aRed, bRed with
        | some true, _ | _, some true => return some true
        | some false, some false => return some false
        | _, _ => return none
      | _ => return none
    catch ex => rethrowIfFatal ex; return none
  let result ← structural
  restoreState saved
  match result with
  | some v => return some v
  | none => tryDecide e
