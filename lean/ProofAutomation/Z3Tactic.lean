/-
  Z3Tactic.lean — A Lean 4 command that translates a stated theorem + the
  current file's `ax_<n>` axioms to SMT-LIB and checks satisfiability via Z3.

  Usage:
    z3   theorem_name                       -- auto-collect every `ax_<n>` in this file
    z3   theorem_name only [ax_5, ax_7]     -- restrict to a subset
    z3   theorem_name only []               -- send no axioms (pure tautology check)
    z3?  …                                  -- verbose: log axiom list, SMT path, unsat core
    z3!  …                                  -- expect sat
    z3!? …                                  -- expect sat, verbose

  Looks up `theorem_name`'s stated type, asserts each axiom, negates the
  goal, and calls Z3. If Z3 returns "unsat", the axioms are sufficient.
  The generated SMT-LIB file is written to a unique path under /tmp/ for
  inspection. Mirrors `z3_local` (tactic-mode equivalent) on the axiom
  side; the only difference is the goal source (named theorem vs. main
  proof target).

  ## `?` is best-effort

  Verbose mode (`z3?` / `z3!?`) sets `(set-option :produce-unsat-cores
  true)` so it can report which axioms were actually used. Z3 then
  disables some preprocessing and equality-propagation paths to keep
  core attribution consistent — the cores-on solver is strictly weaker
  than the cores-off solver. On quantifier-heavy queries (rbtree
  subtyping is the canonical example) `z3? thm` can return `unknown`
  where plain `z3 thm` returns `unsat`. We deliberately do **not**
  auto-fall-back to a cores-off retry: that would mask a real
  solver-mode mismatch. If `?` returns `unknown`, retry without `?`.
-/
import Lean
import ProofAutomation.Helpers

open Lean Meta Elab Tactic

namespace Z3Check

private def z3DefaultTimeoutMs : Nat := 10000
private def maxUnfoldSteps : Nat := 5

/-- Sanitize a string for use as an SMT-LIB simple symbol
    (single-quote is not a valid SMT-LIB simple-symbol character). -/
private def sanitizeSmt (s : String) : String :=
  s.replace "'" "_q"

/-- Sanitize a binder/local `Name` for SMT-LIB. Tactic-introduced binders
    (e.g. from `cases`/`intro`) carry macro scopes stored as
    `n._@.external:.../._hyg.<n>` segments — colons and slashes that no
    `sanitizeSmt` rewrite would catch. Strip scopes before sanitizing.
    Anonymity is preserved (`eraseMacroScopes` is identity on
    `.anonymous`), so callers still need their own anonymous handling. -/
private def sanitizeBinderName (n : Name) : String :=
  sanitizeSmt n.eraseMacroScopes.toString

/-- True iff `s` is a valid SMT-LIB v2 simple symbol: non-empty, doesn't
    start with a digit, and every character is alphanumeric or one of
    `~ ! @ $ % ^ & * _ - + = < > . ? /`. Reserved words are not screened
    — emitted names always contain `ax_` or dots, so they can't collide. -/
private def isSmtSimpleSymbol (s : String) : Bool :=
  match s.toList with
  | [] => false
  | h :: rest =>
    let valid (c : Char) : Bool :=
      c.isAlphanum || "~!@$%^&*_-+=<>.?/".any (· == c)
    !h.isDigit && valid h && rest.all valid

/-- Render a `Name` as an SMT-LIB simple symbol using its *full* dotted
    path (dots rewritten to underscores), so that `A.foo` and `B.foo` map
    to distinct SMT symbols. Throws on `.anonymous` — an anonymous name
    reaching here means an upstream introspection bug. -/
private def nameStr (n : Name) : CoreM String := do
  if n.isAnonymous then
    throwError "z3 nameStr: unexpected anonymous name (upstream produced a Name with no string/num component)"
  return sanitizeSmt (n.toString.replace "." "_")

/-- Safe array access with a descriptive error on out-of-bounds -/
private def getArg (args : Array Expr) (i : Nat) (ctx : String) : CoreM Expr :=
  if h : i < args.size then return args[i]
  else throwError s!"z3: {ctx}: expected at least {i + 1} args, got {args.size}"

/-- Safe access to args[args.size - offset] with bounds checking. Assumes
    `offset ≥ 1` (every call site passes 1 or 2); given that, `args.size ≥
    offset` implies `args.size - offset < args.size`, so the indexed read
    never panics. -/
private def getArgFromEnd (args : Array Expr) (offset : Nat) (ctx : String) : CoreM Expr := do
  if args.size < offset then
    throwError s!"z3: {ctx}: expected at least {offset} args, got {args.size}"
  return args[args.size - offset]!

/-- Reject applications whose arity doesn't match the head's declared
signature. `getArg` / `getArgFromEnd` only check `args.size ≥ N`, so
over-application would otherwise silently drop trailing args and
produce a well-formed but incorrect SMT term. Every fixed-arity clause
in `toSmt`'s dispatch should gate on this. -/
private def expectArity (args : Array Expr) (n : Nat) (ctx : String) : CoreM Unit :=
  unless args.size == n do
    throwError s!"z3: {ctx}: expected exactly {n} args, got {args.size}"

-- ============================================================
-- Datatype introspection
-- ============================================================

structure FieldInfo where
  name : String
  sort : String
  deriving Inhabited

structure CtorDecl where
  name : String
  fields : Array FieldInfo
  deriving Inhabited

structure DatatypeDecl where
  name : String
  ctors : Array CtorDecl
  deriving Inhabited

-- ============================================================
-- Translation state: tracks custom sorts and function declarations
-- ============================================================

structure TransState where
  customSorts : Array String := #[]
  -- (name, argSorts, retSort)
  funDecls : Array (String × Array String × String) := #[]
  datatypes : Array DatatypeDecl := #[]
  /-- Names of datatypes whose registration is in progress or complete.
  Checked before recursing into a datatype's constructors so recursive
  occurrences (e.g. `ilist` referencing itself in `Cons`) short-circuit. -/
  visitedDatatypes : Std.HashSet String := {}
  /-- When set, every `forall` body emitted by `toSmt` is wrapped with
  `(! body :qid <currentQid>)` so Z3's trace output groups all quantifier
  instantiations under the user-axiom name instead of `k!N`. -/
  currentQid : Option String := none
  /-- Every top-level SMT symbol the translator declares (datatype names,
  constructor names, selector names, declared sorts, uninterpreted-function
  names). Quantifier binders are checked against this set so a Lean theorem
  binder named `color` won't shadow the `irbtree.Rbtnode` selector `color`
  inside the emitted SMT — Z3 silently rebinds the inner reference and
  rejects the resulting term with a cryptic "select requires 0 arguments"
  message at the call site, not at the offending binder. -/
  declaredSymbols : Std.HashSet String := {}

abbrev TransM := StateT TransState MetaM

/-- Run `action` with `currentQid` set, restoring on exit. -/
private def withQid {α : Type} (qid : Option String) (action : TransM α) : TransM α := do
  let prev := (← get).currentQid
  modify fun st => { st with currentQid := qid }
  try action
  finally modify fun st => { st with currentQid := prev }

/-- Register `s` as a name declared at the top level of the emitted SMT.
    See `TransState.declaredSymbols`. -/
private def addDeclaredSymbol (s : String) : TransM Unit :=
  modify fun st => { st with declaredSymbols := st.declaredSymbols.insert s }

private def addSort (s : String) : TransM Unit := do
  if s == "Int" || s == "Bool" then pure ()
  else
    addDeclaredSymbol s
    modify fun st =>
      if st.customSorts.contains s then st
      else { st with customSorts := st.customSorts.push s }

private def addFunc (name : String) (argSorts : Array String) (retSort : String) : TransM Unit := do
  let st ← get
  if let some (_, existArgs, existRet) := st.funDecls.find? (fun (n, _, _) => n == name) then
    if existArgs != argSorts || existRet != retSort then
      throwError s!"z3 addFunc: conflicting signatures for '{name}': ({existArgs} → {existRet}) vs ({argSorts} → {retSort})"
  else
    addDeclaredSymbol name
    modify fun st => { st with funDecls := st.funDecls.push (name, argSorts, retSort) }

-- ============================================================
-- Sort translation: Lean Expr (type) → SMT-LIB sort string
-- ============================================================

mutual
private partial def sortToSmt (e : Expr) : TransM String := do
  let e := e.consumeMData
  match e with
  | Expr.const ``Int _  => return "Int"
  | Expr.const ``Bool _ => return "Bool"
  | Expr.const ``Nat _  => throwError s!"z3 sortToSmt: Nat is not directly supported — use Int instead"
  | Expr.sort lvl =>
    if lvl == .zero then return "Bool"  -- Prop maps to Bool in SMT-LIB
    else throwError s!"z3: cannot translate Sort level {lvl} to SMT-LIB (only Prop/Sort 0 is supported)"
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | Expr.const ``Option _ =>
      -- Strip Option: Option T → T
      if args.size > 0 then sortToSmt args[0]!
      else throwError s!"z3 sortToSmt: Option with 0 type args"
    | Expr.const name _ =>
      let s ← nameStr name
      let env ← getEnv
      if let some (.inductInfo val) := env.find? name then
        registerDatatype s name val
      else
        addSort s
      return s
    | _ => throwError m!"z3 sortToSmt: cannot translate sort expression: {e}"

/-- Register an inductive type as an SMT-LIB datatype with constructors and selectors -/
private partial def registerDatatype (dtName : String) (_name : Name) (val : InductiveVal) : TransM Unit := do
  if (← get).visitedDatatypes.contains dtName then return
  modify fun st => { st with visitedDatatypes := st.visitedDatatypes.insert dtName }
  let env ← getEnv
  let ctors : Array CtorDecl ← val.ctors.toArray.mapM fun ctorName => do
    let some (.ctorInfo cval) := env.find? ctorName
      | throwError m!"z3 registerDatatype: constructor '{ctorName}' not found in environment for datatype '{dtName}'"
    let fields ← extractCtorFields cval.type val.numParams
    return { name := (← nameStr ctorName), fields }
  if ctors.isEmpty then
    throwError s!"z3 registerDatatype: datatype '{dtName}' has no constructors"
  -- SMT-LIB requires every selector in a `declare-datatypes` block to be
  -- unique across the whole datatype; a duplicate produces broken SMT
  -- visible only as a downstream Z3 parse error. Catch it loudly here.
  let mut seen : Std.HashMap String (String × String) := {}
  for ctor in ctors do
    for field in ctor.fields do
      match seen[field.name]? with
      | some (prevCtor, prevSort) =>
        throwError s!"z3 registerDatatype: datatype '{dtName}' has selector '{field.name}' \
          declared in both ctor '{prevCtor}' (sort '{prevSort}') and ctor '{ctor.name}' \
          (sort '{field.sort}'); SMT-LIB requires per-datatype selector uniqueness."
      | none =>
        seen := seen.insert field.name (ctor.name, field.sort)
  addDeclaredSymbol dtName
  for ctor in ctors do
    addDeclaredSymbol ctor.name
    for field in ctor.fields do
      addDeclaredSymbol field.name
  modify fun st => { st with datatypes := st.datatypes.push { name := dtName, ctors } }

/-- Extract field names and sorts from a constructor type, skipping the first
    `numParams` binders (the inductive's type parameters) and any non-explicit
    binders (implicit / instance args on GADT-ish ctors). Uses `forallTelescope`
    so each field's type is closed (loose BVars get instantiated with fresh
    fvars), which is strictly more correct than walking the raw `Expr.forallE`
    chain for polymorphic datatypes — and the user-facing monomorphic
    datatypes (`ilist`, etc.) round-trip identically. -/
private partial def extractCtorFields (ty : Expr) (numParams : Nat) : TransM (Array FieldInfo) :=
  forallTelescope ty fun fvars _body => do
    let fieldFvars := fvars.extract numParams fvars.size
    let mut fields : Array FieldInfo := #[]
    let mut explicitIdx : Nat := 0
    for fv in fieldFvars do
      let decl ← fv.fvarId!.getDecl
      if decl.binderInfo != .default then continue
      let sort ← sortToSmt (← inferType fv)
      let fieldName :=
        if decl.userName.isAnonymous then s!"field_{explicitIdx}"
        else decl.userName.toString
      fields := fields.push { name := fieldName, sort }
      explicitIdx := explicitIdx + 1
    return fields
end

-- ============================================================
-- Datatype recognizer/accessor detection
-- ============================================================

/-- Unfold a definition body through match_N auxiliaries to expose the underlying recursor.
    Returns `(reducedExpr, env)` or `none` if no recursor is reached. -/
private def unfoldToRecursor (env : Environment) (body : Expr) : TransM Expr := do
  let body0 ← withTransparency .all <| whnf body
  let mut body' := body0
  let mut steps := 0
  for _ in [:maxUnfoldSteps] do
    let hd := body'.consumeMData.getAppFn.consumeMData
    match hd with
    | .const hdName _ =>
      match env.find? hdName with
      | some (.recInfo _) => break
      | some (.defnInfo hdDefn) =>
        let hdArgs := body'.consumeMData.getAppArgs
        body' ← withTransparency .all <| whnf (hdDefn.value.beta hdArgs)
        steps := steps + 1
      -- Any other constant kind (ctor, inductive, axiom, ...) is a legitimate
      -- "this def doesn't unfold to a recursor" outcome — stop and let the
      -- caller's `recInfo` match return none. Only env corruption is a bug.
      | some _ => break
      | none => throwError m!"z3 unfoldToRecursor: constant '{hdName}' not found in environment"
    | _ => break
  -- Cap exhaustion: warn so the user can raise `maxUnfoldSteps` if the head
  -- is a real recognizer/accessor.
  if steps == maxUnfoldSteps then
    if let .const hdName _ := body'.consumeMData.getAppFn.consumeMData then
      if let some (.defnInfo _) := env.find? hdName then
        logWarning m!"z3 unfoldToRecursor: hit unfold cap ({maxUnfoldSteps}) at '{hdName}'; \
          containing function will be treated as uninterpreted. Raise `maxUnfoldSteps` if this is a \
          recognizer/accessor that needs deeper unfolding."
  return body'

/-- Reduce branches via lambdaTelescope + whnf, returning (branchFvars, reducedBody) pairs. -/
private def reduceBranches (branches : Array Expr) : TransM (Array (Array Expr × Expr)) :=
  branches.mapM fun b =>
    lambdaTelescope b fun bfvs bdy => do
      let r ← withTransparency .all <| whnf bdy
      return (bfvs, r)

/-- Detect if reduced branches form a recognizer pattern (one true, rest false).
    Returns the index of the true-constructor, or `none`. -/
private def detectRecognizer (reducedBranches : Array (Array Expr × Expr)) : Option Nat := Id.run do
  let mut trueCtorIdx : Option Nat := none
  for ((_, rbody), i) in reducedBranches.zipIdx do
    match rbody.consumeMData with
    | .const ``Bool.true _ =>
      if trueCtorIdx.isSome then return none
      trueCtorIdx := some i
    | .const ``Bool.false _ => pure ()
    | _ => return none
  return trueCtorIdx

/-- Detect if reduced branches form an accessor pattern (one Option.some for a field, rest Option.none).
    Returns `(ctorIdx, fieldIdx)` or `none`. -/
private def detectAccessor (reducedBranches : Array (Array Expr × Expr)) (dt : DatatypeDecl) : Option (Nat × Nat) := Id.run do
  let mut accessorInfo : Option (Nat × Nat) := none
  for (br, i) in reducedBranches.zipIdx do
    if i >= dt.ctors.size then return none
    let ctorInfo := dt.ctors[i]!
    let nFields := ctorInfo.fields.size
    let (bfvars, rbody) := br
    let bodyFn := rbody.consumeMData.getAppFn.consumeMData
    match bodyFn with
    | .const ``Option.some _ =>
      let bodyArgs := rbody.consumeMData.getAppArgs
      if bodyArgs.size < 2 then return none
      let valExpr := bodyArgs[1]!.consumeMData
      let some j := bfvars.findIdx? (· == valExpr) | return none
      if j >= nFields then return none
      if accessorInfo.isSome then return none
      accessorInfo := some (i, j)
    | .const ``Option.none _ => pure ()
    | _ => return none
  return accessorInfo

/-- Try to translate a user function application as a Z3 datatype tester or selector.
    - Recognizer: `is_leaf t` → `((_ is Leaf) t)`
    - Accessor:   `value t`   → `(Node-value t)` -/
private def tryDatatypeBuiltin (translateExpr : Expr → TransM String)
    (fn : Expr) (allArgs : Array Expr) : TransM (Option String) := do
  let .const fnName _ := fn | return none
  let env ← getEnv
  let some (.defnInfo defn) := env.find? fnName | return none
  lambdaTelescope defn.value fun fvars body => do
    let body' ← unfoldToRecursor env body
    let redFn := body'.consumeMData.getAppFn.consumeMData
    let redArgs := body'.consumeMData.getAppArgs
    let .const recName _ := redFn | return none
    let some (.recInfo rval) := env.find? recName | return none
    let indName := recName.getPrefix
    let dtName ← nameStr indName
    let st ← get
    let some dt := st.datatypes.find? (fun d => d.name == dtName) | return none
    -- Past this point we've identified a recursor on a known datatype — errors are bugs
    let isCasesOn := recName == Name.mkStr indName "casesOn"
    let majorIdx := if isCasesOn
      then rval.numParams + rval.numMotives + rval.numIndices
      else rval.numParams + rval.numMotives + rval.numMinors + rval.numIndices
    let branchStart := if isCasesOn
      then majorIdx + 1
      else rval.numParams + rval.numMotives
    if redArgs.size < branchStart + rval.numMinors then
      throwError m!"z3 tryDatatypeBuiltin: not enough args for branches in '{fnName}': {redArgs.size} < {branchStart + rval.numMinors} (recursor={recName})"
    if majorIdx >= redArgs.size then
      throwError m!"z3 tryDatatypeBuiltin: majorIdx {majorIdx} out of bounds for '{fnName}' (redArgs.size={redArgs.size}, recursor={recName})"
    let scrutineeFvar := redArgs[majorIdx]!
    let some argIdx := fvars.findIdx? (· == scrutineeFvar)
      | throwError m!"z3 tryDatatypeBuiltin: scrutinee fvar not found among function params for '{fnName}' (recursor={recName})"
    if argIdx >= allArgs.size then
      throwError m!"z3 tryDatatypeBuiltin: scrutinee argIdx {argIdx} >= allArgs.size {allArgs.size} for '{fnName}'"
    let actualArg := allArgs[argIdx]!
    let branches := redArgs.extract branchStart (branchStart + rval.numMinors)
    if branches.size != dt.ctors.size then
      throwError m!"z3 tryDatatypeBuiltin: branch count {branches.size} != ctor count {dt.ctors.size} for '{fnName}' on datatype '{dtName}'"
    let reducedBranches ← reduceBranches branches
    -- Try recognizer detection
    if let some idx := detectRecognizer reducedBranches then
      if idx < dt.ctors.size then
        let ctorDecl := dt.ctors[idx]!
        let scrutStr ← translateExpr actualArg
        return some s!"((_ is {ctorDecl.name}) {scrutStr})"
    -- Try accessor detection
    if let some (ctorIdx, fieldIdx) := detectAccessor reducedBranches dt then
      if ctorIdx < dt.ctors.size then
        let ctor := dt.ctors[ctorIdx]!
        if fieldIdx < ctor.fields.size then
          let field := ctor.fields[fieldIdx]!
          let scrutStr ← translateExpr actualArg
          return some s!"({field.name} {scrutStr})"
    return none

-- ============================================================
-- Helper functions
-- ============================================================

/-- Recursively strip Option.some and Coe.coe wrappers.
    Throws if the wrapper has fewer args than expected — this indicates a malformed Expr,
    and aborting the elaborator with no context is worse than surfacing the offending term. -/
private partial def unwrap (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | Expr.const ``Option.some _ =>
    if args.size > 1 then unwrap args[1]!
    else throwError "z3 unwrap: Option.some with {args.size} args (expected ≥ 2)\n  offending expr: {e}"
  | Expr.const ``Coe.coe _ =>
    expectArity args 4 "Coe.coe (unwrap)"
    unwrap args[3]!
  | _ => return e

/-- Detect @Eq Bool x true/false patterns (Bool→Prop coercion).
    Returns (expr, isTrue) where expr is the boolean expression. -/
private def boolEqTrue? (ty lhs rhs : Expr) : Option (Expr × Bool) :=
  match ty.consumeMData with
  | Expr.const ``Bool _ =>
    match rhs.consumeMData with
    | Expr.const ``Bool.true _  => some (lhs, true)
    | Expr.const ``Bool.false _ => some (lhs, false)
    | _ => match lhs.consumeMData with
      | Expr.const ``Bool.true _  => some (rhs, true)
      | Expr.const ``Bool.false _ => some (rhs, false)
      | _ => none
  | _ => none

/-- Extract explicit args, their sorts, and the return sort from a function's
    declared type. This avoids calling inferType on expressions with loose bvars.

    After consuming `allArgs`, the residual type must be non-`forallE`:
    otherwise the caller supplied fewer arguments than the function's arity
    (partial application), and falling through to `sortToSmt ty` would emit a
    confusing "cannot translate sort expression" pointing at a forall. We
    detect that case explicitly. -/
private partial def analyzeApp (fnTy : Expr) (allArgs : Array Expr) : TransM (Array Expr × Array String × String) := do
  let mut eArgs : Array Expr := #[]
  let mut aSorts : Array String := #[]
  let mut ty := fnTy
  for (arg, i) in allArgs.zipIdx do
    match ty.consumeMData with
    | Expr.forallE _ argTy body bi =>
      if bi == .default then
        eArgs := eArgs.push arg
        aSorts := aSorts.push (← sortToSmt argTy)
      ty := body.instantiate1 arg
    | other =>
      throwError m!"z3 analyzeApp: expected forallE in function type at arg {i}, got {other.ctorName}: {other}"
  if ty.consumeMData.isForall then
    throwError m!"z3 analyzeApp: arity mismatch — applied {allArgs.size} argument(s), but function still has unconsumed binders. Residual type: {ty}"
  let retSort ← sortToSmt ty
  return (eArgs, aSorts, retSort)

-- ============================================================
-- Main translator: Lean Expr → SMT-LIB string
-- ============================================================

-- Lean Name → (SMT-LIB spelling, Lean arity). `binLastOps` take the last
-- two args of their arity-counted application; `binFirstOps` take the first two.
private def binLastOps : List (Name × String × Nat) :=
  [(``HSub.hSub, "-", 6), (``HAdd.hAdd, "+", 6), (``HMul.hMul, "*", 6),
   (``HDiv.hDiv, "div", 6), (``HMod.hMod, "mod", 6),
   (``GE.ge, ">=", 4), (``LE.le, "<=", 4), (``GT.gt, ">", 4), (``LT.lt, "<", 4)]

private def binFirstOps : List (Name × String) :=
  [(``And, "and"), (``Or, "or"), (``Iff, "="),
   (``and, "and"), (``or, "or"), (``xor, "xor")]

private def unOps : List (Name × String) :=
  [(``Not, "not"), (``not, "not")]

private def nullaryOps : List (Name × String) :=
  [(``True, "true"), (``False, "false"),
   (``Bool.true, "true"), (``Bool.false, "false")]

private partial def toSmt (bv : List String) (e : Expr) : TransM String := do
  let e := e.consumeMData
  match e with
  -- Bound variable (de Bruijn index)
  | Expr.bvar i =>
    if i < bv.length then
      let s := bv.getD i ""
      if s.isEmpty then
        throwError s!"z3 toSmt: bvar {i} resolved to empty name (bv={bv})"
      return s
    else throwError s!"z3 toSmt: loose bound variable ?b{i} (bv depth={bv.length})"
  -- Free variable
  | Expr.fvar id => return sanitizeBinderName (← id.getDecl).userName
  -- Literal
  | Expr.lit (Literal.natVal n) => return toString n
  -- Forall / implication. SMT-LIB has two relevant shapes:
  --   `(forall ((x T)) body)` — `T` must be a *sort*, `body` a formula.
  --   `(=> A B)`              — both `A` and `B` must be *formulas* (Prop/Bool).
  -- A Lean `forallE` maps to implication only when both: (a) the binder is
  -- unused in body, so we can drop the witness; (b) the LHS is a Prop, so
  -- it's a translatable formula. Every other case is a universal quantifier.
  | Expr.forallE name ty body _ =>
    let nm := if name.isAnonymous then s!"_x{bv.length}" else sanitizeBinderName name
    let isLhsProp ← Meta.isProp ty
    let isUnusedPropHyp := isLhsProp && !body.hasLooseBVar 0
    if isUnusedPropHyp then
      let l ← toSmt bv ty
      let r ← toSmt ("_" :: bv) body
      return s!"(=> {l} {r})"
    let s ← try sortToSmt ty
      catch e =>
        -- `ty` may carry loose bvars from outer binders we walked past
        -- without telescoping (e.g. `∀ T, ∀ x : T, …` reaches the inner
        -- forallE with `ty = .bvar 0`). `inferType` throws on loose
        -- bvars; without this guard the catch raises a new error that
        -- masks the real sortToSmt failure.
        let tyStr ← try Meta.ppExpr ty catch _ => pure "<unprintable>"
        let kindStr ← try
          let k ← inferType ty
          Meta.ppExpr k
        catch _ => pure "<unprintable>"
        let usageHint :=
          if body.hasLooseBVar 0 then
            "the binder is used in the body, so the LHS must be translatable to an SMT sort"
          else
            "the binder is unused; if it's a Prop hypothesis it should translate, otherwise drop it (e.g. `(_x : Bool) → ...` is the common offender)"
        throwError m!"z3 toSmt: cannot translate forall binder `{nm} : {tyStr}` (kind `{kindStr}`). \
          {usageHint}. Underlying sortToSmt error: {e.toMessageData}"
    if bv.contains nm then
      throwError m!"z3 toSmt: forall binder `{nm}` shadows an outer binder of the same name \
        (bv stack = {bv}). After macro-scope erasure two distinct Lean binders collapsed to \
        the same SMT symbol; emitting both would let Z3 bind the inner reference to the wrong \
        quantifier. Rename one of the binders before invoking the tactic, or extend \
        `sanitizeBinderName` with a depth suffix when collisions become common."
    if (← get).declaredSymbols.contains nm then
      throwError m!"z3 toSmt: forall binder `{nm}` shadows a top-level SMT symbol of the same \
        name (datatype, constructor, selector, declared sort, or uninterpreted function). \
        Z3 would silently rebind the inner reference to the binder, then fail at the call site \
        with an unhelpful arity/sort message (typically 'select requires 0 arguments'). \
        Rename the binder in the source theorem to a non-colliding name."
    let b ← toSmt (nm :: bv) body
    let bAnnotated ← do
      match (← get).currentQid with
      | some q => pure s!"(! {b} :qid {q})"
      | none => pure b
    return s!"(forall (({nm} {s})) {bAnnotated})"
  -- Explicit errors for unsupported expression kinds
  | Expr.lam nm _ _ _ => throwError m!"z3 toSmt: unexpected lambda expression (name={nm}) — lambdas should only appear inside Exists"
  | Expr.letE nm _ _ _ _ => throwError m!"z3 toSmt: let-expressions not supported (name={nm})"
  | Expr.mvar id => throwError m!"z3 toSmt: unresolved metavariable {id.name}"
  | Expr.proj typeName idx _ => throwError m!"z3 toSmt: projection expressions not supported ({typeName}.{idx})"
  -- Everything else: decompose as function application
  | _ => goApp e
where
  goApp (e : Expr) : TransM String := do
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | Expr.const name _ =>
      if let some op := nullaryOps.lookup name then
        expectArity args 0 op
        return op
      if let some (op, arity) := binLastOps.lookup name then
        expectArity args arity op
        return ← bin op (← getArgFromEnd args 2 op) (← getArgFromEnd args 1 op)
      if let some op := binFirstOps.lookup name then
        expectArity args 2 op
        return ← bin op (← getArg args 0 op) (← getArg args 1 op)
      if let some op := unOps.lookup name then
        expectArity args 1 op
        return ← un op (← getArg args 0 op)
      match name with
      -- ── Equality ──
      | ``Eq =>
        expectArity args 3 "Eq"
        let ty ← getArg args 0 "Eq"
        let lhs ← unwrap (← getArg args 1 "Eq")
        let rhs ← unwrap (← getArg args 2 "Eq")
        match boolEqTrue? ty lhs rhs with
        | some (expr, true)  => toSmt bv expr
        | some (expr, false) => do
          let s ← toSmt bv expr; return s!"(not {s})"
        | none => bin "=" lhs rhs

      -- ── Existential ──
      | ``Exists =>
        expectArity args 2 "Exists"
        match (← getArg args 1 "Exists").consumeMData with
        | Expr.lam nm ty body _ =>
          let s ← sortToSmt ty
          let nmStr := sanitizeBinderName nm
          if bv.contains nmStr then
            throwError m!"z3 toSmt: exists binder `{nmStr}` shadows an outer binder of the same \
              name (bv stack = {bv}). After macro-scope erasure two distinct Lean binders \
              collapsed to the same SMT symbol; emitting both would let Z3 bind the inner \
              reference to the wrong quantifier. Rename one of the binders before invoking the \
              tactic, or extend `sanitizeBinderName` with a depth suffix when collisions become \
              common."
          if (← get).declaredSymbols.contains nmStr then
            throwError m!"z3 toSmt: exists binder `{nmStr}` shadows a top-level SMT symbol of \
              the same name (datatype, constructor, selector, declared sort, or uninterpreted \
              function). Z3 would silently rebind the inner reference to the binder, then fail \
              at the call site with an unhelpful arity/sort message (typically 'select requires \
              0 arguments'). Rename the binder in the source theorem to a non-colliding name."
          let b ← toSmt (nmStr :: bv) body
          return s!"(exists (({nmStr} {s})) {b})"
        | _ => throwError "z3: Exists without lambda body"

      -- ── Numeric literals ──
      | ``OfNat.ofNat =>
        expectArity args 3 "OfNat.ofNat"
        let α := (← getArg args 0 "OfNat").consumeMData
        unless α.isConstOf ``Int do
          throwError m!"z3: OfNat literal at unsupported sort {α} — only Int is supported"
        match (← getArg args 1 "OfNat").consumeMData with
        | Expr.lit (Literal.natVal n) => return toString n
        | _ => throwError "z3: OfNat with non-literal arg"
      | ``Int.ofNat =>
        expectArity args 1 "Int.ofNat"
        toSmt bv (← getArg args 0 "Int.ofNat")
      | ``Int.negSucc =>
        expectArity args 1 "Int.negSucc"
        match (← getArg args 0 "Int.negSucc").consumeMData with
        | Expr.lit (Literal.natVal n) => return s!"(- {n + 1})"
        | _ => throwError "z3: negSucc with non-literal"
      | ``Neg.neg => do
        expectArity args 3 "Neg.neg"
        let s ← toSmt bv (← getArgFromEnd args 1 "Neg"); return s!"(- {s})"

      | ``BEq.beq =>
        -- @BEq.beq α inst a b — last 2 args are the actual values
        expectArity args 4 "BEq.beq"
        let l ← unwrap (← getArgFromEnd args 2 "BEq")
        let r ← unwrap (← getArgFromEnd args 1 "BEq")
        bin "=" l r

      -- ── ite ──
      | ``ite => do
        expectArity args 5 "ite"
        let c ← toSmt bv (← getArg args 1 "ite")
        let t ← toSmt bv (← getArg args 3 "ite")
        let el ← toSmt bv (← getArg args 4 "ite")
        return s!"(ite {c} {t} {el})"

      -- ── Wrappers to strip ──
      | ``Option.some =>
        expectArity args 2 "Option.some"
        toSmt bv (← getArg args 1 "Option.some")
      | ``Coe.coe =>
        expectArity args 4 "Coe.coe"
        toSmt bv (← getArgFromEnd args 1 "Coe.coe")
      | ``decide =>
        expectArity args 2 "decide"
        toSmt bv (← getArg args 0 "decide")

      -- ── Constructor or user-defined function ──
      | _ => do
        let env ← getEnv
        match env.find? name with
        | some (.ctorInfo cval) =>
          -- Walk `cval.type` to filter args by explicitness: skip the first
          -- `numParams` type-parameter binders, then keep only `.default`
          -- binders. Implicit/instance args (e.g. `[Decidable α]` on GADT-ish
          -- ctors) must not leak into SMT — the corresponding SMT-LIB ctor
          -- declared by `extractCtorFields` filters the same way.
          let mut explicitArgs : Array Expr := #[]
          let mut t : Expr := cval.type
          for (arg, i) in args.zipIdx do
            match t.consumeMData with
            | Expr.forallE _ _ body bi =>
              if i >= cval.numParams && bi == .default then
                explicitArgs := explicitArgs.push arg
              t := body.instantiate1 arg
            | other =>
              throwError m!"z3 ctor '{name}': forallE chain exhausted at arg \
                {i}, got {other.ctorName}: {other}"
          let ctorName ← nameStr name
          if explicitArgs.isEmpty then return ctorName
          else
            let argStrs ← explicitArgs.toList.mapM (toSmt bv)
            return s!"({ctorName} {" ".intercalate argStrs})"
        | _ =>
          -- Analyze function signature (also registers datatype sorts via sortToSmt)
          let ci ← getConstInfo name
          let (ea, aSorts, rSort) ← analyzeApp ci.type args
          -- Try recognizer/accessor detection before falling back to uninterpreted.
          -- `tryDatatypeBuiltin` returns `none` for every "not applicable" case
          -- and only throws on genuine bugs (out-of-bounds, branch-count mismatch,
          -- env corruption). Surface those rather than swallowing them.
          let builtinResult ← tryDatatypeBuiltin (toSmt bv) fn args
          if let some smtStr := builtinResult then
            return smtStr
          -- Fall through to uninterpreted function
          let fnName ← nameStr name
          addFunc fnName aSorts rSort
          let aStrs ← ea.toList.mapM (toSmt bv)
          if aStrs.isEmpty then return fnName
          else return s!"({fnName} {" ".intercalate aStrs})"

    | _ => throwError m!"z3: unsupported expression head: {fn}"

  bin (op : String) (l r : Expr) : TransM String := do
    let ls ← toSmt bv l; let rs ← toSmt bv r
    return s!"({op} {ls} {rs})"
  un (op : String) (x : Expr) : TransM String := do
    let xs ← toSmt bv x
    return s!"({op} {xs})"

-- ============================================================
-- SMT-LIB query assembly
-- ============================================================

private def buildQuery (axiomTypes : Array Expr) (goalType : Expr)
    (axiomNames : Array Name := #[])
    (timeoutMs : Nat := z3DefaultTimeoutMs)
    (produceCores : Bool := false) : MetaM String := do
  -- SMT-LIB symbol form for a Lean `Name`. Pipe-quoted only when the
  -- string contains characters outside SMT-LIB's simple-symbol grammar
  -- (or starts with a digit) — keeps dumped queries readable for typical
  -- axiom names like `ax_5` or `Tests.PBT.ax_3`. Both forms round-trip
  -- via `String.toName` in `parseUnsatCore`.
  let nameToSmtSym (n : Name) : String :=
    let s := n.toString
    if isSmtSimpleSymbol s then s else s!"|{s}|"
  let ((axiomStrs, goalStr), st) ← (do
    let mut aStrs : Array String := #[]
    for h : i in [0 : axiomTypes.size] do
      let ax := axiomTypes[i]
      let qid := axiomNames[i]?.map nameToSmtSym
      aStrs := aStrs.push (← withQid qid (toSmt [] ax))
    let g ← toSmt [] goalType
    return (aStrs, g)
  : TransM _).run {}

  -- Build the file as a concatenation of section arrays. Order matters:
  -- (set-option :produce-unsat-cores ...) MUST precede (set-logic ALL).
  let header : Array String :=
    (if produceCores then #["(set-option :produce-unsat-cores true)"] else #[])
    ++ #["(set-logic ALL)", s!"(set-option :timeout {timeoutMs})", ""]

  let dtNames : Std.HashSet String :=
    st.datatypes.foldl (init := ∅) fun acc d => acc.insert d.name

  let datatypeLines : Array String := st.datatypes.map fun dt =>
    let ctorStrs := dt.ctors.map fun ctor =>
      if ctor.fields.isEmpty then s!"({ctor.name})"
      else
        let fields := ctor.fields.map fun f => s!"({f.name} {f.sort})"
        s!"({ctor.name} {" ".intercalate fields.toList})"
    s!"(declare-datatypes (({dt.name} 0)) (({" ".intercalate ctorStrs.toList})))"

  let sortLines : Array String := st.customSorts.filterMap fun s =>
    if dtNames.contains s then none else some s!"(declare-sort {s} 0)"

  let funDeclLines : Array String := st.funDecls.map fun (name, aSorts, rSort) =>
    s!"(declare-fun {name} ({" ".intercalate aSorts.toList}) {rSort})"

  let axiomLines : Array String := (axiomStrs.mapIdx fun idx ax =>
    let body := match axiomNames[idx]? with
      | some name => s!"(assert (! {ax} :named {nameToSmtSym name}))"
      | none      => s!"(assert {ax})"
    #[s!"; axiom {idx}", body]).flatten

  let goalLines : Array String :=
    #["; === negated goal ===", s!"(assert (not {goalStr}))", ""]

  let footer : Array String :=
    #["(check-sat)"] ++ (if produceCores then #["(get-unsat-core)"] else #[])

  let lines : Array String :=
    header ++ datatypeLines ++ sortLines ++ funDeclLines ++ #[""]
      ++ axiomLines ++ #[""] ++ goalLines ++ footer
  return "\n".intercalate lines.toList

-- ============================================================
-- Z3 invocation
-- ============================================================

/-- Outcome of invoking Z3 on a query. `unknown` is the *informational*
    after-verdict case — Z3 ran cleanly, looked at the query, and
    couldn't decide (timeout, incomplete theory, quantifier instantiation
    gave up). `error` is the *fatal* before-verdict case — Z3 itself
    failed: malformed SMT query (`(error …)` on stdout), non-zero exit,
    empty stdout, or unrecognized first line. These MUST stay distinct
    so we don't mis-attribute "Z3 said the query is broken" as "axioms
    are insufficient." See root CLAUDE.md "External tool failures must
    surface, not collapse to a neutral verdict."

    No `deriving Inhabited`: defaulting to `.unsat` (the first ctor) on
    any panic-recovery path would silently fabricate a proof. -/
inductive Z3Result where
  | unsat
  | sat
  | unknown (reason : String)
  | error   (reason : String)

structure Z3Output where
  result : Z3Result
  smtFile : System.FilePath
  /-- Names of axioms in Z3's reported unsat core, if `parseCores` was requested
      and the result was `unsat`. `none` otherwise. Note: Z3's core isn't
      *guaranteed* minimal — it's the set of `(! ... :named foo)`-labeled
      assertions the solver touched. In practice it's tight for our queries. -/
  usedAxioms : Option (Array Name) := none

/-- Resolve the Z3 binary. Honours `Z3_PATH` if set (must be an explicit path
    to an existing file — we don't treat it as a PATH-style lookup), and
    otherwise falls back to `z3` on `PATH`. An *explicitly-set-but-empty*
    `Z3_PATH` is an error rather than a silent fallback (no-silent-fallback
    rule — user clearly intended to override but supplied nothing). -/
private def resolveZ3Binary : IO String := do
  match ← IO.getEnv "Z3_PATH" with
  | some p =>
    let p := p.trimAscii.toString
    if p.isEmpty then
      throw <| IO.userError "z3: Z3_PATH is set but empty. \
        Unset Z3_PATH to fall back to a 'z3' on PATH, or point it at the Z3 4.15.1 binary."
    if ← System.FilePath.pathExists p then
      return p
    throw <| IO.userError s!"z3: Z3_PATH is set to '{p}' but no file exists at that path. \
      Unset Z3_PATH to fall back to a 'z3' on PATH, or point it at the Z3 4.15.1 binary."
  | none => return "z3"

/-- Parse a `(get-unsat-core)` response line. Z3 emits piped names like
    `(|ax.foo| |bar|)` for symbols needing quoting, and bare tokens like
    `(ax_5 ax_7)` for simple SMT-LIB symbols. Handle both.

    Returns `Except String (Array Name)` so malformed cores (unterminated
    pipe, unexpected paren, empty quoted symbol, missing enclosing
    parens, embedded quote) surface as an explicit error rather than
    being silently coerced into bogus names. Hierarchical names like
    `Tests.X.ax_zero` round-trip via `String.toName`, not
    `Name.mkSimple` (which would produce a single-component name that
    fails downstream `==` comparison against `axiomNames`). -/
private partial def parseUnsatCoreBody
    (chars : List Char) (acc : Array Name) (buf : String) (inPipe : Bool)
    (orig : String) : Except String (Array Name) :=
  match chars with
  | [] =>
    if inPipe then .error s!"unterminated '|' in core line: '{orig}'"
    else if buf.isEmpty then .ok acc
    else .ok (acc.push buf.toName)
  | c :: rest =>
    if inPipe then
      if c == '|' then
        if buf.isEmpty then .error s!"empty quoted symbol in core line: '{orig}'"
        else parseUnsatCoreBody rest (acc.push buf.toName) "" false orig
      else parseUnsatCoreBody rest acc (buf.push c) true orig
    else if c == '|' then
      let acc' := if buf.isEmpty then acc else acc.push buf.toName
      parseUnsatCoreBody rest acc' "" true orig
    else if c.isWhitespace then
      let acc' := if buf.isEmpty then acc else acc.push buf.toName
      parseUnsatCoreBody rest acc' "" false orig
    else if c == '(' || c == ')' || c == '"' then
      .error s!"unexpected '{c}' in core line body: '{orig}'"
    else
      parseUnsatCoreBody rest acc (buf.push c) false orig

private def parseUnsatCore (line : String) : Except String (Array Name) := do
  let trimmed := line.trimAscii.toString
  unless trimmed.startsWith "(" do
    throw s!"core line must start with '(' — got: '{trimmed}'"
  unless trimmed.endsWith ")" do
    throw s!"core line must end with ')' — got: '{trimmed}'"
  let body := ((trimmed.toRawSubstring.drop 1).dropRight 1).toString
  parseUnsatCoreBody body.toList #[] "" false trimmed

private def runZ3 (query : String) (parseCores : Bool := false) : IO Z3Output := do
  -- PID disambiguates across parallel lean processes (lake builds Tests.* in
  -- parallel); monoNanosNow disambiguates within a process.
  let path : System.FilePath :=
    s!"/tmp/z3_lean_check_{← IO.Process.getPID}_{← IO.monoNanosNow}.smt2"
  try
    IO.FS.writeFile path query
  catch e =>
    throw <| IO.userError s!"z3: failed to write SMT query to '{path}': {e}"
  let z3Cmd ← resolveZ3Binary
  let r ← try
    IO.Process.output { cmd := z3Cmd, args := #[path.toString] }
  catch e =>
    let src :=
      if z3Cmd == "z3" then "'z3' on PATH"
      else s!"Z3_PATH='{z3Cmd}'"
    throw <| IO.userError s!"z3: failed to invoke Z3 ({src}): {e}\n\
      Totem requires Z3 4.15.1. Either install it on PATH or set Z3_PATH \
      to the absolute path of the binary."
  -- Classify Z3's output into a Z3Result. Z3 emits malformed-query errors
  -- as `(error …)` s-expressions on STDOUT (not stderr) before / after the
  -- verdict line, so we collect them by line-prefix. Genuine inconclusive
  -- results show up as a `unknown` verdict line.
  let allLines := r.stdout.splitOn "\n"
  let isErrorLine (l : String) : Bool := l.trimAscii.toString.startsWith "(error"
  let isBlankLine (l : String) : Bool := l.trimAscii.toString.isEmpty
  let errorLines := allLines.filter isErrorLine
  let verdictLine? := allLines.find? fun l => !isErrorLine l && !isBlankLine l
  let stderrTrimmed := r.stderr.trimAscii.toString
  let stderrInfo := if stderrTrimmed.isEmpty then "" else s!"\nstderr: {stderrTrimmed}"
  -- Z3's most actionable diagnostic is the `(error ...)` line on stdout, not
  -- stderr — include it in every error path so the caller doesn't have to
  -- open the SMT file to find out what went wrong.
  let errorLinesInfo :=
    if errorLines.isEmpty then ""
    else s!"\nZ3 stdout error(s) ({errorLines.length}):\n  " ++
      "\n  ".intercalate (errorLines.map fun l => l.trimAscii.toString)
  -- Both non-zero exit and non-empty stderr are fatal-before-verdict: any
  -- stdout verdict is unreliable. Z3 emits `WARNING: unknown logic` to stderr
  -- with exit 0, which would otherwise let an unrelated `unsat` slip through.
  let result : Z3Result :=
    if r.exitCode != 0 then
      let verdictHint := match verdictLine? with
        | some line => s!" (stdout verdict: '{line.trimAscii.toString}')"
        | none      => ""
      Z3Result.error s!"Z3 exited non-zero (exit code {r.exitCode}){verdictHint}{errorLinesInfo}{stderrInfo}"
    else if !stderrTrimmed.isEmpty then
      let verdictHint := match verdictLine? with
        | some line => s!" (stdout verdict: '{line.trimAscii.toString}')"
        | none      => ""
      Z3Result.error s!"Z3 wrote to stderr (treated as fatal){verdictHint}{errorLinesInfo}{stderrInfo}"
    else if !errorLines.isEmpty then
      -- Exit 0 but Z3 still reported errors on stdout — malformed query the
      -- solver didn't consider fatal enough to bail on. Fatal-before-verdict;
      -- never collapse into `unknown`.
      Z3Result.error s!"Z3 reported errors in the generated query (exit 0, but stdout had error lines).{errorLinesInfo}{stderrInfo}"
    else
      match verdictLine? with
      | none =>
        Z3Result.error s!"Z3 produced no verdict on stdout{stderrInfo}"
      | some line =>
        let v := line.trimAscii.toString
        match v with
        | "unsat" => Z3Result.unsat
        | "sat"   => Z3Result.sat
        | _ =>
          if v.startsWith "unknown" then
            Z3Result.unknown s!"{v}{stderrInfo}"
          else
            -- Unrecognized verdict (not sat/unsat/unknown). Per policy,
            -- this is an error, NOT a silent fallthrough to unknown.
            Z3Result.error s!"unrecognized Z3 verdict line: '{v}'{stderrInfo}"
  -- Unsat-core parsing: positional — Z3 emits the response on the line
  -- *immediately following* `unsat`, not scanned freely (which would pick up
  -- unrelated s-exprs like `(error: …)` as bogus core names). Shape-check
  -- the candidate so non-cores fail loudly.
  -- `()` is a legitimate response — Z3 derived `unsat` without needing any
  -- `:named` assertion. Since `buildQuery` doesn't `:named`-wrap the negated
  -- goal, an empty core means "no axiom was touched" (e.g. theory reasoning
  -- on the negated goal alone, or unsat via preprocessing). Accept empty,
  -- shape-reject only truly malformed responses.
  let isCoreShape (s : String) : Bool := Id.run do
    let t := s.trimAscii.toString
    if !(t.startsWith "(" && t.endsWith ")") then return false
    let body := ((t.toRawSubstring.drop 1).dropRight 1).toString
    let toks := body.splitOn " " |>.filter (· ≠ "")
    return toks.all fun tok => tok.all fun c => c ≠ ' ' && c ≠ ')'
  let (result, usedAxioms) : Z3Result × Option (Array Name) :=
    match result, parseCores with
    | .unsat, true =>
      let verdictIdx? : Option Nat :=
        allLines.findIdx? fun l => !isErrorLine l && !isBlankLine l
      let coreLine? : Option String :=
        match verdictIdx? with
        | none     => none
        | some idx => (allLines.drop (idx + 1)).find? (fun l => !isBlankLine l)
      match coreLine? with
      | some line =>
        if !isCoreShape line then
          (Z3Result.error s!"Z3 returned 'unsat' but the line immediately following \
            the verdict is not a valid (get-unsat-core) response: \
            '{line.trimAscii.toString}'",
           none)
        else match parseUnsatCore line with
        | .error msg =>
          (Z3Result.error s!"Z3 returned 'unsat' but the (get-unsat-core) line is malformed: {msg}",
           none)
        | .ok parsed =>
          -- An empty `()` core is legitimate: the negated goal isn't
          -- `:named`-wrapped in buildQuery, so when Z3 closes the query
          -- without touching any named axiom (theory contradiction on the
          -- negated goal alone, or preprocessing-time discharge) the core
          -- is empty by construction. Surface it verbatim.
          (.unsat, some parsed)
      | none =>
        (Z3Result.error
          s!"Z3 returned 'unsat' but produced no (get-unsat-core) response. \
            Verbose ? mode requested an unsat core; rerun without ? if you only need the verdict.",
         none)
    | other, _ => (other, none)
  return { result, smtFile := path, usedAxioms }

-- ============================================================
-- Command: z3 / z3? / z3! / z3!? goal_name [only [ax1, ax2, ...]]
--   z3   — expects unsat (axioms are sufficient), errors on sat
--   z3?  — same as z3, verbose (logs SMT path and unsat core)
--   z3!  — expects sat (goal is false or axioms insufficient), errors on unsat
--   z3!? — same as z3!, verbose
-- The axiom set is auto-collected from current-file `ax_<n>` theorems by
-- default, optionally restricted via `only [...]` (mirrors `z3_local`).
-- ============================================================

/-- Pure message construction for Z3 results. `.ok msg` ⇒ info-log; `.error msg` ⇒ throw.
    `goalDesc?` names the goal in messages (used by command-mode `z3_auto` where the
    name disambiguates among many theorems in a file). Tactic-mode callers pass
    `none` — the goal is already visible in the proof state. `refuteHint?` is
    appended only to the `sat`-when-`unsat`-expected branch. -/
def z3ResultMessage (cmdName : String) (goalDesc? : Option MessageData)
    (verbose expectSat : Bool) (output : Z3Output)
    (refuteHint? : Option MessageData := none) :
    Except MessageData MessageData :=
  let forDesc : MessageData :=
    match goalDesc? with
    | some d => m!" for {d}"
    | none   => MessageData.nil
  match output.result, expectSat with
  | .unsat, false =>
    if verbose then .ok m!"Z3 result: unsat (axioms are sufficient{forDesc})"
    else .ok m!"{cmdName}: unsat ✓"
  | .sat, true =>
    if verbose then .ok m!"Z3 result: sat (correctly rejected{forDesc})"
    else .ok m!"{cmdName}: sat ✓"
  | .unsat, true =>
    let pfx := if verbose then "Z3 result" else cmdName
    let subject := match goalDesc? with
      | some d => m!" {d}"
      | none   => m!" the conjecture"
    .error m!"{pfx}: unsat — expected{subject} to be rejected, but Z3 proved it"
  | .sat, false =>
    let hint := refuteHint?.getD MessageData.nil
    if verbose then
      .error m!"Z3 result: sat (axioms are NOT sufficient{forDesc}, or goal is false){hint}"
    else
      .error m!"{cmdName}: sat — axioms are NOT sufficient{forDesc}, or goal is false{hint}"
  | .unknown reason, _ =>
    let body := m!"\nDetails: {reason}\nSMT file: {output.smtFile.toString}"
    if verbose then
      let suffix := if expectSat then " (expected sat)" else ". Try reducing the axiom set"
      .error m!"Z3 result: unknown{forDesc} — Z3 could not decide{suffix}.{body}"
    else
      let suffix := if expectSat then " (expected sat)" else ""
      .error m!"{cmdName}: unknown{forDesc}{suffix}{body}"
  | .error reason, _ =>
    -- Fatal: malformed query, non-zero exit, garbled output. Never report
    -- this as "axioms insufficient" or "could not decide" — that would
    -- mis-attribute a tooling failure to the user's axiom set.
    .error m!"{cmdName}: Z3 invocation failed{forDesc} (query malformed or solver crashed — \
      this is NOT an 'axioms insufficient' result).\nDetails: {reason}\n\
      SMT file: {output.smtFile.toString}"

-- ============================================================
-- Axiom auto-collection helpers (shared by command-mode `z3` and
-- tactic-mode `z3_local`).
-- ============================================================

/-- Gather current-file user theorems suitable for use as axioms. Walks the env,
    filters via `Helpers.isUserTheorem`, drops typeclass instances, trial-translates
    each candidate to SMT, then applies the optional `only [...]` name filter.

    Throws on any translation failure (PLAN_z3_unify.md decision 13):
    every failing axiom is listed with its own underlying message on its
    own indented line, so distinct failure causes are visible without
    iteratively `only`-excluding axioms. `cmdName` is the caller's literal
    token (`"z3"`, `"z3_local"`, …) used as the error prefix. Shared by
    command-mode `z3` (`runZ3Command`) and tactic-mode `z3_local`
    (`z3LocalImpl`). -/
def gatherUserAxioms (cmdName : String) (excludeName : Option Name)
    (filter? : Option (Array Name) := none) : MetaM (Array (Name × Expr)) := do
  let env ← getEnv
  -- Include both `theorem ax_<n>` (Cobb-generated, common) and `axiom ax_<n>`
  -- (hand-written test fixtures) — both are semantic axioms for SMT dispatch.
  let candidates := env.constants.fold (init := #[]) fun acc name cinfo =>
    match cinfo with
    | .thmInfo info | .axiomInfo info =>
      if isUserTheorem env name && excludeName.all (· != name) then
        acc.push (name, info.type)
      else acc
    | _ => acc
  let mut kept : Array (Name × Expr) := #[]
  let mut skipped : Array (Name × String) := #[]
  for (name, ty) in candidates do
    if ← Meta.isInstance name then continue
    let res ← try
      let _ ← (toSmt [] ty : TransM _).run {}
      pure (Except.ok () : Except String Unit)
    catch e =>
      -- Interrupts, max-heartbeat, and max-recDepth are not "this axiom
      -- failed to translate" — they're resource/control-flow exceptions
      -- from outside the translator and must propagate, not get rebranded
      -- as SMT translation bugs.
      rethrowIfFatal e
      pure (Except.error (← e.toMessageData.toString) : Except String Unit)
    match res with
    | .ok _      => kept := kept.push (name, ty)
    | .error msg => skipped := skipped.push (name, msg)
  if !skipped.isEmpty then
    -- Surface every failure; distinct axioms often fail for distinct reasons.
    let lines := skipped.map fun (n, msg) => m!"  - {n}: {msg}"
    let body := MessageData.joinSep lines.toList "\n"
    throwError m!"{cmdName}: failed to translate {skipped.size} axiom(s):\n{body}"
  -- Stable order: env-walk above is hash-bucket-ordered, which leaks
  -- into SMT `(assert)` order and (with quantifier-heavy axioms) into
  -- Z3's e-matching priorities. Sort by name so output is deterministic.
  let keptSorted := kept.qsort fun a b => Name.lt a.1 b.1
  applyAxiomFilter cmdName keptSorted filter?

/-- Post-dispatch verbose log: axiom-count sent, unsat-core summary (if any),
    SMT file path. Shared by command-mode (`runZ3Command`) and tactic-mode
    (`z3LocalImpl`). Pre-dispatch logging (e.g. the full axiom-name list before
    invocation) stays at the call site — it's command-mode-specific. -/
def logVerboseDispatch (cmdName : String) (axiomNames : Array Name)
    (output : Z3Output) : CoreM Unit := do
  let usedDesc := match output.usedAxioms with
    | some used => m!", {used.size} used: {used}"
    | none      => MessageData.nil
  Lean.logInfo m!"{cmdName}: {axiomNames.size} axioms sent{usedDesc}, \
    SMT-LIB query written to {output.smtFile.toString}"

/-- Build the SMT query, run Z3, and optionally log a verbose post-dispatch
    summary. Shared dispatch tail for command-mode (`runZ3Command`) and
    tactic-mode (`z3LocalImpl`); both sites previously hand-rolled this same
    `buildQuery → runZ3 → log` sequence with subtle formatting drift. -/
def dispatchZ3 (cmdName : String) (kept : Array (Name × Expr)) (goal : Expr)
    (verbose : Bool) : MetaM Z3Output := do
  let axiomNames := kept.map (·.1)
  let axiomTypes := kept.map (·.2)
  let query ← buildQuery axiomTypes goal (axiomNames := axiomNames)
    (produceCores := verbose)
  let output ← runZ3 query (parseCores := verbose)
  if verbose then
    logVerboseDispatch cmdName axiomNames output
  return output

/-- Unified command-mode entry point. Auto-collects current-file `ax_<n>`
    theorems (excluding the goal itself), applies the optional name filter,
    dispatches to Z3. Verbose `?` mode requests unsat cores and logs the SMT path. -/
def runZ3Command (cmdName : String) (goalName : Name) (verbose : Bool)
    (filter? : Option (Array Name)) : Lean.Elab.Command.CommandElabM Z3Output := do
  let goalName ← try
    Lean.Elab.Command.liftCoreM <| resolveGlobalConstNoOverloadCore goalName
  catch _ =>
    throwError m!"{cmdName}: goal '{goalName}' not found — is it declared before this {cmdName} command?"
  let goalCi ← Lean.Elab.Command.liftCoreM <| getConstInfo goalName
  -- Only `theorem`/`axiom` have a `.type` that IS the statement to discharge.
  -- For `def foo : Prop := …`, `.type` is `Prop` itself — dispatching on it
  -- would discharge the wrong proposition.
  let goalKind : String := match goalCi with
    | .thmInfo _    => "theorem"
    | .axiomInfo _  => "axiom"
    | .defnInfo _   => "def"
    | .opaqueInfo _ => "opaque"
    | .inductInfo _ => "inductive"
    | .ctorInfo _   => "constructor"
    | .recInfo _    => "recursor"
    | .quotInfo _   => "quot"
  match goalCi with
  | .thmInfo _ | .axiomInfo _ => pure ()
  | _ =>
    throwError m!"{cmdName}: '{goalName}' is a {goalKind}, not a theorem or axiom — \
      {cmdName} dispatches the declaration's stated type, which is only meaningful \
      for theorems and axioms (for a `def foo : Prop := body`, the stated type is `Prop`, \
      not `body`). Restate `{goalName}` as `theorem` or `axiom`."
  let kept ← Lean.Elab.Command.liftTermElabM <|
    gatherUserAxioms cmdName (some goalName) filter?
  if verbose then
    Lean.logInfo m!"{cmdName}: using {kept.size} axioms: {kept.map (·.1)}"
  Lean.Elab.Command.liftTermElabM <|
    dispatchZ3 cmdName kept goalCi.type verbose

end Z3Check

/-! ## Command syntax -/

open Z3Check in
private def reportFromCmd (cmdName : String) (verbose expectSat : Bool)
    (goal : Lean.Ident) (filter? : Option (Array Name)) :
    Lean.Elab.Command.CommandElabM Unit := do
  let gn := goal.getId
  let output ← runZ3Command cmdName gn verbose filter?
  let refuteHint : MessageData :=
    m!"\nHint: the goal may be genuinely refutable — try `propose_counterexample {gn}` at a `sorry` site."
  dispatchExceptMsg
    (Z3Check.z3ResultMessage cmdName (some m!"'{gn}'") verbose expectSat output (some refuteHint))

-- Four prefix tokens; suffix `!` ⇒ expectSat, `?` ⇒ verbose. The token must
-- stay glued (`z3?`, not `z3 ?`) because Lean's lexer would otherwise mis-tokenize.
syntax "z3"   ident ("only" "[" ident,* "]")? : command
syntax "z3?"  ident ("only" "[" ident,* "]")? : command
syntax "z3!"  ident ("only" "[" ident,* "]")? : command
syntax "z3!?" ident ("only" "[" ident,* "]")? : command

private def elabZ3 (cmdName : String) (verbose expectSat : Bool) (g : Lean.Ident)
    (a? : Option (Lean.Syntax.TSepArray `ident ",")) :
    Lean.Elab.Command.CommandElabM Unit :=
  reportFromCmd cmdName verbose expectSat g (a?.map fun arr => arr.getElems.map (·.getId))

elab_rules : command
  | `(command| z3   $g $[only [$a,*]]?) => elabZ3 "z3"   false false g a
  | `(command| z3?  $g $[only [$a,*]]?) => elabZ3 "z3?"  true  false g a
  | `(command| z3!  $g $[only [$a,*]]?) => elabZ3 "z3!"  false true  g a
  | `(command| z3!? $g $[only [$a,*]]?) => elabZ3 "z3!?" true  true  g a
