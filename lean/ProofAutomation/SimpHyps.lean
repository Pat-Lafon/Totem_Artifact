import Lean
import ProofAutomation.Helpers

open Lean Elab Tactic Meta

/-! # SimpHyps — iteratively simplify hypotheses -/

-- Try to prove a type in an empty context. Returns true only if `tac` fully
-- discharges the goal — `simp` succeeds without throwing even when it merely
-- simplifies, so checking `getGoals.isEmpty` is required to avoid false positives.
private def provableInEmptyCtx (ty : Expr) (tac : TacticM Unit) : TacticM Bool := do
  let gs ← getGoals
  try
    let goal ← withLCtx {} {} <| mkFreshExprMVar (some ty)
    setGoals [goal.mvarId!]
    tac
    let solved := (← getGoals).isEmpty
    setGoals gs; pure solved
  catch e => rethrowIfFatal e; setGoals gs; pure false

/-! ## Steps: each operates on a single hypothesis -/

private def tryDestruct (d : LocalDecl) (ty : Expr) : TacticM Bool := do
  let shouldDestruct := match_expr ty with
    | And _ _ => true | Exists _ _ => true | Iff _ _ => true | _ => false
  if shouldDestruct then
    destructCore d.userName; return true
  return false

private def trySpecialize (lctx : LocalContext) (d : LocalDecl) (ty : Expr) : TacticM Bool := do
  let .forallE _ domain _ .default := ty | return false
  let hi := mkIdent d.userName

  -- Premise is trivially provable → specialize with the proof
  let premiseProof? ← try
    let goal ← mkFreshExprMVar (some domain)
    let gs ← getGoals; setGoals [goal.mvarId!]
    evalTactic (← `(tactic| first | rfl | trivial | decide | grind))
    setGoals gs; pure (some goal)
  catch e => rethrowIfFatal e; pure none
  if let some proof := premiseProof? then
    if ← tryTacticStep do
        let newProof := mkApp (mkFVar d.fvarId) proof
        let newType ← inferType newProof
        -- Use a throwaway name for `note` (the old hyp still occupies d.userName);
        -- after clearing the old fvar, rename the new one back to d.userName.
        -- Without this, repeated specializations cascade names like h_20 →
        -- h_20_42 → h_20_42_44.
        let tempName ← freshAccessibleName `_simp_hyps_tmp
        let goal ← getMainGoal
        let (newFvar, goal) ← goal.note tempName newProof newType
        let goal ← goal.clear d.fvarId
        let goal ← goal.rename newFvar d.userName
        replaceMainGoal [goal] then
      return true

  -- Premise is provably false → clear
  let premiseFalse ← try
    let negDomain ← mkAppM ``Not #[domain]
    let goal ← mkFreshExprMVar (some negDomain)
    let gs ← getGoals; setGoals [goal.mvarId!]
    evalTactic (← `(tactic| first | trivial | decide | grind))
    setGoals gs; pure true
  catch e => rethrowIfFatal e; pure false
  if premiseFalse then
    if ← tryTacticStep (evalTactic (← `(tactic| clear $hi))) then return true

  -- Match premise against existing hypothesis → specialize.
  -- Multiple specCandidates are flagged loudly: silently picking the first one in
  -- declaration order makes downstream failures hard to trace back here.
  let mut specCandidates : Array Name := #[]
  for d' in lctx do
    if d'.fvarId == d.fvarId || d'.isImplementationDetail then continue
    if ← withNewMCtxDepth (isDefEq domain (← instantiateMVars d'.type)) then
      specCandidates := specCandidates.push d'.userName
  if specCandidates.size > 1 then
    throwError "simp_hyps: hypothesis '{d.userName} : {ty}' has multiple specialization \
      candidates for its premise: {specCandidates}. Disambiguate with an explicit `specialize` \
      before running `simp_hyps`."
  if h : specCandidates.size = 1 then
    if ← tryTacticStep (evalTactic (← `(tactic| specialize ($hi $(mkIdent specCandidates[0]))))) then
      return true

  -- Hypothesis of form (P → False) where P specCandidates another hyp → clear
  let domainWhnf ← whnf domain
  if let .forallE _ p body .default := domainWhnf then
    if (← whnf body).isConstOf ``False then
      for d' in lctx do
        if d'.fvarId == d.fvarId || d'.isImplementationDetail then continue
        if ← withNewMCtxDepth (isDefEq p (← instantiateMVars d'.type)) then
          if ← tryTacticStep (evalTactic (← `(tactic| clear $hi))) then return true

  -- Another hypothesis is (domain → False) → clear this one
  for d' in lctx do
    if d'.fvarId == d.fvarId || d'.isImplementationDetail then continue
    let ty'Whnf ← whnf (← instantiateMVars d'.type)
    if let .forallE _ p body .default := ty'Whnf then
      if (← whnf body).isConstOf ``False then
        if ← withNewMCtxDepth (isDefEq p domain) then
          if ← tryTacticStep (evalTactic (← `(tactic| clear $hi))) then return true

  return false

-- True iff `e` (after `getAppFn`) is a constructor of some inductive.
private def isCtorApp (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => match env.find? n with
    | some (.ctorInfo _) => true
    | _ => false
  | _ => false

-- Strip outer lambdas, returning the inner body and the number stripped.
private partial def stripOuterLambdas : Expr → Nat → Expr × Nat
  | .lam _ _ body _, k => stripOuterLambdas body (k + 1)
  | e, k => (e, k)

/-! `paramScrutPositions n`: param positions of def `n` (0-indexed from
the outermost lambda) whose values flow into a matcher scrutinee — either
directly via a matcher app in `n`'s body, or transitively via a call to
another `toUnfold` def whose body matches on the corresponding arg.
Unfolding `n` applied to args produces a stuck matcher whenever any of
these positions is non-ctor at the call site. Lambda/forall bodies are
skipped: bvar indices inside those binders refer to fresh binders rather
than the def's params, so static back-mapping isn't sound. -/

mutual

private partial def paramScrutPositionsAux
    (env : Environment) (toUnfold : PHashSet Name)
    (visited : Std.HashSet Name) (n : Name) : Std.HashSet Nat :=
  if visited.contains n then {} else
    let visited := visited.insert n
    match env.find? n with
    | some (.defnInfo ci) =>
      let (inner, numLams) := stripOuterLambdas ci.value 0
      collectScrutPositions env toUnfold visited numLams inner {}
    | _ => {}

private partial def collectScrutPositions
    (env : Environment) (toUnfold : PHashSet Name) (visited : Std.HashSet Name)
    (numLams : Nat) (e : Expr) (acc : Std.HashSet Nat) :
    Std.HashSet Nat := Id.run do
  let mut acc := acc
  if e.isApp then
    let head := e.getAppFn
    let args := e.getAppArgs
    if let .const m _ := head then
      -- Direct matcher app: pick up scrutinees pointing at outer params.
      if let some mInfo := getMatcherInfoCore? env m then
        let lo := mInfo.getFirstDiscrPos
        let hi := lo + mInfo.numDiscrs
        if args.size ≥ hi then
          for i in [lo:hi] do
            if let .bvar j := args[i]! then
              if j < numLams then
                acc := acc.insert (numLams - 1 - j)
      -- Transitive call to another toUnfold def: pull its scrut-prone
      -- positions back to the enclosing def's param positions.
      if toUnfold.contains m then
        let inner := paramScrutPositionsAux env toUnfold visited m
        for q in inner do
          if h : q < args.size then
            if let .bvar j := args[q] then
              if j < numLams then
                acc := acc.insert (numLams - 1 - j)
    for arg in args do
      acc := collectScrutPositions env toUnfold visited numLams arg acc
    return acc
  match e with
  | .letE _ ty val body _ =>
    acc := collectScrutPositions env toUnfold visited numLams ty acc
    acc := collectScrutPositions env toUnfold visited numLams val acc
    acc := collectScrutPositions env toUnfold visited numLams body acc
    return acc
  | .mdata _ inner =>
    acc := collectScrutPositions env toUnfold visited numLams inner acc
    return acc
  | .proj _ _ inner =>
    acc := collectScrutPositions env toUnfold visited numLams inner acc
    return acc
  | _ => return acc

end

private def paramScrutPositions
    (env : Environment) (toUnfold : PHashSet Name) (n : Name) : Std.HashSet Nat :=
  paramScrutPositionsAux env toUnfold {} n

private def tryNormalize (d : LocalDecl) (ty : Expr) : TacticM Bool := do
  let hi := mkIdent d.userName
  -- Normalize BEq: `(x == y) = true/false` or `true/false = (x == y)` → `x = y` / `x ≠ y`
  if (isBEqEq ty).isSome then
    let loc ← `(Lean.Parser.Tactic.locationHyp| $hi:ident)
    if ← tryTacticStep (evalTactic (← `(tactic| simp only [eq_comm (a := true), eq_comm (a := false),
        beq_iff_eq, beq_eq_false_iff_ne, decide_eq_true_eq] at $loc))) then
      return true
  match_expr ty with
  | Eq _ lhs rhs =>
    -- Substitute equalities with an fvar on one side. The gate is asymmetric
    -- by direction, keyed off Cobb's encoding convention:
    --
    --   * Inner numbered fvars appear on the *LHS* of `==`
    --       e.g. `s_2 == (s - 1)`, `inv_1 == (inv - 1)`, `h_0 == (h - 1)`.
    --     These BEq-normalize to `inner = arith`, and we want subst to
    --     eliminate the inner var. So `fvar = expr` admits applications
    --     (arithmetic, function apps).
    --
    --   * Outer user-quantified fvars appear on the *RHS* of `==`
    --       e.g. `(h + h) == inv`, `((h + h) + 1) == inv`.
    --     These BEq-normalize to `arith = outer`, and we must NOT subst —
    --     eliminating `inv` from the lctx breaks downstream `suffices`/
    --     `refine` blocks that reference it by name. So `expr = fvar`
    --     keeps the strict gate (only literals/constructors on LHS).
    --
    -- Both directions still exclude bare unapplied user consts: `x = my_fn`
    -- would inline `my_fn` everywhere `x` appeared and confuse downstream
    -- `grind`. `e.isApp` allows `f a b` but not `f` alone.
    let env ← getEnv
    let isOfNatApp (e : Expr) : Bool :=
      match e.getAppFn with
      | .const ``OfNat.ofNat _ => true
      | _ => false
    let isNumLit (e : Expr) : Bool :=
      isOfNatApp e ||
        (match e.getAppFn with
         | .const ``Neg.neg _ =>
           let args := e.getAppArgs
           args.size ≥ 3 && isOfNatApp args[2]!
         | _ => false)
    let isSimpleStrict (e : Expr) : Bool :=
      e.isFVar || e.isLit || isNumLit e || isCtorApp env e
    let isSimpleLoose (e : Expr) : Bool :=
      isSimpleStrict e || e.isApp
    if (lhs.isFVar && isSimpleLoose rhs) || (rhs.isFVar && isSimpleStrict lhs) then
      if ← tryTacticStep (evalTactic (← `(tactic| subst $hi))) then return true
  | _ => pure ()
  return false

-- Logical/Bool connectives — always admit; fast path before the env lookup.
private def pureBoolWhitelist : NameSet :=
  NameSet.empty
    |>.insert ``Eq |>.insert ``Ne |>.insert ``HEq
    |>.insert ``And |>.insert ``Or |>.insert ``Not |>.insert ``Iff
    |>.insert ``True |>.insert ``False
    |>.insert ``Bool |>.insert ``Bool.true |>.insert ``Bool.false

-- Reject recursive defs: one unfold step on `f (Ctor _)` re-exposes `f` on
-- subterms and leaves messy residue. Structural/well-founded recursion is
-- compiled away from the const name, so we also check for the elaborated
-- markers (`brecOn`/`binductionOn`/`WellFounded.fix`/`_unsafe_rec`).
private def isNonRecursiveDef (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo ci) =>
    let tainted := ci.value.find? fun
      | .const m _ =>
        ci.all.contains m
        || m == ``WellFounded.fix
        || (match m with
            | .str _ s => s == "brecOn" || s == "binductionOn" || s == "_unsafe_rec"
            | _ => false)
      | _ => false
    tainted.isNone
  | _ => false

-- Admit a hypothesis only when every `toUnfold` const in it is non-recursive
-- AND every param position whose value would flow into a (possibly
-- transitive) matcher scrutinee is ctor-headed at the call site. Without
-- the transitive check, simp can cascade through a wrapper def into a
-- matcher-bearing helper and leave a stuck `match v, _ with ...` residue.
private partial def safeForSimp
    (env : Environment) (toUnfold : PHashSet Name) (e : Expr) : Bool :=
  match e with
  | .app .. =>
    let head := e.getAppFn
    let args := e.getAppArgs
    let okHead : Bool := match head with
      | .const n _ =>
        if pureBoolWhitelist.contains n then true
        else if !toUnfold.contains n then true
        else
          isNonRecursiveDef env n &&
            (paramScrutPositions env toUnfold n).toList.all fun i =>
              i < args.size && isCtorApp env args[i]!
      | _ => true
    okHead && args.all (safeForSimp env toUnfold)
  | .forallE _ ty body _ =>
    safeForSimp env toUnfold ty && safeForSimp env toUnfold body
  | .lam _ ty body _ =>
    safeForSimp env toUnfold ty && safeForSimp env toUnfold body
  | .letE _ ty val body _ =>
    safeForSimp env toUnfold ty && safeForSimp env toUnfold val
      && safeForSimp env toUnfold body
  | .mdata _ inner => safeForSimp env toUnfold inner
  | .proj _ _ inner => safeForSimp env toUnfold inner
  | .const n _ =>
    -- Nullary: unfolds to a closed term, no match-on-fvar risk.
    if pureBoolWhitelist.contains n then true
    else if !toUnfold.contains n then true
    else isNonRecursiveDef env n
  | _ => true

-- Resolve an `ite` inside a hypothesis when the condition is discharged by
-- the current lctx. Finds the first `ite c _ _ _ _` subterm and tries
-- `simp only [if_pos (by …)]`/`[if_neg (by …)]` against `h`, where the
-- inner tactic is `assumption | omega | decide`. `simp only` fails cheaply
-- on "no progress" when the probe can't close, so we don't pre-filter.
private def tryIteResolve (d : LocalDecl) (ty : Expr) : TacticM Bool := do
  let some iteExpr := ty.find? (·.isAppOfArity ``ite 5) | return false
  let cond := iteExpr.getAppArgs[1]!
  let hi := mkIdent d.userName
  let condStx ← Term.exprToSyntax cond
  if ← tryTacticStep (evalTactic (← `(tactic|
      simp only [if_pos (show $condStx by first | assumption | omega | decide)] at $hi:ident))) then
    return true
  if ← tryTacticStep (evalTactic (← `(tactic|
      simp only [if_neg (show ¬ $condStx by first | assumption | omega | decide)] at $hi:ident))) then
    return true
  return false

private def trySimp (d : LocalDecl) (ty : Expr) : TacticM Bool := do
  let toUnfold := (← Lean.Meta.getSimpTheorems).toUnfold
  let hi := mkIdent d.userName
  let loc ← `(Lean.Parser.Tactic.locationHyp| $hi:ident)
  if safeForSimp (← getEnv) toUnfold ty then
    tryTacticStep (evalTactic (← `(tactic| simp at $loc)))
  else
    -- Narrow logical-only fallback when `safeForSimp` gates off the full
    -- `simp at`. No def unfolds, so no stuck-matcher residue is possible.
    tryTacticStep (evalTactic (← `(tactic|
      simp only [true_and, false_and, and_true, and_false,
                 true_or, false_or, or_true, or_false,
                 not_true, not_false, reduceCtorEq] at $loc)))

-- Bail early if the lctx already contradicts itself: `False` hypothesis,
-- `P` + `¬P`, or disjoint-constructor equalities. Stops the rest of
-- `simpHypsOnce` from grinding through a doomed goal.
private def tryCloseByContradiction : TacticM Bool := do
  let gs ← getGoals
  try
    evalTactic (← `(tactic| contradiction))
    pure (← getGoals).isEmpty
  catch e =>
    rethrowIfFatal e; setGoals gs; pure false

private def tryClearTrivial (d : LocalDecl) (ty : Expr) : TacticM Bool := do
  let hi := mkIdent d.userName
  -- Clear True
  if ty.isConstOf ``True then
    if ← tryTacticStep (evalTactic (← `(tactic| clear $hi))) then return true
  -- Ground hypotheses only from here
  if !(Lean.collectFVars {} ty).fvarSet.isEmpty then return false
  -- Clear if hypothesis is a tautology
  if ← provableInEmptyCtx ty (evalTactic (← `(tactic| first | omega | decide | simp))) then
    if ← tryTacticStep (evalTactic (← `(tactic| clear $hi))) then return true
  return false

-- Recognize a hypothesis type that looks like linear arithmetic over `Int`/
-- `Nat`. Head must be `LE.le`/`LT.lt`/`GE.ge`/`GT.gt`/`Eq`, with the operand
-- type a numeric type that `grind`/`omega` can reason about. Gates
-- `tryClearRedundant` so we only run the (expensive) probe on hypotheses
-- where redundancy via arithmetic is actually plausible — running it on every
-- hyp blows the outer simp_hyps heartbeat budget on large rbtree lctxs.
private def isArithProp (ty : Expr) : Bool :=
  let isNumericTy (t : Expr) : Bool := match t with
    | .const ``Int _ | .const ``Nat _ => true
    | _ => false
  match_expr ty with
  | LE.le t _ _ _ => isNumericTy t
  | LT.lt t _ _ _ => isNumericTy t
  | GE.ge t _ _ _ => isNumericTy t
  | GT.gt t _ _ _ => isNumericTy t
  | Eq t _ _ => isNumericTy t
  | _ => false

-- Clear a hypothesis if it follows from the rest of the local context. Probe:
-- build a fresh goal of type `ty` in a copy of the current lctx with `d`
-- removed, then try `grind`. If grind closes it, `d` is redundant and we drop
-- it from the main goal. Catches cases like `0 ≤ h - 1 + (h - 1) + 1` that
-- follow from a sibling `h > 0` but aren't tautologies in isolation (so
-- `tryClearTrivial`'s empty-context probe can't see them).
--
-- Gated to arithmetic-shaped types: the probe is too expensive to run on every
-- hypothesis (rbtree-shaped lctxs blow the outer heartbeat budget), and
-- arithmetic is where this kind of derivable-from-siblings redundancy
-- actually shows up in practice.
private def tryClearRedundant (d : LocalDecl) (ty : Expr) : TacticM Bool := do
  if !isArithProp ty then return false
  let hi := mkIdent d.userName
  let provable ← withMainContext do
    let gs ← getGoals
    let probeId? ← try
      let probe ← mkFreshExprMVar (some ty)
      pure (some (← probe.mvarId!.clear d.fvarId))
    catch e => rethrowIfFatal e; pure none
    match probeId? with
    | none => pure false
    | some probeId =>
      setGoals [probeId]
      let ok ← try
        withCurrHeartbeats <|
          evalTactic (← `(tactic| set_option maxHeartbeats 4000 in grind))
        pure true
      catch e =>
        if e.isInterrupt || e.isMaxRecDepth then throw e
        pure false
      let solved := ok && (← getGoals).isEmpty
      setGoals gs
      pure solved
  if provable then
    return ← tryTacticStep (evalTactic (← `(tactic| clear $hi)))
  return false

/-! ## Public entry points -/

def simpHypsOnce : TacticM Bool := withMainContext do
  if ← tryCloseByContradiction then return true
  let lctx ← getLCtx
  let phases : Array (LocalDecl → Expr → TacticM Bool) :=
    #[tryDestruct, trySpecialize lctx, tryNormalize, trySimp, tryIteResolve,
      tryClearTrivial, tryClearRedundant]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    for phase in phases do
      if ← phase d ty then return true
  return false

partial def simpHypsLoop : TacticM Unit := do
  if (← getGoals).isEmpty then return
  if ← simpHypsOnce then simpHypsLoop
