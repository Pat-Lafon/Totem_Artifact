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
    -- Substitute simple equalities (fvar = simple or simple = fvar). "Simple"
    -- excludes unapplied user functions: `subst` is sound on `x = my_fn`, but
    -- it inlines `my_fn` everywhere `x` appeared and the resulting goal is
    -- usually harder for downstream `grind`. Restrict the const branch to
    -- constructor heads (zero-arg ctors like `Nat.zero`, `Nil`, `true`).
    let env ← getEnv
    let isSimple (e : Expr) : Bool := e.isFVar || e.isLit || isCtorApp env e
    if (lhs.isFVar && isSimple rhs) || (rhs.isFVar && isSimple lhs) then
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
-- AND applied to a ctor-headed arg (so iota fires after the unfold).
-- Heuristic: ctor-headed check is positional-agnostic.
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
        else isNonRecursiveDef env n && args.any (isCtorApp env)
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

private def trySimp (d : LocalDecl) (ty : Expr) : TacticM Bool := do
  let toUnfold := (← Lean.Meta.getSimpTheorems).toUnfold
  if !safeForSimp (← getEnv) toUnfold ty then return false
  let hi := mkIdent d.userName
  let loc ← `(Lean.Parser.Tactic.locationHyp| $hi:ident)
  tryTacticStep (evalTactic (← `(tactic| simp at $loc)))

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

/-! ## Public entry points -/

def simpHypsOnce : TacticM Bool := withMainContext do
  if ← tryCloseByContradiction then return true
  let lctx ← getLCtx
  let phases : Array (LocalDecl → Expr → TacticM Bool) :=
    #[tryDestruct, trySpecialize lctx, tryNormalize, trySimp, tryClearTrivial]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    for phase in phases do
      if ← phase d ty then return true
  return false

partial def simpHypsLoop : TacticM Unit := do
  if (← getGoals).isEmpty then return
  if ← simpHypsOnce then simpHypsLoop
