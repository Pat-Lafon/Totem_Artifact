import Lean
import ProofAutomation.Helpers

open Lean Elab Tactic Meta

/-! # SearchAxioms — find applicable axioms via unification

  Modes:
    search_axioms          -- both directions (default)
    search_axioms goal     -- backward only: axiom conclusion unifies with goal
    search_axioms hyps     -- forward only: any premise unifies with any hypothesis
    search_axioms h        -- forward, anchored on `h`: some premise must unify with `h`

  Both directions share the same premise-classification pipeline
  (`classifyPremises` → `propagateMissing` → `binderPinningSweep` →
  `reclassifyMissing`) so the goal mode benefits from the same
  simp + bool-eq unification, lctx `isDefEq` matching, and binder
  pinning that the forward mode uses. -/

inductive SearchMode where
  | all
  | goalOnly
  | hypsOnly
  | hypOnly (anchor : Name)
  deriving Inhabited

/-! ## Theorem collection -/

private def collectFileTheorems (env : Environment) :
    Array (Name × ConstantInfo) :=
  env.constants.fold (init := #[]) fun acc name cinfo =>
    match cinfo with
    | .thmInfo _ =>
      if isUserTheorem env name then acc.push (name, cinfo) else acc
    | _ => acc

/-! ## Slot type and lctx scanning -/

/-- One premise slot of an axiom, classified by how search filled it.
    In backward mode, slots correspond to the axiom premises that remain
    after the conclusion has been unified with the goal. -/
private inductive PremiseSlot where
  /-- Filled by a hypothesis from the local context. -/
  | hyp (n : Name) (ty : Expr)
  /-- Auto-discharged: the premise reduces to `True` once binder mvars
      are pinned. Rendered as `(by grind)` for paste-ready output —
      relying on Lean's elaborator to repeat the reduction is fragile. -/
  | discharged (ty : Expr)
  /-- Couldn't match a hypothesis or reduce to `True`/`False`. Rendered
      as `(by grind)` with a comment showing the residual goal. -/
  | missing (ty : Expr)

/-- Scan the local context for a hypothesis whose (instantiated) type is
    definitionally equal to `target`. Used by both modes — much looser
    than `assumption` because it tolerates simp-unfolding of `def`-wrapped
    predicates and propagates metavar pins via `isDefEq`. -/
private def findMatchingHypIn (lctx : LocalContext) (skip : Option Name) (target : Expr) :
    TacticM (Option (Name × Expr)) := do
  for d in lctx do
    if d.isImplementationDetail then continue
    if skip = some d.userName then continue
    let dTy ← instantiateMVars d.type
    if ← try isDefEq target dTy catch e => do rethrowIfFatal e; pure false then
      return some (d.userName, dTy)
  return none

/-! ## Axiom decomposition and normalization -/

/-- Decompose an axiom type into (binders, premises, conclusion). Walks the
    outer ∀/→ in source order via `classifyForall?`: each dependent binder
    becomes a fresh metavar (substituted into the body and pushed onto
    `binders`); each non-dependent arrow contributes its source type to
    `premises`. Binders and premises may interleave. Premises and binders
    share metavars, so unifying premises against the local context pins
    binder values. -/
private def decomposeAxiom (ty : Expr) :
    MetaM (Array Expr × Array Expr × Expr) := do
  let mut cur := ty
  let mut binders : Array Expr := #[]
  let mut premises : Array Expr := #[]
  repeat
    let cur' ← whnf cur
    match classifyForall? cur' with
    | some (.binder n bty, body) =>
      let mvar ← mkFreshExprMVar (some bty) (userName := n)
      binders := binders.push mvar
      cur := body.instantiate1 mvar
    | some (.premise bty, body) =>
      premises := premises.push bty
      cur := body
    | none => break
  return (binders, premises, cur)

/-- Simp-reduce `e` using the global simp set. Metavar unifications that occur
    during simp's pattern matching are preserved — e.g. when a bool-eq simp
    lemma like `(a == b) = true ↔ a = b` fires, the surrounding metavar gets
    pinned. Returns the original expression unchanged if simp throws. -/
private def simpReduce (e : Expr) : MetaM Expr := do
  try
    let ctx ← Simp.mkContext
      (config := { decide := true })
      (simpTheorems := #[← getSimpTheorems])
      (congrTheorems := ← getSimpCongrTheorems)
    let (r, _) ← Simp.main e ctx
    return r.expr
  catch ex =>
    rethrowIfFatal ex
    return e

/-- For each conjunct of form `(a == b) = true` in `e`, try `isDefEq a b` to
    propagate metavar unifications. The Cobb-Totem axioms encode equalities
    via `BEq.beq` (i.e. `==`) and `Eq Bool _ Bool.true`, which simp's stock
    `LawfulBEq` lemmas don't always rewrite to the bare `Eq` form needed for
    automatic unification. This walks `And`-spines and surfaces those
    equalities directly to `isDefEq`. -/
private partial def unifyBoolEqs (e : Expr) : MetaM Unit := do
  match_expr e with
  | And p q => unifyBoolEqs p; unifyBoolEqs q
  | _ =>
    if let some (true, a, b) := isBEqEq e then
      let _ ← try isDefEq a b catch ex => do rethrowIfFatal ex; pure false

/-- Decide whether a forward-derived `concl` is uninformative — either a
    tautology (reduces to True, e.g. `0 ≥ 0`) or `isDefEq` to a hypothesis
    already in scope. Restores meta state before returning. -/
private def conclusionIsRedundant (concl : Expr) (lctx : LocalContext) :
    MetaM Bool := do
  if (← reducedExpr concl) == some true then return true
  withoutModifyingState do
    for d in lctx do
      if d.isImplementationDetail then continue
      let dTy ← instantiateMVars d.type
      if ← try isDefEq concl dTy catch e => do rethrowIfFatal e; pure false then
        return true
    return false

/-! ## Shared classification pipeline

  Both backward and forward modes funnel premises through this four-step
  pipeline. The only difference is the entry condition (forward picks an
  anchor premise / requires at least one premise; backward unifies the
  conclusion against the goal first). -/

/-- First-pass classification: for each premise, try direct match, then
    simp + bool-eq unification + retry. Reduces to False ⇒ axiom inapplicable. -/
private def classifyPremises (premises : Array Expr) (lctx : LocalContext)
    (skipHyp : Option Name) (anchoredAt : Option Nat) (anchor : Option (Name × Expr)) :
    TacticM (Option (Array PremiseSlot)) := do
  let mut slots : Array PremiseSlot := #[]
  for i in [:premises.size] do
    let pInst ← instantiateMVars premises[i]!
    if anchoredAt = some i then
      if let some (hn, hty) := anchor then
        slots := slots.push (.hyp hn hty)
      continue
    if let some (hn, hty) ← findMatchingHypIn lctx skipHyp pInst then
      slots := slots.push (.hyp hn hty)
      continue
    -- Simp-reduce + bool-eq unify. Propagates constraints from structural
    -- premises like `(some c' == some ?c) = true` into surrounding metavars,
    -- so by the polarity premise (`¬c = true`), `?c` is pinned to `c'`.
    let pInstFinal ← instantiateMVars premises[i]!
    let pSimped ← simpReduce pInstFinal
    unifyBoolEqs pSimped
    let pSimpedI ← instantiateMVars pSimped
    if let some (hn, hty) ← findMatchingHypIn lctx skipHyp pSimpedI then
      slots := slots.push (.hyp hn hty)
      continue
    -- For display, prefer the original premise shape (mvars now pinned
    -- by unifyBoolEqs) over the simp-unfolded form.
    let pDisplay ← instantiateMVars pInstFinal
    match ← reducedExpr pSimpedI with
    | some false => return none
    | some true => slots := slots.push (.discharged pDisplay)
    | none => slots := slots.push (.missing pDisplay)
  return some slots

/-- Second-pass propagation: the first classification walks premises in
    source order, so a premise whose mvars are pinned only by a *later*
    premise (e.g. ax_17's premise 0 references `r`, which premise 3 pins)
    stays `.missing` even after the structural premise resolves. Re-run
    simp + unifyBoolEqs on each `.missing` slot now that all earlier
    premises have committed their pinnings. Done outside saveState so
    the unifications persist into the final result. -/
private def propagateMissing (slots : Array PremiseSlot) : TacticM Unit := do
  for s in slots do
    match s with
    | .missing m =>
      let mI ← instantiateMVars m
      let mSimped ← simpReduce mI
      unifyBoolEqs mSimped
    | _ => pure ()

/-- Score the slot array under the current metavar assignment. Used by the
    binder-pinning sweep to compare candidate fvar assignments. Returns
    none if any premise reduces to False under this assignment. Wrap in
    saveState/restoreState if you don't want simp's incidental mvar pins
    to leak — `binderPinningSweep` does so. -/
private def scoreSlots (slots : Array PremiseSlot) (lctx : LocalContext)
    (skipHyp : Option Name) : TacticM (Option Int) := do
  let mut score : Int := 0
  for s in slots do
    match s with
    | .hyp _ _ => score := score + 2
    | .discharged _ => score := score + 1
    | .missing m =>
      let mI ← instantiateMVars m
      let mSimped ← simpReduce mI
      unifyBoolEqs mSimped
      let mSimpedI ← instantiateMVars mSimped
      match ← reducedExpr mSimpedI with
      | some true => score := score + 1
      | some false => return none
      | none =>
        if let some _ ← findMatchingHypIn lctx skipHyp mSimpedI then score := score + 2
  return some score

/-- Try to pin still-unbound binder mvars by enumerating compatible
    fvars from the local context. Commit an assignment only when it
    strictly raises slot quality (more `.hyp`/`.discharged` slots, and
    no premise reducing to False). Greedy left-to-right: a later binder
    sees the pinnings made by earlier ones. -/
private def binderPinningSweep (binders : Array Expr) (slots : Array PremiseSlot)
    (lctx : LocalContext) (skipHyp : Option Name) : TacticM Unit := do
  let baseScoreOpt ← withoutModifyingState <| scoreSlots slots lctx skipHyp
  let some baseScore := baseScoreOpt | return ()
  let mut runningBase : Int := baseScore
  for b in binders do
    let bI ← instantiateMVars b
    if !bI.isMVar then continue
    let bTy ← inferType bI
    let mut best : Option (Expr × Int) := none
    for d in lctx do
      if d.isImplementationDetail then continue
      let dTy ← instantiateMVars d.type
      let sc? ← withoutModifyingState do
        let assigned ←
          try
            if ← isDefEq dTy bTy then isDefEq bI d.toExpr else pure false
          catch e => rethrowIfFatal e; pure false
        if assigned then scoreSlots slots lctx skipHyp else pure none
      if let some s := sc? then
        if s > runningBase then
          match best with
          | none => best := some (d.toExpr, s)
          | some (_, prev) => if s > prev then best := some (d.toExpr, s)
    if let some (v, sBest) := best then
      let _ ← try isDefEq bI v catch e => do rethrowIfFatal e; pure false
      runningBase := sBest

/-- Final reclassification after propagation + binder pinning. Metavars
    pinned by later premises or the binder sweep may now reduce a
    previously-missing premise to True/False or make it structurally
    match a hypothesis. -/
private def reclassifyMissing (slots : Array PremiseSlot) (lctx : LocalContext)
    (skipHyp : Option Name) : TacticM (Option (Array PremiseSlot)) := do
  let mut finalSlots : Array PremiseSlot := #[]
  for s in slots do
    match s with
    | .missing m =>
      let mI ← instantiateMVars m
      match ← reducedExpr mI with
      | some false => return none
      | some true => finalSlots := finalSlots.push (.discharged mI)
      | none =>
        if let some (hn, hty) ← findMatchingHypIn lctx skipHyp mI then
          finalSlots := finalSlots.push (.hyp hn hty)
        else
          finalSlots := finalSlots.push (.missing mI)
    | other => finalSlots := finalSlots.push other
  return some finalSlots

/-! ## Unified match result -/

private inductive MatchMode where
  | forward
  | backward

private structure AxiomMatch where
  name       : Name
  binders    : Array Expr
  slots      : Array PremiseSlot
  conclusion : Expr
  ty         : Expr
  mode       : MatchMode

private def slotsComplete (slots : Array PremiseSlot) : Bool :=
  !slots.any fun | .missing _ => true | _ => false

/-! ## Backward (goal) mode

  Symmetric with `tryForward`: decompose the axiom, unify its conclusion
  against the goal type, then run the shared classification pipeline on
  the remaining premises. -/

private def tryGoalMatch (goalType : Expr) (name : Name) (ci : ConstantInfo)
    (lctx : LocalContext) : TacticM (Option AxiomMatch) := do
  try
    withNewMCtxDepth do
      let (binders, premises, conclusion) ← decomposeAxiom ci.type
      let unified ←
        try isDefEq conclusion goalType
        catch e => do rethrowIfFatal e; pure false
      if !unified then return none
      let some slots ← classifyPremises premises lctx none none none | return none
      propagateMissing slots
      binderPinningSweep binders slots lctx none
      let some finalSlots ← reclassifyMissing slots lctx none | return none
      let conclI ← instantiateMVars conclusion
      let binderArgs ← binders.mapM instantiateMVars
      return some { name, binders := binderArgs, slots := finalSlots,
                    conclusion := conclI, ty := ci.type, mode := .backward }
  catch e => rethrowIfFatal e; return none

/-! ## Forward (hypothesis) mode -/

/-- Try to instantiate `name`'s premises from the local context.
    If `anchor` is given, require that some premise unifies with the anchor's type;
    that premise is bound to the anchor before any other premise is matched. -/
private def tryForward (name : Name) (ci : ConstantInfo) (lctx : LocalContext)
    (anchor : Option (Name × Expr)) : TacticM (Option AxiomMatch) := do
  withNewMCtxDepth do
    let (binders, premises, conclusion) ← decomposeAxiom ci.type
    if premises.isEmpty then return none

    -- Lock the anchor in first if requested: pick the lowest-index premise that
    -- unifies with the anchor's type. This may constrain shared metavars.
    let mut anchoredAt : Option Nat := none
    if let some (_, anchorTy) := anchor then
      let mut found : Option Nat := none
      for i in [:premises.size] do
        let pInst ← instantiateMVars premises[i]!
        if ← try isDefEq pInst anchorTy catch e => do rethrowIfFatal e; pure false then
          found := some i
          break
      match found with
      | none => return none
      | some i => anchoredAt := some i

    -- Skip the anchor when scanning the lctx: it's already consumed at its
    -- locked slot, and re-using it for another premise only pins shared
    -- metavars to the same value, producing a tautological conclusion.
    let anchorName? := anchor.map (·.1)
    let some slots ← classifyPremises premises lctx anchorName? anchoredAt anchor
      | return none
    propagateMissing slots
    binderPinningSweep binders slots lctx anchorName?
    let conclI ← instantiateMVars conclusion
    if ← conclusionIsRedundant conclI lctx then return none
    let some finalSlots ← reclassifyMissing slots lctx anchorName? | return none
    let binderArgs ← binders.mapM instantiateMVars
    return some { name, binders := binderArgs, slots := finalSlots,
                  conclusion := conclI, ty := ci.type, mode := .forward }

/-! ## Display -/

/-- Render a binder value for paste-ready output. Unsolved mvars become `_`
    so Lean's elaborator can either infer them or surface them as needed.
    Compound expressions (anything that isn't an atom) are parenthesized so
    they parse as a single argument when concatenated. -/
private def fmtBinder (e : Expr) : TacticM MessageData := do
  let e ← instantiateMVars e
  if e.isMVar then return m!"_"
  let needsParens :=
    match e with
    | .app .. | .forallE .. | .lam .. | .letE .. => true
    | _ => false
  let pp ← ppExpr e
  if needsParens then return m!"({pp})" else return pp

/-- Render a slot. In `refine` mode, `.missing` slots become `?_` so the
    user gets a named subgoal instead of an inline `(by grind)` that
    silently fails; the residual type stays in a comment. -/
private def fmtSlot (refineMode : Bool) : PremiseSlot → TacticM MessageData
  | .hyp n _ => pure m!"{n}"
  | .discharged _ => pure m!"(by grind)"
  | .missing ty => do
    if refineMode then pure m!"?_ /- {← ppExpr ty} -/"
    else pure m!"(by grind /- {← ppExpr ty} -/)"

private def fmtMatch (r : AxiomMatch) : TacticM Unit := do
  let complete := slotsComplete r.slots
  let binderStrs ← r.binders.mapM fmtBinder
  let mark := if complete then m!"✓ " else m!"  "
  match r.mode with
  | .forward =>
    let slotStrs ← r.slots.mapM (fmtSlot (refineMode := false))
    let argsMsg := MessageData.joinSep (binderStrs ++ slotStrs).toList " "
    logInfo m!"{mark}have := {r.name} {argsMsg}\n    gives: {← ppExpr r.conclusion}"
  | .backward =>
    -- `exact` when every slot is filled; `refine` when some are `.missing`,
    -- so the missing premises surface as `?_` subgoals rather than failing
    -- inline via `(by grind)`. Filled slots (`.hyp` / `.discharged`) keep
    -- their args either way — `refine` still closes them.
    let slotStrs ← r.slots.mapM (fmtSlot (refineMode := !complete))
    let argsMsg := MessageData.joinSep (binderStrs ++ slotStrs).toList " "
    let head := if complete then m!"exact" else m!"refine"
    logInfo m!"{mark}{head} {r.name} {argsMsg}"

/-! ## Public entry point -/

def searchAxiomsImpl (mode : SearchMode) : TacticM Unit := withMainContext do
  let env ← getEnv
  let entries := collectFileTheorems env
  let lctx ← getLCtx

  let runBackward := match mode with | .all | .goalOnly => true | _ => false
  let runForward  := match mode with | .all | .hypsOnly | .hypOnly _ => true | _ => false

  -- Resolve anchor up front so a bad name fails loudly.
  let anchor : Option (Name × Expr) ← match mode with
    | .hypOnly hName =>
      let some hDecl := lctx.findFromUserName? hName
        | throwError "search_axioms: hypothesis '{hName}' is not in scope"
      pure (some (hName, ← instantiateMVars hDecl.type))
    | _ => pure none

  -- Backward
  let goalId ← getMainGoal
  let goalType ← instantiateMVars (← goalId.getType)
  let mut goalResults : Array AxiomMatch := #[]
  let mut goalNames : NameHashSet := {}
  if runBackward then
    for (name, ci) in entries do
      if let some r ← tryGoalMatch goalType name ci lctx then
        goalResults := goalResults.push r
        goalNames := goalNames.insert name

  -- Forward
  let mut fwdResults : Array AxiomMatch := #[]
  if runForward then
    for (name, ci) in entries do
      if goalNames.contains name then continue
      if let some r ← tryForward name ci lctx anchor then
        fwdResults := fwdResults.push r

  if goalResults.isEmpty && fwdResults.isEmpty then
    let modeStr := match mode with
      | .all => ""
      | .goalOnly => " (goal mode)"
      | .hypsOnly => " (hyps mode)"
      | .hypOnly n => s!" (anchored on `{n}`)"
    logInfo m!"No applicable axioms found{modeStr}"
    return

  if !goalResults.isEmpty then
    logInfo m!"── Apply (closes or nearly closes goal) ──"
    -- If any axiom fully closes the goal (all slots are .hyp or .discharged),
    -- show only those — partials are noise once we have a complete solution.
    -- Otherwise fall back to showing all partials.
    let fullyClosing := goalResults.filter (slotsComplete ·.slots)
    let toShow := if fullyClosing.isEmpty then goalResults else fullyClosing
    for r in toShow do fmtMatch r

  if !fwdResults.isEmpty then
    let header := match anchor with
      | some (hName, _) => m!"── Forward (anchored on `{hName}`) ──"
      | none => m!"── Forward (new facts from hypotheses) ──"
    logInfo header
    for r in fwdResults do
      if slotsComplete r.slots then fmtMatch r
    for r in fwdResults do
      if !slotsComplete r.slots then fmtMatch r
