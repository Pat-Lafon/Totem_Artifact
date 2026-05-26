import Lean
import ProofAutomation.OcamlFormat
import ProofAutomation.Helpers

open Lean Elab Tactic Meta

/-! # ProposeAxiom — formulate an axiom from hypotheses, prove it, print it, apply it -/

-- Register a theorem under `<currentNamespace>.Axioms.<name>`. The `Axioms`
-- segment is what `Helpers.isAxiomName` keys on for pool collection.
-- Callers add `open Axioms` to reference the result unqualified.
private def registerThm (name : Name) (type : Expr) (value : Expr) : TacticM Name := do
  let currNs ← Lean.Elab.Term.getDeclName?
  let prefix' := match currNs with | some ns => ns ++ `Axioms | none => `Axioms
  let fullName := prefix' ++ name
  Lean.addDecl (Declaration.thmDecl {
    name        := fullName
    levelParams := []
    type        := type
    value       := value })
  return fullName

-- Build the axiom type from goal + selected hypotheses, in both ctor and accessor forms.
private def buildAxiomTypes (hyps : Array (TSyntax `ident)) (goal : Expr) :
    TacticM (Expr × Expr × Array FVarId) := do
  let lctx ← getLCtx
  let mut hypExprs : Array Expr := #[]
  for h in hyps do
    let some decl := lctx.findFromUserName? h.getId
      | throwError "propose_axiom: hypothesis '{h.getId}' not found"
    hypExprs := hypExprs.push (← instantiateMVars decl.type)
  let mut prop := goal
  for ty in hypExprs.reverse do prop := Expr.forallE `_ ty prop .default
  let fvarIds := (Lean.collectFVars {} prop).fvarSet.toArray
  let sortedFVars := fvarIds.qsort fun a b =>
    match lctx.find? a, lctx.find? b with
    | some da, some db => da.index < db.index | _, _ => false
  let ctorAxiomType ← mkForallFVars (sortedFVars.map mkFVar) prop
  let axiomType ← replaceCtorsWithAccessors ctorAxiomType
  return (ctorAxiomType, axiomType, sortedFVars)

-- Build simp/grind lemma syntax arrays from user-defined constants in a type.
private def buildDefLemmas (env : Environment) (ty : Expr) :
    TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma) × Array (TSyntax ``Lean.Parser.Tactic.grindParam)) := do
  let defNames := collectUserDefs env ty
  let mut simpLemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  let mut grindParams : Array (TSyntax ``Lean.Parser.Tactic.grindParam) := #[]
  for cn in defNames.toArray do
    let ident := mkIdent cn
    simpLemmas := simpLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $ident:ident))
    grindParams := grindParams.push (← `(Lean.Parser.Tactic.grindParam| $ident:ident))
  return (simpLemmas, grindParams)

-- Prove the constructor form of an axiom via grind/cases/induction strategies.
-- The mvar is created in an empty local context so tactics like `grind` cannot
-- reference outer fvars (which would leave the proof term with free variables
-- and produce a kernel "declaration has free variables" error at addDecl time).
private def proveCtorForm (ctorAxiomType : Expr) (env : Environment)
    (grindParams : Array (TSyntax ``Lean.Parser.Tactic.grindParam))
    (simpLemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM Expr := do
  let ctorMVar ← Meta.withLCtx {} {} <|
    mkFreshExprMVar (some ctorAxiomType) (kind := .syntheticOpaque)
  let (ctorIntroIdents, ctorInductiveNames) := scanForallIntros env ctorAxiomType "_pa"
  let doCtorIntro : TacticM Unit :=
    evalTactic (eraseMacroScopesFromSyntax (← `(tactic| intro $ctorIntroIdents*)))
  let savedGoals ← getGoals
  let tryStrategy (body : TacticM Unit) : TacticM (Option Expr) := do
    if ← withBacktrack do setGoals [ctorMVar.mvarId!]; doCtorIntro; body then
      return some (← instantiateMVars ctorMVar)
    return none
  -- Strategy 1: intro + grind
  if let some r ← tryStrategy <| evalTactic (← `(tactic| grind (splits := 20) [$grindParams,*])) then
    return r
  -- Strategy 2: intro + cases + simp_all + grind
  for caseVar in ctorInductiveNames do
    if let some r ← tryStrategy <| evalTactic (eraseMacroScopesFromSyntax
        (← `(tactic| cases $caseVar:ident <;> (simp_all; try grind (splits := 20) [$grindParams,*]))))
    then return r
  -- Strategy 3: intro + induction + simp + grind
  for caseVar in ctorInductiveNames do
    if let some r ← tryStrategy <| evalTactic (eraseMacroScopesFromSyntax (← `(tactic|
        induction $caseVar:ident <;> simp only [$simpLemmas,*] at * <;> grind (splits := 20) [$grindParams,*])))
    then return r
  setGoals savedGoals
  throwError "propose_axiom: could not auto-prove constructor form"

-- Build a tactic that chains `cases v1 <;> cases v2 <;> ... <;> finalTac`.
private def buildChainedCases (vars : Array (TSyntax `ident))
    (finalTac : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  if vars.isEmpty then return finalTac
  let mut tac := finalTac
  for i in [:vars.size] do
    let v := vars[vars.size - 1 - i]!
    tac ← `(tactic| cases $v:ident <;> $tac)
  return ⟨eraseMacroScopesFromSyntax tac.raw⟩

-- Derive the accessor form from the constructor form.
private def deriveAccessorForm (axiomType : Expr) (env : Environment)
    (simpLemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma))
    (grindParams : Array (TSyntax ``Lean.Parser.Tactic.grindParam)) : TacticM Expr := do
  let axiomMVar ← Meta.withLCtx {} {} <|
    mkFreshExprMVar (some axiomType) (kind := .syntheticOpaque)
  let (introIdents, inductiveNames) := scanForallIntros env axiomType "_pa"
  let doIntro : TacticM Unit :=
    evalTactic (eraseMacroScopesFromSyntax (← `(tactic| intro $introIdents*)))
  let simpAccessors : TacticM Unit :=
    evalTactic (← `(tactic| all_goals simp_all [$simpLemmas,*]))
  let tryStrategy (body : TacticM Unit) : TacticM (Option Expr) := do
    if ← withBacktrack do setGoals [axiomMVar.mvarId!]; doIntro; body then
      return some (← instantiateMVars axiomMVar)
    return none
  -- Strategy 1: cases on each intro variable + simp_all
  for indVar in introIdents do
    if let some r ← tryStrategy do
        evalTactic (eraseMacroScopesFromSyntax (← `(tactic| cases $indVar:ident)))
        simpAccessors
    then return r
  -- Strategy 2: just intro + simp_all (no cases needed)
  if let some r ← tryStrategy simpAccessors then return r
  -- Strategy 3: cases on ALL inductive variables + simp_all (+ try grind).
  -- For nested pattern matching on multiple args, single-cases leaves stuck matches.
  if inductiveNames.size > 1 then
    let finalTac ← `(tactic|
      (simp_all [$simpLemmas,*]; try grind (splits := 20) [$grindParams,*]))
    let chainedTac ← buildChainedCases inductiveNames finalTac
    if let some r ← tryStrategy (evalTactic chainedTac) then return r
  -- Strategy 4: cases on each inductive variable + simp_all + grind
  for indVar in inductiveNames do
    if let some r ← tryStrategy <| evalTactic (eraseMacroScopesFromSyntax
        (← `(tactic| cases $indVar:ident <;> (simp_all [$simpLemmas,*]; try grind (splits := 20) [$grindParams,*]))))
    then return r
  -- Strategy 5: intro + grind (no cases)
  if let some r ← tryStrategy <|
      evalTactic (← `(tactic| grind (splits := 20) [$grindParams,*]))
  then return r
  throwError "propose_axiom: proved constructor form but could not derive accessor form"

/-! ## Public entry point -/

def proposeAxiomImpl (name : TSyntax `str) (hyps : TSyntaxArray `ident) : TacticM Unit :=
  withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    let env ← getEnv

    -- Build both axiom type forms
    let (ctorAxiomType, axiomType, sortedFVars) ← buildAxiomTypes hyps goal

    -- Print axiom. `ppOcamlAxiom` failure is fatal: the printed `let[@axiom]`
    -- line is the load-bearing paste-back artifact for Cobb-Totem, so a
    -- silent warning here would leave the user with a registered theorem
    -- but no way to copy it back into the OCaml source.
    let axiomName := name.getString
    let (params, bodyStr) ← ppOcamlAxiom axiomType
    logInfo m!"let[@axiom] {axiomName} {String.intercalate " " params} = {bodyStr}"
    logInfo m!"theorem {axiomName} : {← ppExpr axiomType}"

    let (simpLemmas, grindParams) ← buildDefLemmas env axiomType

    -- Prove constructor form and register it
    let savedGoals ← getGoals
    let ctorProofTerm ← proveCtorForm ctorAxiomType env grindParams simpLemmas
    let ctorBaseName := Name.mkSimple s!"{axiomName}_ctor"
    let ctorDeclName ← registerThm ctorBaseName ctorAxiomType ctorProofTerm

    -- Derive accessor form and register it
    let axiomProofTerm ← deriveAccessorForm axiomType env simpLemmas grindParams
    let baseName := Name.mkSimple axiomName
    let declName ← registerThm baseName axiomType axiomProofTerm
    logInfo m!"Registered theorem: {declName}"

    -- Close the main goal using the constructor-form proof
    setGoals savedGoals
    withMainContext do
      let mainGoal ← getMainGoal
      let mut fullProof := mkConst ctorDeclName
      for fid in sortedFVars do fullProof := mkApp fullProof (mkFVar fid)
      for h in hyps do
        let some hDecl := (← getLCtx).findFromUserName? h.getId
          | do
            let available := (← getLCtx).foldl (init := #[]) fun acc decl =>
              if decl.isAuxDecl then acc else acc.push decl.userName
            throwError "propose_axiom: hypothesis '{h.getId}' not found when applying.\nAvailable hypotheses: {available}"
        fullProof := mkApp fullProof (mkFVar hDecl.fvarId)
      mainGoal.assign fullProof
