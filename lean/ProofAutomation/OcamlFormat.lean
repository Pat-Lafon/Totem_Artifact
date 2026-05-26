import Lean
import ProofAutomation.Helpers

open Lean Meta

/-! ## PPStyle: parameterized expression pretty-printer -/

/-- Map a Lean type Expr to an OCaml type string. -/
partial def ppOcamlType (e : Expr) : MetaM String := do
  match e with
  | .const name _ =>
    match name.toString with
    | "Int" | "Nat" => return "int"
    | "Bool" => return "bool"
    -- User-defined types live under whatever namespace the test file uses
    -- (e.g. `Tests.Snapshots.ilist`). Strip to the last component so the
    -- emitted OCaml is what Cobb's reader expects.
    | _ => return name.getString!
  | .app (.const ``Option _) inner => ppOcamlType inner
  | _ =>
    throwError "ppOcamlType: unsupported type '{← ppExpr e}'"

structure PPStyle where
  fmtForallDep   : String → String → String → String  -- name, type, body
  fmtArrow       : String → String → String            -- premise, conclusion
  fmtExists      : String → String → String → String   -- name, type, body
  fmtAnd         : String → String → String
  fmtOr          : String → String → String
  fmtNot         : String → String
  fmtIff         : String → String → String
  fmtEqBoolTrue  : Option (String → String)            -- none = no sugar
  fmtEqBoolFalse : Option (String → String)
  fmtEq          : String → String → String
  fmtCmp         : String → String → String → String   -- op, l, r
  fmtArith       : String → String → String → String   -- op, l, r
  fmtNeg         : String → String
  fmtMax         : String → String → String
  propTrue       : String
  propFalse      : String
  leSymbol       : String
  geSymbol       : String
  ppBinderType   : Expr → MetaM String
  ppFallback     : Expr → MetaM String

partial def genericPP (s : PPStyle) (e : Expr) : MetaM String := do
  match e with
  | .forallE name ty body bi => do
    if body.hasLooseBVars then
      let tyStr ← s.ppBinderType ty
      withLocalDecl name bi ty fun fvar => do
        let bodyStr ← genericPP s (body.instantiate1 fvar)
        return s.fmtForallDep name.toString tyStr bodyStr
    else
      let pStr ← genericPP s ty
      let qStr ← genericPP s body
      return s.fmtArrow pStr qStr
  | .app (.app (.const ``Exists _) _) lam => do
    match lam with
    | .lam name ty body _ =>
      let tyStr ← s.ppBinderType ty
      withLocalDecl name .default ty fun fvar => do
        let bodyStr ← genericPP s (body.instantiate1 fvar)
        return s.fmtExists name.toString tyStr bodyStr
    | _ => return s!"∃ {← genericPP s lam}"
  | .app (.app (.const ``And _) p) q => do
    return s.fmtAnd (← genericPP s p) (← genericPP s q)
  | .app (.app (.const ``Or _) p) q => do
    return s.fmtOr (← genericPP s p) (← genericPP s q)
  | .app (.const ``Not _) p => do
    return s.fmtNot (← genericPP s p)
  | .app (.app (.const ``Iff _) p) q => do
    return s.fmtIff (← genericPP s p) (← genericPP s q)
  | .app (.app (.app (.const ``Eq _) _) a) (.const ``Bool.true _) => do
    if let some fmt := s.fmtEqBoolTrue then return fmt (← genericPP s a)
    return s.fmtEq (← genericPP s a) "true"
  | .app (.app (.app (.const ``Eq _) _) a) (.const ``Bool.false _) => do
    if let some fmt := s.fmtEqBoolFalse then return fmt (← genericPP s a)
    return s.fmtEq (← genericPP s a) "false"
  | .app (.app (.app (.const ``Eq _) _) a) b => do
    return s.fmtEq (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.const ``BEq.beq _) _) _) a) b => do
    return s.fmtEq (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.const ``LT.lt _) _) _) a) b => do
    return s.fmtCmp "<" (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.const ``LE.le _) _) _) a) b => do
    return s.fmtCmp s.leSymbol (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.const ``GT.gt _) _) _) a) b => do
    return s.fmtCmp ">" (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.const ``GE.ge _) _) _) a) b => do
    return s.fmtCmp s.geSymbol (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.app (.app (.const ``HAdd.hAdd _) _) _) _) _) a) b => do
    return s.fmtArith "+" (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.app (.app (.const ``HSub.hSub _) _) _) _) _) a) b => do
    return s.fmtArith "-" (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.app (.app (.const ``HMul.hMul _) _) _) _) _) a) b => do
    return s.fmtArith "*" (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.app (.app (.app (.const ``HDiv.hDiv _) _) _) _) _) _) _ => do
    throwError "genericPP: division (HDiv) is not supported"
  | .app (.app (.app (.app (.app (.app (.const ``HMod.hMod _) _) _) _) _) _) _ => do
    throwError "genericPP: modulo (HMod) is not supported"
  | .app (.app (.app (.const ``Neg.neg _) _) _) a => do
    return s.fmtNeg (← genericPP s a)
  | .app (.app (.app (.app (.const ``Max.max _) _) _) a) b => do
    return s.fmtMax (← genericPP s a) (← genericPP s b)
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
    return s!"{n}"
  | .app (.app (.app (.app (.const ``Coe.coe _) _) _) _) x => genericPP s x
  | .app (.app (.const ``Option.some _) _) x => genericPP s x
  | .app (.const ``Option.none _) _ => return "none"
  | .const ``Bool.true _ => return "true"
  | .const ``Bool.false _ => return "false"
  | .const ``True _ => return s.propTrue
  | .const ``False _ => return s.propFalse
  | .lit (.natVal n) => return s!"{n}"
  | .app (.app (.const ``Int.ofNat _) _) (.lit (.natVal n)) => return s!"{n}"
  | .fvar id => do return (← id.getDecl).userName.toString
  | e@(.app ..) => do
    let headStr ← genericPP s e.getAppFn
    let argStrs ← e.getAppArgs.toList.mapM (genericPP s)
    return s!"({headStr} {" ".intercalate argStrs})"
  | .const name _ => return name.getString!
  | other => s.ppFallback other

/-! ## Style instances -/

def ocamlStyle : PPStyle where
  fmtForallDep n t b   := s!"(∀ ({n} : {t}), {b})"
  fmtArrow l r         := s!"({l})#==>({r})"
  fmtExists n t b      := s!"fun (({n} [@exists]) : {t}) -> {b}"
  fmtAnd l r           := s!"({l}) && ({r})"
  fmtOr l r            := s!"({l}) || ({r})"
  fmtNot p             := s!"(not ({p}))"
  fmtIff l r           := s!"(({l}) ↔ ({r}))"
  fmtEqBoolTrue        := some fun a => a
  fmtEqBoolFalse       := some fun a => s!"(not ({a}))"
  fmtEq l r            := s!"({l}) == ({r})"
  fmtCmp op l r        := s!"({l}) {op} ({r})"
  fmtArith op l r      := s!"(({l}) {op} ({r}))"
  fmtNeg a             := s!"(-{a})"
  fmtMax l r           := s!"(max ({l}) ({r}))"
  propTrue             := "true"
  propFalse            := "false"
  leSymbol             := "<="
  geSymbol             := ">="
  ppBinderType         := ppOcamlType
  ppFallback e         := do throwError s!"ocamlPP: unsupported expression '{← ppExpr e}'"

def ocamlPP := genericPP ocamlStyle

/-! ## Theorem collection -/

private def collectTheorems (suffix : String) : Elab.Command.CommandElabM (Array (Name × Expr)) := do
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun acc name cinfo =>
    match cinfo with
    | .thmInfo info =>
      if isAxiomName name &&
         (suffix.isEmpty || name.getString!.endsWith suffix) then
        acc.push (name, info.type)
      else acc
    | _ => acc
  return entries.qsort (fun a b => a.1.toString < b.1.toString)

/-! ## Constructor-to-accessor transformation -/

private def getCtorFieldNames (ctorType : Expr) (numParams : Nat) : Array Name := Id.run do
  let mut names : Array Name := #[]
  let mut cur := ctorType
  let mut idx := 0
  while true do
    match cur with
    | .forallE name _ body _ =>
      if idx >= numParams then names := names.push name.eraseMacroScopes
      idx := idx + 1; cur := body
    | _ => break
  return names

private partial def collectUserCtorApps (env : Environment) (e : Expr)
    (acc : Array Expr := #[]) : Array Expr :=
  let acc :=
    if let .const name _ := e.getAppFn then
      if let some (.ctorInfo ci) := env.find? name then
        if isUserInductive env ci.induct &&
           e.getAppNumArgs == ci.numParams + ci.numFields then
          if !acc.any (· == e) then acc.push e else acc
        else acc
      else acc
    else acc
  match e with
  | .app f a => collectUserCtorApps env a (collectUserCtorApps env f acc)
  | .lam _ ty body _ => collectUserCtorApps env body (collectUserCtorApps env ty acc)
  | .forallE _ ty body _ => collectUserCtorApps env body (collectUserCtorApps env ty acc)
  | .letE _ ty val body _ =>
    collectUserCtorApps env body (collectUserCtorApps env val (collectUserCtorApps env ty acc))
  | .mdata _ inner => collectUserCtorApps env inner acc
  | .proj _ _ inner => collectUserCtorApps env inner acc
  | _ => acc

private def buildAccessorPremise (ci : ConstructorVal)
    (ctorApp : Expr) (tFVar : Expr) : MetaM Expr := do
  let ctorShortName := ci.name.getString!
  let discrimName := Name.mkSimple s!"is_{ctorShortName.toLower}"
  let discrimApp := mkApp (mkConst discrimName) tFVar
  let mut conj ← mkAppM ``Eq #[discrimApp, mkConst ``Bool.true]
  let fieldNames := getCtorFieldNames ci.type ci.numParams
  let args := ctorApp.getAppArgs
  for i in [:ci.numFields] do
    let fieldName := fieldNames[i]!
    let arg := args[ci.numParams + i]!
    let accessorApp := mkApp (mkConst fieldName) tFVar
    let accessorTy ← inferType accessorApp
    let wrappedArg ← if accessorTy.isAppOf ``Option then
      mkAppM ``Option.some #[arg]
    else pure arg
    let eqProp ← mkAppM ``Eq #[accessorApp, wrappedArg]
    conj ← mkAppM ``And #[conj, eqProp]
  return conj

def replaceCtorsWithAccessors (axiomType : Expr) : MetaM Expr := do
  let env ← getEnv
  forallTelescope axiomType fun fvars body => do
    let mut varFVars : Array Expr := #[]
    let mut premiseFVars : Array Expr := #[]
    for fv in fvars do
      let sort ← inferType (← inferType fv)
      if sort.isProp then premiseFVars := premiseFVars.push fv
      else varFVars := varFVars.push fv
    let mut expandedBody := body
    for i in [:premiseFVars.size] do
      let fv := premiseFVars[premiseFVars.size - 1 - i]!
      let decl ← fv.fvarId!.getDecl
      expandedBody := .forallE decl.userName decl.type (expandedBody.abstract #[fv]) .default
    let ctorApps := collectUserCtorApps env expandedBody
    if ctorApps.isEmpty then return axiomType
    let rec go : List Expr → Expr → Array Expr → Array Expr → Nat → MetaM Expr
      | [], currentBody, extraFVars, extraPremises, _ => do
        let mut result := currentBody
        for premise in extraPremises.reverse do
          result := .forallE `_ premise result .default
        mkForallFVars (extraFVars ++ varFVars) result
      | ctorApp :: rest, currentBody, extraFVars, extraPremises, counter => do
        if (currentBody.find? (· == ctorApp)).isNone then
          go rest currentBody extraFVars extraPremises counter
        else
          let .const ctorName _ := ctorApp.getAppFn
            | go rest currentBody extraFVars extraPremises counter
          let some (.ctorInfo ci) := env.find? ctorName
            | go rest currentBody extraFVars extraPremises counter
          let ctorShortName := ci.name.getString!
          let discrimName := Name.mkSimple s!"is_{ctorShortName.toLower}"
          if (env.find? discrimName).isNone then
            go rest currentBody extraFVars extraPremises counter
          else
            let inductTy := mkConst ci.induct
            let varName := if counter == 0 then `t else Name.mkSimple s!"t_{counter}"
            withLocalDecl varName .default inductTy fun tFVar => do
              let newBody := currentBody.replace fun e =>
                if e == ctorApp then some tFVar else none
              let premise ← buildAccessorPremise ci ctorApp tFVar
              go rest newBody (extraFVars.push tFVar) (extraPremises.push premise) (counter + 1)
    go ctorApps.toList expandedBody #[] #[] 0

/-! ## OCaml axiom formatting -/

partial def ppOcamlAxiom (e : Expr) : MetaM (List String × String) := do
  match e with
  | .forallE name ty body bi => do
    if body.hasLooseBVars then
      let tyStr ← ppOcamlType ty
      withLocalDecl name bi ty fun fvar => do
        let body' := body.instantiate1 fvar
        let (params, bodyStr) ← ppOcamlAxiom body'
        return (s!"({name} : {tyStr})" :: params, bodyStr)
    else
      let bodyStr ← ocamlPP e
      return ([], bodyStr)
  | _ =>
    let bodyStr ← ocamlPP e
    return ([], bodyStr)

def ppTheoremsAsOcamlAxioms (suffix : String) : Elab.Command.CommandElabM Unit := do
  let entries ← collectTheorems suffix
  for (name, ty) in entries do
    let ty ← Elab.Command.liftTermElabM <| replaceCtorsWithAccessors ty
    let (params, bodyStr) ← Elab.Command.liftTermElabM <| ppOcamlAxiom ty
    let paramsStr := String.intercalate " " params
    let shortName := match name with | .str _ s => s | _ => name.toString
    IO.println s!"let[@axiom] {shortName} {paramsStr} = {bodyStr}"
    IO.println ""
