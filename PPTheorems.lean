import Lean

open Lean Meta

/-- Custom pretty-printer: translates a Lean Expr into a readable syntax. -/
partial def customPP (e : Expr) : MetaM String := do
  match e with
  -- ∀ (x : T), body  (also handles → when x is not free in body)
  | .forallE name ty body bi => do
    let tyStr ← customPP ty
    withLocalDecl name bi ty fun fvar => do
      let body' := body.instantiate1 fvar
      let bodyStr ← customPP body'
      if body.hasLooseBVars then
        return s!"∀ ({name} : {tyStr}), {bodyStr}"
      else
        return s!"({tyStr}) → {bodyStr}"
  -- ∃ (x : T), body  (Exists takes 2 args: type + predicate)
  | .app (.app (.const ``Exists _) _) lam => do
    match lam with
    | .lam name ty body _ =>
      let tyStr ← customPP ty
      withLocalDecl name .default ty fun fvar => do
        let body' := body.instantiate1 fvar
        let bodyStr ← customPP body'
        return s!"∃ ({name} : {tyStr}), {bodyStr}"
    | _ => return s!"∃ {← customPP lam}"
  -- P ∧ Q
  | .app (.app (.const ``And _) p) q => do
    return s!"({← customPP p}) ∧ ({← customPP q})"
  -- P ∨ Q
  | .app (.app (.const ``Or _) p) q => do
    return s!"({← customPP p}) ∨ ({← customPP q})"
  -- ¬ P
  | .app (.const ``Not _) p => do
    return s!"¬({← customPP p})"
  -- ↔
  | .app (.app (.const ``Iff _) p) q => do
    return s!"({← customPP p}) ↔ ({← customPP q})"
  -- a = b
  | .app (.app (.app (.const ``Eq _) _) a) b => do
    return s!"{← customPP a} = {← customPP b}"
  -- a == b (BEq)
  | .app (.app (.app (.app (.const ``BEq.beq _) _) _) a) b => do
    return s!"{← customPP a} == {← customPP b}"
  -- Comparisons (4 args: type + inst + a + b)
  | .app (.app (.app (.app (.const ``LT.lt _) _) _) a) b => do
    return s!"{← customPP a} < {← customPP b}"
  | .app (.app (.app (.app (.const ``LE.le _) _) _) a) b => do
    return s!"{← customPP a} ≤ {← customPP b}"
  | .app (.app (.app (.app (.const ``GT.gt _) _) _) a) b => do
    return s!"{← customPP a} > {← customPP b}"
  | .app (.app (.app (.app (.const ``GE.ge _) _) _) a) b => do
    return s!"{← customPP a} ≥ {← customPP b}"
  -- Arithmetic (6 args: 3 types + inst + a + b)
  | .app (.app (.app (.app (.app (.app (.const ``HAdd.hAdd _) _) _) _) _) a) b => do
    return s!"{← customPP a} + {← customPP b}"
  | .app (.app (.app (.app (.app (.app (.const ``HSub.hSub _) _) _) _) _) a) b => do
    return s!"{← customPP a} - {← customPP b}"
  | .app (.app (.app (.app (.app (.app (.const ``HMul.hMul _) _) _) _) _) a) b => do
    return s!"{← customPP a} * {← customPP b}"
  -- Division / modulo: explicitly unsupported
  | .app (.app (.app (.app (.app (.app (.const ``HDiv.hDiv _) _) _) _) _) _) _ => do
    throwError "customPP: division (HDiv) is not supported"
  | .app (.app (.app (.app (.app (.app (.const ``HMod.hMod _) _) _) _) _) _) _ => do
    throwError "customPP: modulo (HMod) is not supported"
  -- Unary negation
  | .app (.app (.app (.const ``Neg.neg _) _) _) a => do
    return s!"-{← customPP a}"
  -- Max
  | .app (.app (.app (.app (.const ``Max.max _) _) _) a) b => do
    return s!"max ({← customPP a}) ({← customPP b})"
  -- OfNat.ofNat (3 args: type + nat literal + instance)
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
    return s!"{n}"
  -- Option.some → unwrap
  | .app (.app (.const ``Option.some _) _) x => customPP x
  -- Option.none
  | .app (.const ``Option.none _) _ => return "none"
  -- Bool literals
  | .const ``Bool.true _ => return "true"
  | .const ``Bool.false _ => return "false"
  -- Prop literals
  | .const ``True _ => return "True"
  | .const ``False _ => return "False"
  -- Nat/Int literals
  | .lit (.natVal n) => return s!"{n}"
  | .app (.app (.const ``Int.ofNat _) _) (.lit (.natVal n)) => return s!"{n}"
  -- Free variables (bound vars that got instantiated)
  | .fvar id => do
    let decl ← id.getDecl
    return decl.userName.toString
  -- General application: flatten curried calls
  | e@(.app ..) => do
    let head := e.getAppFn
    let args := e.getAppArgs
    let headStr ← customPP head
    let argStrs ← args.toList.mapM customPP
    return s!"({headStr} {" ".intercalate argStrs})"
  -- Named constant
  | .const name _ => return name.toString
  -- Fallback: use Lean's built-in pretty printer
  | other => do
    let fmt ← ppExpr other
    return s!"{fmt}"

/-- Collect theorems from the environment, sorted by name.
    If suffix is empty, collects all theorems defined in the current file.
    Otherwise, collects theorems whose names end with the suffix. -/
private def collectTheorems (suffix : String) : Elab.Command.CommandElabM (Array (Name × Expr)) := do
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun acc name cinfo =>
    match cinfo with
    | .thmInfo info =>
      let nameStr := name.toString
      if suffix.isEmpty then
        match env.getModuleIdxFor? name with
        | none => acc.push (name, info.type)
        | some _ => acc
      else if nameStr.endsWith suffix then
        acc.push (name, info.type)
      else acc
    | _ => acc
  return entries.qsort (fun a b => a.1.toString < b.1.toString)

/-- Print theorems with custom pretty-printing.
    If suffix is empty, prints all theorems defined in the current file.
    Otherwise, prints theorems whose names end with the suffix. -/
def ppTheoremsWithSuffix (suffix : String := "") : Elab.Command.CommandElabM Unit := do
  let entries ← collectTheorems suffix
  for (name, ty) in entries do
    let tyStr ← Elab.Command.liftTermElabM <| customPP ty
    IO.println s!"-- {name}\n{tyStr}\n"

-- ═══════════════════════════════════════════════════════════════
-- OCaml axiom pretty-printer
-- ═══════════════════════════════════════════════════════════════

/-- Map a Lean type Expr to an OCaml type string.
    Only base types that exist in the OCaml axiom system are supported. -/
partial def ppOcamlType (e : Expr) : MetaM String := do
  match e with
  | .const name _ =>
    match name.toString with
    | "Int" | "Nat" => return "int"
    | "Bool" => return "bool"
    | s => return s
  | .app (.const ``Option _) inner => ppOcamlType inner
  | _ =>
    throwError "ppOcamlType: unsupported type '{← ppExpr e}'"

/-- Pretty-print an expression in OCaml axiom body syntax -/
partial def ocamlPP (e : Expr) : MetaM String := do
  match e with
  -- Implication (non-dependent ∀) → #==>
  | .forallE name ty body bi => do
    if body.hasLooseBVars then
      let tyStr ← ppOcamlType ty
      withLocalDecl name bi ty fun fvar => do
        let body' := body.instantiate1 fvar
        let bodyStr ← ocamlPP body'
        return s!"(∀ ({name} : {tyStr}), {bodyStr})"
    else
      let pStr ← ocamlPP ty
      let qStr ← ocamlPP body
      return s!"({pStr})#==>({qStr})"
  -- ∃ → fun ((x [@exists]) : t) ->  (Exists takes 2 args: type + predicate)
  | .app (.app (.const ``Exists _) _) lam => do
    match lam with
    | .lam name ty body _ =>
      let tyStr ← ppOcamlType ty
      withLocalDecl name .default ty fun fvar => do
        let body' := body.instantiate1 fvar
        let bodyStr ← ocamlPP body'
        return s!"fun (({name} [@exists]) : {tyStr}) -> {bodyStr}"
    | _ => return s!"(∃ {← ocamlPP lam})"
  -- ∧ → &&
  | .app (.app (.const ``And _) p) q => do
    return s!"({← ocamlPP p}) && ({← ocamlPP q})"
  -- ∨ → ||
  | .app (.app (.const ``Or _) p) q => do
    return s!"({← ocamlPP p}) || ({← ocamlPP q})"
  -- ¬ → not
  | .app (.const ``Not _) p => do
    return s!"(not ({← ocamlPP p}))"
  -- ↔
  | .app (.app (.const ``Iff _) p) q => do
    return s!"(({← ocamlPP p}) ↔ ({← ocamlPP q}))"
  -- a = true → a,  a = false → not a  (Bool predicate sugar)
  | .app (.app (.app (.const ``Eq _) _) a) (.const ``Bool.true _) => do
    ocamlPP a
  | .app (.app (.app (.const ``Eq _) _) a) (.const ``Bool.false _) => do
    return s!"(not ({← ocamlPP a}))"
  -- a = b
  | .app (.app (.app (.const ``Eq _) _) a) b => do
    return s!"({← ocamlPP a} = {← ocamlPP b})"
  -- a == b (BEq, 4 args: type + inst + a + b)
  | .app (.app (.app (.app (.const ``BEq.beq _) _) _) a) b => do
    return s!"({← ocamlPP a}) == ({← ocamlPP b})"
  -- Comparisons (4 args: type + inst + a + b)
  | .app (.app (.app (.app (.const ``LT.lt _) _) _) a) b => do
    return s!"({← ocamlPP a}) < ({← ocamlPP b})"
  | .app (.app (.app (.app (.const ``LE.le _) _) _) a) b => do
    return s!"({← ocamlPP a}) <= ({← ocamlPP b})"
  | .app (.app (.app (.app (.const ``GT.gt _) _) _) a) b => do
    return s!"({← ocamlPP a}) > ({← ocamlPP b})"
  | .app (.app (.app (.app (.const ``GE.ge _) _) _) a) b => do
    return s!"({← ocamlPP a}) >= ({← ocamlPP b})"
  -- Arithmetic (6 args: 3 types + inst + a + b)
  | .app (.app (.app (.app (.app (.app (.const ``HAdd.hAdd _) _) _) _) _) a) b => do
    return s!"({← ocamlPP a}) + ({← ocamlPP b})"
  | .app (.app (.app (.app (.app (.app (.const ``HSub.hSub _) _) _) _) _) a) b => do
    return s!"({← ocamlPP a}) - ({← ocamlPP b})"
  | .app (.app (.app (.app (.app (.app (.const ``HMul.hMul _) _) _) _) _) a) b => do
    return s!"({← ocamlPP a}) * ({← ocamlPP b})"
  -- Division / modulo: explicitly unsupported
  | .app (.app (.app (.app (.app (.app (.const ``HDiv.hDiv _) _) _) _) _) _) _ => do
    throwError "ocamlPP: division (HDiv) is not supported"
  | .app (.app (.app (.app (.app (.app (.const ``HMod.hMod _) _) _) _) _) _) _ => do
    throwError "ocamlPP: modulo (HMod) is not supported"
  -- Unary negation (3 args: type + inst + value)
  | .app (.app (.app (.const ``Neg.neg _) _) _) a => do
    return s!"(-{← ocamlPP a})"
  -- Max (4 args: type + inst + a + b)
  | .app (.app (.app (.app (.const ``Max.max _) _) _) a) b => do
    return s!"(max ({← ocamlPP a}) ({← ocamlPP b}))"
  -- OfNat.ofNat (3 args: type + nat literal + instance)
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
    return s!"{n}"
  -- Option.some → unwrap (2 args: type + value)
  | .app (.app (.const ``Option.some _) _) x => ocamlPP x
  -- Option.none
  | .app (.const ``Option.none _) _ => return "none"
  -- Bool literals
  | .const ``Bool.true _ => return "true"
  | .const ``Bool.false _ => return "false"
  -- Prop literals
  | .const ``True _ => return "true"
  | .const ``False _ => return "false"
  -- Nat/Int literals
  | .lit (.natVal n) => return s!"{n}"
  | .app (.app (.const ``Int.ofNat _) _) (.lit (.natVal n)) => return s!"{n}"
  -- Free variables
  | .fvar id => do
    let decl ← id.getDecl
    return decl.userName.toString
  -- General application: flatten curried calls into (f a1 a2 ...)
  | e@(.app ..) => do
    let head := e.getAppFn
    let args := e.getAppArgs
    let headStr ← ocamlPP head
    let argStrs ← args.toList.mapM ocamlPP
    return s!"({headStr} {" ".intercalate argStrs})"
  -- Named constant
  | .const name _ => return name.toString
  -- Fallback
  | other => do
    throwError "ocamlPP: unsupported expression '{← ppExpr other}'"

/-- Process a theorem type: extract top-level ∀ as params, print body as OCaml.
    Must stay inside withLocalDecl scopes so fvars remain valid. -/
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

/-- Print theorems as OCaml axiom declarations.
    Requires a suffix to filter theorems by name. -/
def ppTheoremsAsOcamlAxioms (suffix : String) : Elab.Command.CommandElabM Unit := do
  let entries ← collectTheorems suffix
  for (name, ty) in entries do
    let (params, bodyStr) ← Elab.Command.liftTermElabM <| ppOcamlAxiom ty
    let paramsStr := String.intercalate " " params
    IO.println s!"let[@axiom] {name} {paramsStr} = {bodyStr}"
    IO.println ""
