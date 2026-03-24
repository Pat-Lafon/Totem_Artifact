import Lean

open Lean Meta

partial def eraseMacroScopesFromSyntax : Syntax → Syntax
  | .ident info rawVal name preresolved =>
    .ident info rawVal name.eraseMacroScopes preresolved
  | .node info kind args =>
    .node info kind (args.map eraseMacroScopesFromSyntax)
  | other => other

open Lean Elab Tactic Meta in
partial def destructCore (hypName : Name) (counter : IO.Ref Nat) : TacticM Unit :=
  withMainContext do
    -- Rescan context before each allocation so names never overlap with existing hypotheses
    let mut cur ← counter.get
    for d in (← getLCtx) do
      let s := d.userName.toString
      if s.startsWith "h" then
        if let some n := (s.drop 1).toNat? then
          cur := max cur (n + 1)
    counter.set cur
    let some decl := (← getLCtx).findFromUserName? hypName
      | return ()
    let hypType ← instantiateMVars decl.type
    let hi := mkIdent hypName

    match_expr hypType with
    | And _ _ => do
      let n ← counter.get
      let ln := Name.mkSimple s!"h{n}"
      let rn := Name.mkSimple s!"h{n + 1}"
      counter.set (n + 2)
      let li := mkIdent ln
      let ri := mkIdent rn
      let stx ← `(tactic| obtain ⟨$li, $ri⟩ := $hi)
      evalTactic (eraseMacroScopesFromSyntax stx)
      withMainContext do
        destructCore ln counter
        destructCore rn counter
    | Exists _ body => do
      let wn ← match body with
        | .lam n .. => mkFreshUserName n
        | _         => mkFreshUserName `w
      let n ← counter.get
      let pn := Name.mkSimple s!"h{n}"
      counter.set (n + 1)
      let wi := mkIdent wn
      let pi := mkIdent pn
      let stx ← `(tactic| obtain ⟨$wi, $pi⟩ := $hi)
      evalTactic (eraseMacroScopesFromSyntax stx)
      withMainContext do
        destructCore pn counter
    | _ => pure ()

open Lean Elab Tactic Meta in
elab "split_and" : tactic => do
  evalTactic (← `(tactic| repeat (any_goals apply And.intro)))
  try evalTactic (← `(tactic| any_goals grind)) catch _ => pure ()

open Lean Elab Tactic Meta in
elab "destruct" h:ident : tactic => withMainContext do
  let counter ← IO.mkRef 0
  destructCore h.getId counter
