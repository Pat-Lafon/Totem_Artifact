import ProofAutomation

/-! # Tests.Snapshots — value-level snapshot assertions.

Snapshots cover the output-producing helpers in `ProofAutomation` whose
correctness can't be checked by proof obligation alone:

- `ppOcamlAxiom` — used by `propose_axiom` to print proposed axioms in
  OCaml `let[@axiom] …` syntax.
- `search_axioms` — formats applicability hits for the user. -/

open Lean Elab

namespace Tests.Snapshots

-- Minimal fixture: a Cobb-shaped axiom theorem we can render via
-- `ppOcamlAxiom` and search against via `search_axioms`.
inductive ilist where
  | Nil
  | Cons (head : Int) (tail : ilist)
  deriving DecidableEq

def is_nil : ilist → Bool | .Nil => true | .Cons _ _ => false
def is_cons : ilist → Bool | .Nil => false | .Cons _ _ => true

def len_impl : ilist → Int
  | .Nil => 0
  | .Cons _ tl => 1 + len_impl tl
def len (l : ilist) (res : Int) : Prop := len_impl l = res

attribute [simp] is_nil is_cons len_impl len

-- Cobb-shaped axiom fixtures: bodies are `sorry` because the proofs are
-- irrelevant — these exist so `search_axioms` / `ppOcamlAxiom` have
-- something `Axioms.ax_<n>`-named to operate on. The expected
-- `declaration uses 'sorry'` warning is included in the snapshots below.
namespace Axioms

theorem ax_1 : ∀ (l : ilist) (res : Int),
    (len l res) → ((is_nil l) → ((0 == res) ∧ (0 = res))) := by
  sorry

theorem ax_2 : ∀ (l : ilist) (res : Int),
    (len l res) → ((is_cons l) → ((res > 0))) := by
  sorry

end Axioms

open Axioms

end Tests.Snapshots

/-! ## ppOcamlAxiom snapshots

Asserts that the OCaml renderer produces the expected
`let[@axiom] <name> <params> = <body>` form on a Cobb-shaped theorem.
Regression net for `OcamlFormat.lean`'s pretty-printers. -/

/--
info: let[@axiom] Tests.Snapshots.Axioms.ax_1 (l : ilist) (res : int) = ((len l res))#==>(((is_nil l))#==>(((0) == (res)) && ((0) == (res))))
-/
#guard_msgs in
run_cmd
  Command.liftTermElabM do
    let info ← getConstInfo `Tests.Snapshots.Axioms.ax_1
    let (params, body) ← ppOcamlAxiom info.type
    let paramsStr := String.intercalate " " params
    let shortName := info.name.toString
    Lean.logInfo s!"let[@axiom] {shortName} {paramsStr} = {body}"

/--
info: let[@axiom] Tests.Snapshots.Axioms.ax_2 (l : ilist) (res : int) = ((len l res))#==>(((is_cons l))#==>((res) > (0)))
-/
#guard_msgs in
run_cmd
  Command.liftTermElabM do
    let info ← getConstInfo `Tests.Snapshots.Axioms.ax_2
    let (params, body) ← ppOcamlAxiom info.type
    let paramsStr := String.intercalate " " params
    let shortName := info.name.toString
    Lean.logInfo s!"let[@axiom] {shortName} {paramsStr} = {body}"

/-! ## search_axioms snapshots

Asserts that `search_axioms` finds `Tests.Snapshots.Axioms.ax_1` / `ax_2`
for an appropriate hypothesis shape, with the expected `have := ax_N …`
format. If `fmtFwdResult` / `fmtGoalResult` formatting drifts, the
snapshot fires. -/

namespace Tests.Snapshots

attribute [local grind cases] ilist Bool
attribute [local grind =] is_nil is_cons len_impl len

/--
info: ── Apply (closes or nearly closes goal) ──
---
info: ✓ exact Tests.Snapshots.Axioms.ax_1 l res hlen _hcons
---
info: ── Forward (new facts from hypotheses) ──
---
info:   have := Tests.Snapshots.Axioms.ax_2 l res hlen (by grind /- is_cons l = true -/)
    gives: res > 0
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (l : ilist) (res : Int) (hlen : len l res) (_hcons : is_nil l = true) :
    (0 == res) ∧ (0 = res) := by
  search_axioms
  sorry

end Tests.Snapshots
