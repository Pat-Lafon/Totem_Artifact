import ProofAutomation

/-! # Tests.Z3Command — regression suite for the unified `z3` command.

Pins the merged `z3` / `z3?` / `z3!` / `z3!?` command surface with optional
`only [...]` filter. Requires Z3 on PATH (4.15.1+). Unlike `Tests.Z3Local`,
the command form does not construct a proof term — it elaborates an
already-stated theorem's type, asks Z3 if axioms entail it, and logs
unsat/sat. Trust-footprint pinning stays in `Tests.Z3Local`. -/

namespace Tests.Z3Command

/-! ### Happy paths -/

namespace Axioms
theorem ax_zero : ∀ (n : Int), n + 0 = n := by intros; omega
theorem ax_succ : ∀ (n : Int), n + 1 = n + 1 := by intros; rfl
end Axioms
open Axioms

theorem test_auto : ∀ (n : Int), n + 0 = n := by intros; omega

/-- info: z3: unsat ✓ -/
#guard_msgs in z3 Tests.Z3Command.test_auto

/-- info: z3: unsat ✓ -/
#guard_msgs in z3 Tests.Z3Command.test_auto only [Tests.Z3Command.Axioms.ax_zero]

-- Unqualified ident inside the namespace resolves via
-- `resolveGlobalConstNoOverloadCore` to `Tests.Z3Command.Axioms.ax_zero`
-- (`open Axioms` brings the `Axioms` namespace into scope).
/-- info: z3: unsat ✓ -/
#guard_msgs in z3 Tests.Z3Command.test_auto only [ax_zero]

-- Unqualified goal ident resolves the same way.
/-- info: z3: unsat ✓ -/
#guard_msgs in z3 test_auto only [ax_zero]

namespace Axioms
theorem ax_trivial : (0 : Int) = 0 := rfl
end Axioms

-- `only []` confirms Z3 closes a tautology without any user axioms.
/-- info: z3: unsat ✓ -/
#guard_msgs in z3 Tests.Z3Command.Axioms.ax_trivial only []

/-! ### excludeName preservation (decision 7)

`z3 ax_X` must not trivially close by using `ax_X` itself as an axiom.
We declare an opaque predicate so the goal is only provable via the
self-axiom; if the exclude were dropped, Z3 would return `unsat` instead
of `sat`. -/

opaque P : Int → Prop
axiom P_axiom : P 5

namespace Axioms
theorem ax_excluded : P 5 := P_axiom
end Axioms

/--
error: z3: sat — axioms are NOT sufficient for 'Tests.Z3Command.Axioms.ax_excluded', or goal is false
Hint: the goal may be genuinely refutable — try `propose_counterexample Tests.Z3Command.Axioms.ax_excluded` at a `sorry` site.
-/
#guard_msgs in z3 Tests.Z3Command.Axioms.ax_excluded only []

end Tests.Z3Command

/-! ### Untranslatable axiom (decision 1 + 13)

`gatherUserAxioms` errors on any translation failure. Sub-namespace so the
broken axiom only affects this test — it would otherwise poison every
later `z3` call in the file because `gatherUserAxioms` walks the entire
env. -/

namespace Tests.Z3CommandUntranslatable

namespace Axioms
theorem ax_bad (f : Int → Int) (x : Int) : f x = f x := rfl
end Axioms
open Axioms

theorem test_bad : (1 : Int) = 1 := rfl

/--
error: z3: failed to translate 1 axiom(s):
  - Tests.Z3CommandUntranslatable.Axioms.ax_bad: z3 toSmt: cannot translate forall binder `f : Int →
  Int` (kind `Type`). the binder is used in the body, so the LHS must be translatable to an SMT sort. Underlying sortToSmt error: z3 sortToSmt: cannot translate sort expression: Int →
  Int
-/
#guard_msgs in z3 Tests.Z3CommandUntranslatable.test_bad

end Tests.Z3CommandUntranslatable
