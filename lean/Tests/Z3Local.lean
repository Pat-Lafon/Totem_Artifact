import ProofAutomation

/-! # Tests.Z3Local — regression suite for the `z3_local` tactic.

Requires Z3 on PATH (4.15.1+). Every `z3_local`-closed theorem depends on
`ProofAutomation.Trusted.z3SmtTrusted` — that's the SMT trust anchor,
asserted explicitly below so a regression that closes goals *without*
going through Z3 (or, conversely, leaks `sorryAx`) is caught. -/

namespace Tests.Z3Local

-- A theorem in the `Axioms` namespace; `gatherUserAxioms` picks it up
-- via `isAxiomName`. Used below to exercise the `only` axiom-filter path.
namespace Axioms
theorem ax_test_succ : ∀ (n : Int), n + 1 = n + 1 := by intros; rfl
end Axioms
open Axioms

-- Smoke: pure arithmetic, no hypotheses, no axiom filter.
theorem test_z3_local_smoke : ∀ (n : Int), n + 0 = n := by
  intro _; z3_local

-- With a single local hypothesis (full lctx is always sent).
theorem test_z3_local_with_hyp : ∀ (n : Int), n = 5 → n + 0 = 5 := by
  intros _ _; z3_local

-- `only [ax_…]` restricts the env axiom set to the listed names. The
-- filter compares fully-qualified names; pass the namespaced form.
theorem test_z3_local_only_axiom : ∀ (n : Int), n = 5 → n + 0 = 5 := by
  intros _ _; z3_local only [Tests.Z3Local.Axioms.ax_test_succ]

-- `only []` sends zero axioms; the goal must hold from lctx alone.
theorem test_z3_local_only_empty : ∀ (n : Int), n = 99 → (1 : Int) + 1 = 2 := by
  intros _ _; z3_local only []

-- Verbose `?` mode requests unsat cores from Z3. When no `:named` axiom is
-- needed (e.g. `only []`, or theory reasoning closes the negated goal
-- alone), Z3 emits `()` — the empty core. Must be accepted as a legitimate
-- `unsat`, not flagged as malformed.
theorem test_z3_local_verbose_empty_core : ∀ (n : Int), n = 99 → (1 : Int) + 1 = 2 := by
  intros _ _; z3_local? only []

-- After `cases`, each branch closes via z3_local.
theorem test_z3_local_after_cases (b : Bool) : b = true ∨ b = false := by
  cases b <;> z3_local

end Tests.Z3Local

/-! ## Trust-anchor assertions

Each test must depend on `z3SmtTrusted` *and nothing else*. Any other
axiom appearing here (e.g. `sorryAx`) is a regression. -/

/-- info: 'Tests.Z3Local.test_z3_local_smoke' depends on axioms: [ProofAutomation.Trusted.z3SmtTrusted] -/
#guard_msgs in #print axioms Tests.Z3Local.test_z3_local_smoke

/-- info: 'Tests.Z3Local.test_z3_local_with_hyp' depends on axioms: [ProofAutomation.Trusted.z3SmtTrusted] -/
#guard_msgs in #print axioms Tests.Z3Local.test_z3_local_with_hyp

/-- info: 'Tests.Z3Local.test_z3_local_only_axiom' depends on axioms: [ProofAutomation.Trusted.z3SmtTrusted] -/
#guard_msgs in #print axioms Tests.Z3Local.test_z3_local_only_axiom

/-- info: 'Tests.Z3Local.test_z3_local_only_empty' depends on axioms: [ProofAutomation.Trusted.z3SmtTrusted] -/
#guard_msgs in #print axioms Tests.Z3Local.test_z3_local_only_empty

/-- info: 'Tests.Z3Local.test_z3_local_verbose_empty_core' depends on axioms: [ProofAutomation.Trusted.z3SmtTrusted] -/
#guard_msgs in #print axioms Tests.Z3Local.test_z3_local_verbose_empty_core

/-- info: 'Tests.Z3Local.test_z3_local_after_cases' depends on axioms: [ProofAutomation.Trusted.z3SmtTrusted] -/
#guard_msgs in #print axioms Tests.Z3Local.test_z3_local_after_cases

/-! ## Binder/declared-symbol shadowing contract

A quantifier binder whose name matches a previously-declared SMT symbol
(datatype, constructor, selector, declared sort, or uninterpreted
function) must be rejected at the translator — otherwise Z3 silently
rebinds the inner reference and fails downstream with a cryptic
`select requires N arguments` message.

Here `Box.Mk` declares a selector `shadow_field`; the theorem's later
`forall (shadow_field : Int)` binder collides with it. -/

namespace Tests.Z3LocalShadow

inductive Box where
  | Mk (shadow_field : Int)

/--
error: z3 toSmt: forall binder `shadow_field` shadows a top-level SMT symbol of the same name (datatype, constructor, selector, declared sort, or uninterpreted function). Z3 would silently rebind the inner reference to the binder, then fail at the call site with an unhelpful arity/sort message (typically 'select requires 0 arguments'). Rename the binder in the source theorem to a non-colliding name.
-/
#guard_msgs in
example : ∀ (b : Box) (shadow_field : Int), b = b ∧ shadow_field = shadow_field := by
  intros; z3_local

end Tests.Z3LocalShadow

/-! ## Duplicate-in-`only` contract

Listing the same axiom twice in `only [...]` would emit two `:named`
assertions with the same label, which Z3 rejects with
`named expression already defined`. The filter must surface the dup
by name *before* dispatch, not let Z3 crash on a malformed query. -/

namespace Tests.Z3LocalDupOnly

namespace Axioms
theorem ax_dup_ok : ∀ (n : Int), n = n := by intros; rfl
end Axioms
open Axioms

/--
error: z3_local: axiom 'Tests.Z3LocalDupOnly.Axioms.ax_dup_ok' listed more than once in `only [...]` (would emit a duplicate `:named` assertion and crash Z3). Remove the duplicate.
-/
#guard_msgs in
example : ∀ (n : Int), n + 0 = n := by
  intro _; z3_local only [ax_dup_ok, ax_dup_ok]

end Tests.Z3LocalDupOnly

/-! ## Untranslatable-axiom contract (PLAN_z3_unify.md decision 1)

`gatherUserAxioms` throws on any axiom whose type can't be translated to
SMT (function-typed binder, etc.) — same contract as command-mode `z3`.
Kept at the end of the file because once `ax_bad` is in the env, every
later `z3_local` call would also fail; the trust-anchor assertions above
already locked in their proofs from earlier elaboration. -/

namespace Tests.Z3LocalUntranslatable

namespace Axioms
theorem ax_bad (f : Int → Int) (x : Int) : f x = f x := rfl
end Axioms
open Axioms

/--
error: z3_local: failed to translate 1 axiom(s):
  - Tests.Z3LocalUntranslatable.Axioms.ax_bad: z3 toSmt: cannot translate forall binder `f : Int →
  Int` (kind `Type`). the binder is used in the body, so the LHS must be translatable to an SMT sort. Underlying sortToSmt error: z3 sortToSmt: cannot translate sort expression: Int →
  Int
-/
#guard_msgs in
example : (1 : Int) = 1 := by z3_local

end Tests.Z3LocalUntranslatable
