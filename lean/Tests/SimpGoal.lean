import ProofAutomation

/-! # Tests.SimpGoal — regression suite for `simp_goal`. -/

namespace Tests.SimpGoal

theorem test_simp_goal_and : True ∧ True ∧ True := by
  simp_goal

-- simp_goal should witness ∃ goals via pinning equalities.
theorem test_simp_goal_refines_exists (inv : Int) (_h1 : inv ≥ 1) :
    ∃ (x : Int), x ≥ 0 ∧ x < inv ∧ (x == inv - 1) = true := by
  simp_goal

-- Disjunction whose left side reduces to False — pick right.
theorem test_simp_goal_picks_disjunct : False ∨ True := by
  simp_goal

-- Composed shape: ∃-witness inside a ∨-branch with a ∧-split. Exercises
-- the phase-loop interaction (the three primitives chained, not just
-- isolated like the tests above).
theorem test_simp_goal_nested (inv : Int) (_h1 : inv ≥ 1) :
    ∃ (x : Int), ((x == inv - 1) = true ∧ x ≥ 0) ∨ False := by
  simp_goal

-- Pinning equality lives in an implication premise (not an `∧` conjunct).
-- Picking the witness reduces the premise to `e = e`; grind discharges.
theorem test_simp_goal_exists_under_impl (e : Int) (P : Int → Prop) (hP : P e) :
    ∃ (x : Int), x = e → P x := by
  simp_goal

-- Pinning equalities for nested existentials live across multiple premises
-- of a `→`-chain. Mirrors the shape of failed depth_tree axioms.
theorem test_simp_goal_exists_under_impl_chain
    (e1 e2 : Int) (P : Int → Int → Prop) (hP : P e1 e2) :
    ∃ (x y : Int), x = e1 → y = e2 → P x y := by
  simp_goal

-- Regression: bivalued existential. The body pins `x_0` on BOTH polarities
-- (`x_0 = true → …` AND `¬ x_0 = true → …` premises), so the existential is
-- case-split, not pinned. `simp_goal` must NOT commit to `x_0 := true` —
-- that would make `¬ True → s > 0` vacuous and lose the `s > 0` branch.
-- The `bvarAppearsUnderNot` guard in `refineExistsEqImpl` blocks the
-- speculative refinement; the manual `by_cases` then discharges.
-- Mirrors the shape that surfaces after `simp_hyps` in
-- `Scenarios/test_depth_gen_spec.lean`'s `failed_subtyping_1`.
theorem test_simp_goal_preserves_bivalued_exists
    (s : Int) (_h : 0 ≤ s) :
    ∃ (x_0 : Bool),
      (x_0 = true → (s == 0) = true) ∧
      ((s == 0) = true → x_0 = true) ∧
      (¬ x_0 = true → s > 0) ∧
      (s > 0 → ¬ x_0 = true) := by
  simp_goal
  by_cases hs : s = 0
  · exact ⟨true, by grind⟩
  · exact ⟨false, by grind⟩

-- Nested variant mirroring the `failed_subtyping_1` shape in
-- `Scenarios/test_depth_gen_spec.lean`: the bivalued bvar lives inside an
-- outer `∃ x_0`, and there's a *second* existential `∃ u` immediately
-- under it whose pinning equality (`depth v u`) is independent. The check
-- must still reject refining `x_0`, even though `u` is locally pinned.
theorem test_simp_goal_preserves_bivalued_nested_exists
    (s : Int) (_h : 0 ≤ s) (v : Int) :
    ∃ (x_0 : Bool) (u : Int),
      (x_0 = true → (s == 0) = true) ∧
      ((s == 0) = true → x_0 = true) ∧
      (¬ x_0 = true → s > 0) ∧
      (s > 0 → ¬ x_0 = true) ∧
      u = v ∧ u ≤ s + v := by
  simp_goal
  by_cases hs : s = 0
  · exact ⟨true, v, by grind⟩
  · exact ⟨false, v, by grind⟩

-- Negated *inequality* must not trip the bivalued-Eq guard: `¬ x > y` is a
-- premise that doesn't pin `x` to any specific value, so `refine_exists_eq`
-- should still pick the witness from the unconditional `x = e` conjunct.
-- Mirrors ax_9-style bodies (`(depth l x ∧ depth r y ∧ ¬ x > y) ∧ … → …`)
-- in `Scenarios/test_depth_gen_spec.lean`.
theorem test_simp_goal_refines_under_negated_inequality
    (e : Int) (P : Int → Prop) (hP : P e) :
    ∃ (x : Int), (x = e ∧ ¬ x > 5) → P x := by
  simp_goal

-- Pinning equality is hidden inside a `@[simp]` predicate definition.
-- `simp_goal`'s `trySimpUnfold` phase exposes `f t = res` so
-- `refine_exists_eq` can witness. Mirrors the shape of ax_9 in
-- `Scenarios/test_depth_gen_spec.lean` (∃ res, P t res where P is a
-- function-result predicate).
section UnfoldExists
  @[simp] def fimpl (n : Int) : Int := n + 1
  @[simp] def fpred (n res : Int) : Prop := fimpl n = res

  theorem test_simp_goal_unfolds_predicate_def (n : Int) :
      ∃ (res : Int), fpred n res := by
    simp_goal
end UnfoldExists

end Tests.SimpGoal

/-! ## Trust-anchor assertions -/

/-- info: 'Tests.SimpGoal.test_simp_goal_and' depends on axioms: [propext] -/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_and

/-- info: 'Tests.SimpGoal.test_simp_goal_refines_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_refines_exists

/-- info: 'Tests.SimpGoal.test_simp_goal_picks_disjunct' depends on axioms: [propext] -/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_picks_disjunct

/-- info: 'Tests.SimpGoal.test_simp_goal_nested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_nested

/-- info: 'Tests.SimpGoal.test_simp_goal_exists_under_impl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_exists_under_impl

/-- info: 'Tests.SimpGoal.test_simp_goal_exists_under_impl_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_exists_under_impl_chain

/-- info: 'Tests.SimpGoal.test_simp_goal_unfolds_predicate_def' depends on axioms: [propext] -/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_unfolds_predicate_def

/-- info: 'Tests.SimpGoal.test_simp_goal_preserves_bivalued_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_preserves_bivalued_exists

/--
info: 'Tests.SimpGoal.test_simp_goal_preserves_bivalued_nested_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_preserves_bivalued_nested_exists

/--
info: 'Tests.SimpGoal.test_simp_goal_refines_under_negated_inequality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Tests.SimpGoal.test_simp_goal_refines_under_negated_inequality
