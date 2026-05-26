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
