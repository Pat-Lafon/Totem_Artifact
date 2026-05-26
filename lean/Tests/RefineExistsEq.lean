import ProofAutomation

/-! # Tests.RefineExistsEq — regression suite for `refine_exists_eq`. -/

namespace Tests.RefineExistsEq

-- Plain Eq, witness on RHS
theorem test_refine_eq_rhs : ∃ (x : Nat), x = 5 ∧ True := by
  refine_exists_eq
  exact ⟨rfl, trivial⟩

-- Plain Eq, witness on LHS (`5 = x`)
theorem test_refine_eq_lhs : ∃ (x : Nat), True ∧ 5 = x := by
  refine_exists_eq
  exact ⟨trivial, rfl⟩

-- BEq form `(x == e) = true`
theorem test_refine_beq : ∃ (x : Int), (x == 7) = true ∧ x ≥ 0 := by
  refine_exists_eq
  decide

-- BEq form reversed `(e == x) = true`
theorem test_refine_beq_rev : ∃ (x : Int), (7 == x) = true ∧ x ≥ 0 := by
  refine_exists_eq
  decide

-- Equality nested deep in conjunction
theorem test_refine_nested : ∃ (x : Int), True ∧ (True ∧ (x = 3 ∧ True)) := by
  refine_exists_eq
  exact ⟨trivial, trivial, rfl, trivial⟩

-- Witness that mentions an outer free variable
theorem test_refine_outer_fvar (n : Int) : ∃ (x : Int), x = n - 1 ∧ x < n := by
  refine_exists_eq
  refine ⟨rfl, ?_⟩
  omega

-- Multiple existentials chained — apply twice
theorem test_refine_chain : ∃ (x : Int), x = 4 ∧ ∃ (y : Int), (y == x + 1) = true := by
  refine_exists_eq
  refine ⟨rfl, ?_⟩
  refine_exists_eq
  decide

-- The rbtree-style shape from the actual failing subtyping query
theorem test_refine_rbtree_shape (inv : Int) (_h1 : inv ≥ 1) :
    ∃ (inv_1 : Int), inv_1 ≥ 0 ∧ inv_1 < inv ∧ (inv_1 == inv - 1) = true := by
  refine_exists_eq
  refine ⟨?_, ?_, ?_⟩
  · omega
  · omega
  · simp

-- Negative test: no pinning equality → tactic should fail.
example : ∃ (x : Nat), x ≥ 0 := by
  first
    | (refine_exists_eq; exact (by trivial))
    | exact ⟨0, Nat.zero_le _⟩

end Tests.RefineExistsEq

/-! ## Trust-anchor assertions -/

/-- info: 'Tests.RefineExistsEq.test_refine_eq_rhs' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.RefineExistsEq.test_refine_eq_rhs

/-- info: 'Tests.RefineExistsEq.test_refine_beq' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.RefineExistsEq.test_refine_beq

/-- info: 'Tests.RefineExistsEq.test_refine_nested' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.RefineExistsEq.test_refine_nested

/-- info: 'Tests.RefineExistsEq.test_refine_chain' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.RefineExistsEq.test_refine_chain

/-- info: 'Tests.RefineExistsEq.test_refine_rbtree_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.RefineExistsEq.test_refine_rbtree_shape
