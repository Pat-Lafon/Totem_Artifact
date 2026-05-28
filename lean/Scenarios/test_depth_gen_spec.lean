-- Failed subtyping query for integration_tests/depth_tree/subtyping_tests/depth_gen_spec.ml
-- Verbatim copy of integration_tests/depth_tree/encoding_dumps/depth_gen_spec/query_1.lean
-- (query_0 is trivially `∀ v : Int, 0 ≤ v → 0 ≤ v` — its appearance as a failed dump is
--  a separate anomaly worth investigating on its own).
-- subtype-check verdict: false. Reproducer lives in TODO.md.
-- To debug: prove or find a counterexample for the theorem below.

import ProofAutomation

-- Preamble for failed subtyping queries (itree only)

inductive itree where
  | Leaf
  | Node (value : Int) (left : itree) (right : itree)
  deriving DecidableEq, Repr, Plausible.Arbitrary

@[simp, grind =] def is_leaf : itree → Bool
  | .Leaf => true
  | .Node _ _ _ => false

@[simp, grind =] def is_node : itree → Bool
  | .Leaf => false
  | .Node _ _ _ => true

@[simp, grind =] def value : itree → Option Int
  | .Leaf => none
  | .Node v _ _ => some v

@[simp, grind =] def left : itree → Option itree
  | .Leaf => none
  | .Node _ l _ => some l

@[simp, grind =] def right : itree → Option itree
  | .Leaf => none
  | .Node _ _ r => some r

def depth_impl : itree → Int
  | .Leaf => 0
  | .Node _ l r =>
      if depth_impl l > depth_impl r then 1 + depth_impl l
      else                                1 + depth_impl r

def depth (t : itree) (res : Int) : Prop :=
  depth_impl t = res

def complete_impl : itree → Bool
  | .Leaf => true
  | .Node _ l r =>
      complete_impl l && complete_impl r && (depth_impl l == depth_impl r)

def complete (t : itree) (res : Bool) : Prop :=
  complete_impl t = res

def lower_bound_impl : itree → Int → Bool
  | .Leaf, _ => true
  | .Node y l r, x => decide (x ≤ y) && lower_bound_impl l x && lower_bound_impl r x

def lower_bound (t : itree) (x : Int) (res : Bool) : Prop :=
  lower_bound_impl t x = res

def upper_bound_impl : itree → Int → Bool
  | .Leaf, _ => true
  | .Node y l r, x => decide (y ≤ x) && upper_bound_impl l x && upper_bound_impl r x

def upper_bound (t : itree) (x : Int) (res : Bool) : Prop :=
  upper_bound_impl t x = res

def bst_impl : itree → Bool
  | .Leaf => true
  | .Node x l r => bst_impl l && bst_impl r && upper_bound_impl l x && lower_bound_impl r x

def bst (t : itree) (res : Bool) : Prop :=
  bst_impl t = res

-- Axiom section: definitions available to grind/simp for proving axioms.
-- lean_dump.ml emits 'end Axioms' after the axioms, before the subtyping query.
section Axioms
  attribute [local simp] is_leaf is_node value left right
    depth_impl depth complete_impl complete
    lower_bound_impl lower_bound
    upper_bound_impl upper_bound
    bst_impl bst
  attribute [local grind cases] itree Bool
  attribute [local grind =] is_leaf is_node value left right
    depth_impl depth complete_impl complete
    lower_bound_impl lower_bound
    upper_bound_impl upper_bound
    bst_impl bst

theorem ax_0 : ∀ (t : itree), (∀ (n : Int), ((depth t n) → (n >= 0))) := by
  prove_axiom

grind_pattern ax_0 => depth t n

-- Bridge: additional trigger keyed on the impl. Whenever grind sees a bare
-- `depth_impl t` in the proof state (e.g. after `[grind =]` unfolding of the
-- wrapper, or in goals that mention the impl directly), this lemma asserts
-- `depth t (depth_impl t)` as a fact, which then enables ax_0 (and any other
-- wrapper-keyed axiom about depth) to fire with `n := depth_impl t`.
-- Empirically, the wrapper-keyed pattern above is still load-bearing — ax_3
-- fails to close via prove_axiom if removed — so this is purely additive.
theorem depth_intro (t : itree) : depth t (depth_impl t) := rfl
grind_pattern depth_intro => depth_impl t

theorem complete_intro (t : itree) : complete t (complete_impl t) := rfl
grind_pattern complete_intro => complete_impl t

theorem lower_bound_intro (t : itree) (x : Int) :
    lower_bound t x (lower_bound_impl t x) := rfl
grind_pattern lower_bound_intro => lower_bound_impl t x

theorem upper_bound_intro (t : itree) (x : Int) :
    upper_bound t x (upper_bound_impl t x) := rfl
grind_pattern upper_bound_intro => upper_bound_impl t x

theorem bst_intro (t : itree) : bst t (bst_impl t) := rfl
grind_pattern bst_intro => bst_impl t

theorem ax_1 : ∀ (t : itree), (∀ (res : Int), ((depth t res) → ((is_leaf t) → (0 == res)))) := by
  prove_axiom

theorem ax_2 : ∀ (t : itree), (∀ (res : Int), ((is_leaf t) → ((0 == res) → (depth t res)))) := by
  prove_axiom

theorem ax_3 : ∀ (t : itree), (∀ (res : Int), ((depth t res) → ((0 == res) → (is_leaf t)))) := by
  prove_axiom

theorem ax_4 : ∀ (t : itree), (∀ (res : Int), ((is_leaf t) → ((depth t res) → (0 == res)))) := by
  prove_axiom

theorem ax_5 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), ((∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ (res_0 > res_1)))) → ((depth l res_0) → ((1 + res_0) == res)))))))))) := by
  prove_axiom

theorem ax_6 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), ((∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ (res_0 > res_1)))) → ((depth l res_0) → (((1 + res_0) == res) → (depth t res)))))))))) := by
  prove_axiom

theorem ax_7 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), (∃ (res_0 : Int), ((∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ (res_0 > res_1)))) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((depth t res) → ((depth l res_0) ∧ ((1 + res_0) == res)))))))))) := by
  prove_axiom

theorem ax_8 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((((depth l res_0) ∧ ((depth r res_1) ∧ ¬(res_0 > res_1))) ∧ (depth r res_1)) → ((1 + res_1) == res)))))))))) := by
  prove_axiom

theorem ax_9 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((((depth l res_0) ∧ ((depth r res_1) ∧ ¬(res_0 > res_1))) ∧ (depth r res_1)) → (((1 + res_1) == res) → (depth t res)))))))))) := by
  intro t
  cases t with
  | Leaf => grind
  | Node v' l' r' =>
    intros v l r res h1
    simp_hyps
    simp_goal

theorem ax_10 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), (∃ (res_0 : Int), (∃ (res_1 : Int), (((depth l res_0) ∧ ((depth r res_1) ∧ ¬(res_0 > res_1))) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((depth t res) → ((depth r res_1) ∧ ((1 + res_1) == res))))))))))) := by
  intro t
  cases t with
  | Leaf =>
    intros v l r res
    refine ⟨?_, ?_ ⟩; rotate_left
    refine ⟨?_, ?_ ⟩; rotate_left
    grind
    all_goals constructor; constructor
  | Node v' l' r' =>
    intros v l r res
    simp
    simp_goal

theorem ax_11 : ∀ (t : itree), (∀ (res : Int), (∀ (res2 : Int), ((depth t res) → ((depth t res2) → (res2 == res))))) := by
  prove_axiom

theorem ax_12 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ ((res_0 > res_1) → ((1 + res_0) == res)))))))))))) := by
  prove_axiom

theorem ax_13 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ (¬(res_0 > res_1) → ((1 + res_1) == res)))))))))))) := by
  prove_axiom

theorem ax_14 : ∀ (t : itree), (∀ (res : Int), ((depth t res) → ((res > 0) → (is_node t)))) := by
  prove_axiom

end Axioms

auto_pbt_decidable

theorem failed_subtyping_1 : ∀ (s : Int), ((0 <= s) → (∀ (v : itree), ((∃ (x_0 : Bool), (((x_0) → (s == 0)) ∧ (((s == 0) → (x_0)) ∧ ((¬(x_0) → (s > 0)) ∧ (((s > 0) → ¬(x_0)) ∧ (((x_0) ∧ ((is_leaf v) ∧ (depth v 0))) ∨ (¬(x_0) ∧ (∃ (x_1 : Bool), (((x_1) ∧ ((is_leaf v) ∧ (depth v 0))) ∨ (¬(x_1) ∧ (∃ (s_2 : Int), (∃ (lt : itree), (∃ (u1 : Int), (∃ (s_3 : Int), (∃ (rt : itree), (∃ (u2 : Int), (∃ (n : Int), ((0 <= s_2) ∧ ((s_2 >= 0) ∧ ((s_2 < s) ∧ ((s_2 == (s - 1)) ∧ ((depth lt u1) ∧ ((u1 <= s_2) ∧ ((0 <= s_3) ∧ ((s_3 >= 0) ∧ ((s_3 < s) ∧ ((s_3 == (s - 1)) ∧ ((depth rt u2) ∧ ((u2 <= s_3) ∧ ((is_node v) ∧ (((value v) == n) ∧ (((left v) == lt) ∧ ((right v) == rt))))))))))))))))))))))))))))))))) → (∃ (x_0 : Bool), (∃ (u : Int), (((x_0) → (s == 0)) ∧ (((s == 0) → (x_0)) ∧ ((¬(x_0) → (s > 0)) ∧ (((s > 0) → ¬(x_0)) ∧ ((depth v u) ∧ (u <= s))))))))))) := by
  intros s h1 v h2
  simp_hyps
  simp_goal
  by_cases h2: x_0
  · simp_hyps
    refine ⟨true, 0, ?_⟩
    grind
  · simp_hyps
    by_cases h2: x_1
    · simp_hyps
      refine ⟨false, 0, ?_ ⟩
      simp
      cases v with
      | Node => grind
      | Leaf =>
        clear h
        grind
    · simp_hyps
      subst_vars
      cases v with
      | Leaf => grind
      | Node v l r =>
        simp_hyps
        refine ⟨(s = 0), ?_ ⟩; rotate_left
        refine ⟨s, ?_ ⟩
        simp_goal
        propose_counterexample 42
        sorry
-- spec-bug refutation candidate for `failed_subtyping_1`
example : ¬ (∀ (s : Int),
  0 ≤ s →
    ∀ (v : itree),
      (∃ x_0,
          (x_0 = true → (s == 0) = true) ∧
            ((s == 0) = true → x_0 = true) ∧
              (¬x_0 = true → s > 0) ∧
                (s > 0 → ¬x_0 = true) ∧
                  (x_0 = true ∧ is_leaf v = true ∧ depth v 0 ∨
                    ¬x_0 = true ∧
                      ∃ x_1,
                        x_1 = true ∧ is_leaf v = true ∧ depth v 0 ∨
                          ¬x_1 = true ∧
                            ∃ s_2 lt u1 s_3 rt u2 n,
                              0 ≤ s_2 ∧
                                s_2 ≥ 0 ∧
                                  s_2 < s ∧
                                    (s_2 == s - 1) = true ∧
                                      depth lt u1 ∧
                                        u1 ≤ s_2 ∧
                                          0 ≤ s_3 ∧
                                            s_3 ≥ 0 ∧
                                              s_3 < s ∧
                                                (s_3 == s - 1) = true ∧
                                                  depth rt u2 ∧
                                                    u2 ≤ s_3 ∧
                                                      is_node v = true ∧
                                                        (value v == some n) = true ∧
                                                          (left v == some lt) = true ∧ (right v == some rt) = true)) →
        ∃ x_0 u,
          (x_0 = true → (s == 0) = true) ∧
            ((s == 0) = true → x_0 = true) ∧ (¬x_0 = true → s > 0) ∧ (s > 0 → ¬x_0 = true) ∧ depth v u ∧ u ≤ s) := by
  intro H
  have H1 := H 2 (by first | native_decide | grind) (itree.Node 0 itree.Leaf itree.Leaf) 
  sorry
