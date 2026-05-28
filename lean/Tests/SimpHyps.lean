import ProofAutomation

/-! # Tests.SimpHyps — regression suite for `simp_hyps`. -/

namespace Tests.SimpHyps

-- irbtree fixture used by the user-predicate cases below. `is_rbtleaf` is
-- intentionally *not* `@[simp]` (anchors the "non-toUnfold defs pass through
-- freely" path). `is_rbtnode`/`color` are accessor-shaped `@[simp]` defs
-- (anchor the "unfold on a constructor reduces cleanly" path).
-- `num_black_impl` is structurally recursive `@[simp]` def (anchors the
-- "reject recursive defs even on a constructor" path).
inductive irbtree where
  | Rbtleaf
  | Rbtnode (color : Bool) (left : irbtree) (value : Int) (right : irbtree)
def is_rbtleaf : irbtree → Bool | .Rbtleaf => true | .Rbtnode _ _ _ _ => false
@[simp] def is_rbtnode : irbtree → Bool
  | .Rbtleaf => false | .Rbtnode _ _ _ _ => true
@[simp] def color : irbtree → Option Bool
  | .Rbtleaf => none | .Rbtnode c _ _ _ => some c
@[simp] def num_black_impl : irbtree → Int → Bool
  | .Rbtleaf, n => n == 0
  | .Rbtnode _ l _ r, n => num_black_impl l (n - 1) && num_black_impl r (n - 1)

-- Destructs ∧.
theorem test_simp_hyps_and : ∀ (a b : Prop), a ∧ b → a := by
  intros a b h
  simp_hyps
  assumption

-- Normalizes BEq, then subst's `n := 0` (numeric literal qualifies as "simple"
-- for tryNormalize's subst gate via the OfNat-app recognizer).
theorem test_simp_hyps_beq : ∀ (n : Int), (n == 0) = true → n = 0 := by
  intros n h
  simp_hyps
  rfl

-- Normalizes flipped BEq (lit on LHS). Regression for the `eq_comm` fix
-- that lets `simp only` make progress on `true = (a == b)` / `false = (a == b)`.
theorem test_simp_hyps_beq_flipped_true : ∀ (n : Int), true = (n == 0) → n = 0 := by
  intros n h
  simp_hyps
  rfl

theorem test_simp_hyps_beq_flipped_false : ∀ (n : Int), false = (n == 0) → n ≠ 0 := by
  intros n h
  simp_hyps
  assumption

-- Specializes implications.
theorem test_simp_hyps_specialize : ∀ (p q : Prop), p → (p → q) → q := by
  intros p q hp hpq
  simp_hyps
  assumption

-- Clears contradicted implications.
theorem test_simp_hyps_clear_neg : ∀ (p q : Prop), p → (¬p → q) → p := by
  intros p q hp hnpq
  simp_hyps
  assumption

-- Pure-boolean disjunction whose `true = true` side collapses (mirrors
-- h_71-shape from rbtree subtyping queries).
theorem test_simp_hyps_pure_bool_disjunct
    (c c' : Bool) (res_6 res_7 : Bool)
    (h : (¬c = true ∧ ¬c' = true ∧ res_6 = true ∧ res_7 = true) ∧ true = true ∨
         ¬(¬c = true ∧ ¬c' = true ∧ res_6 = true ∧ res_7 = true) ∧ ¬true = true) :
    res_6 = true := by
  simp_hyps
  rfl

-- `is_rbtleaf` is not `@[simp]`-marked, so it's not in the simp set's
-- `toUnfold`; `safeForSimp` admits the hypothesis trivially but `simp at h`
-- has no rewrite to fire and reports "no progress". Hypothesis stays put.
theorem test_simp_hyps_skips_non_simp_def (t : irbtree) (h : is_rbtleaf t = true) :
    is_rbtleaf t = true := by
  simp_hyps
  assumption

-- `@[simp]` def applied to a constructor → simp's def-unfold + iota fire
-- cleanly, then the chain of bool/eq normalizations turns `h` into
-- `c = false`. `subst c` propagates through the goal, leaving `false = false`.
theorem test_simp_hyps_unfolds_on_ctor (c : Bool) (l : irbtree) (v : Int) (r : irbtree)
    (h : ¬(is_rbtnode (irbtree.Rbtnode c l v r) = true ∧
           (color (irbtree.Rbtnode c l v r) == some true) = true)) :
    c = false := by
  simp_hyps
  rfl

-- `@[simp]` def applied to a free variable → `safeForSimp` rejects (no
-- constructor-headed arg, so a simp unfold would leave a `match`-on-fvar in
-- `h`). The hypothesis is preserved verbatim; if simp had fired,
-- `Bool.not_eq_true` would have rewritten `h` to `is_rbtnode v = false` —
-- not defEq to the goal `¬(is_rbtnode v = true)`, so `exact h` would fail.
theorem test_simp_hyps_rejects_unfold_on_fvar (v : irbtree)
    (h : ¬(is_rbtnode v = true)) : ¬(is_rbtnode v = true) := by
  simp_hyps
  exact h

-- `safeForSimp` still rejects the hypothesis (it mentions `is_rbtnode v`),
-- but the narrow logical-connective fallback collapses the `true = true ∧ _ ∨
-- ¬true = true ∧ _` skeleton without unfolding any def. Mirrors the residue
-- left after `intros` on Cobb-dumped subtyping queries (depth_gen_spec).
theorem test_simp_hyps_logical_fallback_under_fvar_unfold
    (v : irbtree)
    (h : true = true ∧ is_rbtnode v = true ∨ ¬true = true ∧ False) :
    is_rbtnode v = true := by
  simp_hyps
  exact h

-- Recursive `@[simp]` def (structural recursion, compiled via
-- `irbtree.brecOn`) → rejected even when the principal arg is a
-- constructor, because one unfold step exposes recursive calls on `l`/`r`
-- and-splits via `Bool.and_eq_true`, mangling `h`'s shape.
theorem test_simp_hyps_rejects_recursive_simp_def
    (c : Bool) (l : irbtree) (val : Int) (r : irbtree) (n : Int)
    (h : num_black_impl (irbtree.Rbtnode c l val r) n = true) :
    num_black_impl (irbtree.Rbtnode c l val r) n = true := by
  simp_hyps
  exact h

-- Resolves an `ite` in a hypothesis when another hyp pins the condition.
-- `h_lt : a < b` flips to defeq-match the ite's `b > a` condition; `if_pos`
-- collapses `h1` to the then-branch.
theorem test_simp_hyps_ite_pos (a b : Int) (h_lt : a < b)
    (h1 : (if b > a then 1 + b else 1 + a) = 0) :
    1 + b = 0 := by
  simp_hyps
  exact h1

-- Negative-condition counterpart: `h_le : a ≤ b` lets `simp_hyps` discharge
-- `if a > b` via `if_neg`, collapsing to the else-branch.
theorem test_simp_hyps_ite_neg (a b : Int) (h_le : a ≤ b)
    (h1 : (if a > b then 1 + a else 1 + b) = 0) :
    1 + b = 0 := by
  simp_hyps
  exact h1

-- Clears a hypothesis implied by the rest of the lctx. Neither
-- `0 ≤ h - 1 + (h - 1) + 1` nor `h - 1 + (h - 1) + 1 < h + h` are tautologies
-- in isolation (both fail at `h = 0`), but both follow from `h > 0`. The
-- empty-context probe in `tryClearTrivial` rejects them; `tryClearRedundant`
-- catches them via `grind` against the rest of the context.
set_option linter.unusedVariables false in
theorem test_simp_hyps_clear_redundant_arith (h : Int) (hpos : h > 0)
    (hred_lo : 0 ≤ h - 1 + (h - 1) + 1) (hred_hi : h - 1 + (h - 1) + 1 < h + h) :
    h > 0 := by
  simp_hyps
  fail_if_success exact hred_lo
  fail_if_success exact hred_hi
  exact hpos

end Tests.SimpHyps

/-! ## Trust-anchor assertions -/

/-- info: 'Tests.SimpHyps.test_simp_hyps_and' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_and

/-- info: 'Tests.SimpHyps.test_simp_hyps_beq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_beq

/-- info: 'Tests.SimpHyps.test_simp_hyps_beq_flipped_true' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_beq_flipped_true

/-- info: 'Tests.SimpHyps.test_simp_hyps_beq_flipped_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_beq_flipped_false

/-- info: 'Tests.SimpHyps.test_simp_hyps_specialize' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_specialize

/-- info: 'Tests.SimpHyps.test_simp_hyps_clear_neg' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_clear_neg

/-- info: 'Tests.SimpHyps.test_simp_hyps_unfolds_on_ctor' depends on axioms: [propext] -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_unfolds_on_ctor

/-- info: 'Tests.SimpHyps.test_simp_hyps_rejects_unfold_on_fvar' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_rejects_unfold_on_fvar

/-- info: 'Tests.SimpHyps.test_simp_hyps_logical_fallback_under_fvar_unfold' depends on axioms: [propext] -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_logical_fallback_under_fvar_unfold

/-- info: 'Tests.SimpHyps.test_simp_hyps_rejects_recursive_simp_def' does not depend on any axioms -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_rejects_recursive_simp_def

/-- info: 'Tests.SimpHyps.test_simp_hyps_clear_redundant_arith' depends on axioms: [propext] -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_clear_redundant_arith

/-- info: 'Tests.SimpHyps.test_simp_hyps_ite_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_ite_pos

/-- info: 'Tests.SimpHyps.test_simp_hyps_ite_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Tests.SimpHyps.test_simp_hyps_ite_neg
