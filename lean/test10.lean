import ProofAutomation

-- Mechanically constructed from the Cobb subtyping_temp_file.smt2
-- to investigate encoding differences between Lean Z3 tactic and Cobb Z3 output.
--
-- This file contains TWO versions of the same subtyping goal:
--   1. "simplified" — with direct arithmetic (inv - 1), (h - 1), matching
--      what Cobb's layout_prop_to_lean produces (existentials simplified by smart_sigma)
--   2. "unsimplified" — with fresh existential variables inv_1, h_0, etc,
--      matching what appears in the Cobb SMT dump (subtyping_temp_file.smt2)
--
-- If z3_auto succeeds on the simplified version but fails on the unsimplified
-- version, that confirms the encoding difference is the root cause.

inductive irbtree where
  | Rbtleaf
  | Rbtnode (color : Bool) (left : irbtree) (value : Int) (right : irbtree)
  deriving DecidableEq

@[simp, grind =] def is_rbtleaf : irbtree → Bool
  | .Rbtleaf => true
  | .Rbtnode _ _ _ _ => false

@[simp, grind =] def is_rbtnode : irbtree → Bool
  | .Rbtleaf => false
  | .Rbtnode _ _ _ _ => true

@[simp, grind =] def color : irbtree → Option Bool
  | .Rbtleaf => none
  | .Rbtnode c _ _ _ => some c

@[simp, grind =] def value : irbtree → Option Int
  | .Rbtleaf => none
  | .Rbtnode _ _ v _ => some v

@[simp, grind =] def left : irbtree → Option irbtree
  | .Rbtleaf => none
  | .Rbtnode _ l _ _ => some l

@[simp, grind =] def right : irbtree → Option irbtree
  | .Rbtleaf => none
  | .Rbtnode _ _ _ r => some r

def num_black_impl : irbtree → Int → Bool
  | .Rbtleaf, h => h == 0
  | .Rbtnode c l _ r, h =>
    if ¬c then num_black_impl l (h - 1) && num_black_impl r (h - 1)
    else num_black_impl l h && num_black_impl r h

def num_black (t : irbtree) (h : Int) (res : Bool) : Prop :=
  num_black_impl t h = res

def no_red_red_impl : irbtree → Bool
  | .Rbtleaf => true
  | .Rbtnode c l _ r =>
    if ¬c then no_red_red_impl l && no_red_red_impl r
    else
      match l, r with
      | .Rbtnode c' _ _ _, .Rbtnode c'' _ _ _ =>
          !c' && !c'' && no_red_red_impl l && no_red_red_impl r
      | .Rbtnode c' _ _ _, .Rbtleaf => !c' && no_red_red_impl l
      | .Rbtleaf, .Rbtnode c'' _ _ _ => !c'' && no_red_red_impl r
      | .Rbtleaf, .Rbtleaf => true

def no_red_red (t : irbtree) (res : Bool) : Prop :=
  no_red_red_impl t = res

section Axioms
  attribute [local simp] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red
  attribute [local grind cases] irbtree Bool
  attribute [local grind =] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red

-- Axioms from the Cobb SMT file (translated to Lean propositions).
-- These are the same axioms that appear in both the .smt2 and .lean dumps.

-- num_black leaf cases
theorem ax_num_black_leaf_fwd : ∀ (t : irbtree) (h : Int) (res : Bool),
    (num_black t h res) → (is_rbtleaf t = true) →
    ((h = 0 ∧ res = true) ∨ (¬(h = 0) ∧ res = false)) := by prove_axiom

theorem ax_num_black_leaf_bwd : ∀ (t : irbtree) (h : Int) (res : Bool),
    (is_rbtleaf t = true) →
    ((h = 0 ∧ res = true) ∨ (¬(h = 0) ∧ res = false)) →
    (num_black t h res) := by prove_axiom

-- no_red_red leaf cases
theorem ax_no_red_red_leaf_fwd : ∀ (t : irbtree) (res : Bool),
    (no_red_red t res) → (is_rbtleaf t = true) → (true = res) := by prove_axiom

theorem ax_no_red_red_leaf_bwd : ∀ (t : irbtree) (res : Bool),
    (is_rbtleaf t = true) → (true = res) → (no_red_red t res) := by prove_axiom

-- no_red_red black node (color = false)
theorem ax_no_red_red_black_fwd : ∀ (t : irbtree) (c : Bool) (l r : irbtree) (res : Bool),
    (no_red_red t res) →
    (is_rbtnode t = true) → (color t = some c) → (left t = some l) → (right t = some r) →
    (¬c = true) →
    ∃ (res_4 : Bool), (no_red_red l res_4) ∧
      ∃ (res_5 : Bool), (no_red_red r res_5) ∧
        ((res_4 = true ∧ res_5 = true ∧ res = true) ∨ (¬(res_4 = true ∧ res_5 = true) ∧ res = false)) := by
  prove_axiom

theorem ax_no_red_red_black_bwd : ∀ (t : irbtree) (c : Bool) (l r : irbtree) (res : Bool),
    (is_rbtnode t = true) → (color t = some c) → (left t = some l) → (right t = some r) →
    (¬c = true) →
    (∃ (res_4 : Bool), (no_red_red l res_4) ∧
      (∃ (res_5 : Bool), (no_red_red r res_5) ∧
        ((res_4 = true ∧ res_5 = true ∧ res = true) ∨ (¬(res_4 = true ∧ res_5 = true) ∧ res = false)))) →
    (no_red_red t res) := by prove_axiom

-- num_black black node (color = false)
theorem ax_num_black_black_fwd : ∀ (t : irbtree) (h : Int) (c : Bool) (l r : irbtree) (res : Bool),
    (num_black t h res) →
    (is_rbtnode t = true) → (color t = some c) → (left t = some l) → (right t = some r) →
    (¬c = true) →
    ∃ (res_0 : Bool), (num_black l (h - 1) res_0) ∧
      ∃ (res_1 : Bool), (num_black r (h - 1) res_1) ∧
        ((res_0 = true ∧ res_1 = true ∧ res = true) ∨ (¬(res_0 = true ∧ res_1 = true) ∧ res = false)) := by
  prove_axiom

theorem ax_num_black_black_bwd : ∀ (t : irbtree) (h : Int) (c : Bool) (l r : irbtree) (res : Bool),
    (is_rbtnode t = true) → (color t = some c) → (left t = some l) → (right t = some r) →
    (¬c = true) →
    (∃ (res_0 : Bool), (num_black l (h - 1) res_0) ∧
      (∃ (res_1 : Bool), (num_black r (h - 1) res_1) ∧
        ((res_0 = true ∧ res_1 = true ∧ res = true) ∨ (¬(res_0 = true ∧ res_1 = true) ∧ res = false)))) →
    (num_black t h res) := by prove_axiom

-- num_black red node (color = true)
theorem ax_num_black_red_fwd : ∀ (t : irbtree) (h : Int) (c : Bool) (l r : irbtree) (res : Bool),
    (num_black t h res) →
    (is_rbtnode t = true) → (color t = some c) → (left t = some l) → (right t = some r) →
    (c = true) →
    ∃ (res_2 : Bool), (num_black l h res_2) ∧
      ∃ (res_3 : Bool), (num_black r h res_3) ∧
        ((res_2 = true ∧ res_3 = true ∧ res = true) ∨ (¬(res_2 = true ∧ res_3 = true) ∧ res = false)) := by
  prove_axiom

theorem ax_num_black_red_bwd : ∀ (t : irbtree) (h : Int) (c : Bool) (l r : irbtree) (res : Bool),
    (is_rbtnode t = true) → (color t = some c) → (left t = some l) → (right t = some r) →
    (c = true) →
    (∃ (res_2 : Bool), (num_black l h res_2) ∧
      (∃ (res_3 : Bool), (num_black r h res_3) ∧
        ((res_2 = true ∧ res_3 = true ∧ res = true) ∨ (¬(res_2 = true ∧ res_3 = true) ∧ res = false)))) →
    (num_black t h res) := by prove_axiom

-- num_black h >= 0
@[grind →]
theorem ax_num_black_nonneg : ∀ (t : irbtree) (h : Int),
    (num_black t h true) → (h ≥ 0) := by prove_axiom

grind_pattern ax_num_black_nonneg => num_black_impl t h

-- num_black 0 red means color is true
theorem ax_num_black_0_red : ∀ (c : Bool) (l : irbtree) (v : Int) (r : irbtree),
    (num_black (irbtree.Rbtnode c l v r) 0 true) → (c = true) := by prove_axiom

-- no_red_red proposed: black node with subtrees both true
theorem ax_no_red_red_proposed : ∀ (t : irbtree) (_c : Bool) (l r : irbtree) (v : Int),
    (no_red_red l true) → (no_red_red r true) →
    (is_rbtnode t = true) → (color t = some false) →
    (left t = some l) → (right t = some r) → (value t = some v) →
    (no_red_red t true) := by prove_axiom

end Axioms

-- ============================================================
-- VERSION 1: Simplified goal (matching Lean Z3 tactic output)
-- Existentials inv_1, h_0, inv_2, h_1 eliminated via substitution
-- ============================================================

axiom goal_simplified :
    ∀ (inv : Int), (inv ≥ 0) →
    ∀ (clr : Bool) (h : Int),
      ((h ≥ 0) ∧ ((clr → (h + h = inv)) ∧ (¬clr → (h + h + 1 = inv)))) →
    ∀ (v : irbtree),
      ((h > 0) ∧ clr ∧ (num_black v h true) ∧ (no_red_red v true) ∧
        (clr → (is_rbtleaf v = true ∨ (is_rbtnode v = true ∧ ¬(color v = some true)))) ∧
        (clr → (is_rbtleaf v = true ∨ (is_rbtnode v = true ∧ ¬(color v = some true)))) ∧
        (¬clr → (h = 0 → (is_rbtleaf v = true ∨ (is_rbtnode v = true ∧ ¬(color v = some false)))))) →
      ((h > 0) ∧ clr ∧
        ∃ (x_13 : Int),
          ((inv - 1) ≥ 0) ∧ ((h - 1) ≥ 0) ∧
          (((h - 1) + (h - 1) + 1) = (inv - 1)) ∧
          ∃ (lt2 : irbtree),
            (no_red_red lt2 true) ∧ (num_black lt2 (h - 1) true) ∧
            ((h - 1 = 0) → (is_rbtleaf lt2 = true ∨ (is_rbtnode lt2 = true ∧ ¬(color lt2 = some false)))) ∧
            ((inv - 1) < inv) ∧ ((h - 1) ≥ 0) ∧
            (((h - 1) + (h - 1) + 1) = (inv - 1)) ∧
            ∃ (rt2 : irbtree),
              (no_red_red rt2 true) ∧ (num_black rt2 (h - 1) true) ∧
              ((h - 1 = 0) → (is_rbtleaf rt2 = true ∨ (is_rbtnode rt2 = true ∧ ¬(color rt2 = some false)))) ∧
              (is_rbtnode v = true) ∧ (color v = some false) ∧
              (value v = some x_13) ∧ (left v = some lt2) ∧ (right v = some rt2))

-- ============================================================
-- VERSION 2: Unsimplified goal (matching Cobb Z3 SMT dump)
-- Existentials inv_1, h_0, inv_2, h_1 kept as fresh variables
-- ============================================================

axiom goal_unsimplified :
    ∀ (inv : Int), (inv ≥ 0) →
    ∀ (clr : Bool) (h : Int),
      ((h ≥ 0) ∧ ((clr → (h + h = inv)) ∧ (¬clr → (h + h + 1 = inv)))) →
    ∀ (v : irbtree),
      ((h > 0) ∧ clr ∧ (num_black v h true) ∧ (no_red_red v true) ∧
        (clr → (is_rbtleaf v = true ∨ (is_rbtnode v = true ∧ ¬(color v = some true)))) ∧
        (clr → (is_rbtleaf v = true ∨ (is_rbtnode v = true ∧ ¬(color v = some true)))) ∧
        (¬clr → (h = 0 → (is_rbtleaf v = true ∨ (is_rbtnode v = true ∧ ¬(color v = some false)))))) →
      ((h > 0) ∧ clr ∧
        ∃ (inv_1 : Int),
          (inv_1 ≥ 0) ∧ (inv_1 < inv) ∧ (inv_1 = inv - 1) ∧
          ∃ (h_0 : Int),
            (h_0 ≥ 0) ∧ (h_0 + h_0 + 1 = inv_1) ∧ (h_0 = h - 1) ∧
            ∃ (lt2 : irbtree),
              (no_red_red lt2 true) ∧ (num_black lt2 h_0 true) ∧
              ((h_0 = 0) → (is_rbtleaf lt2 = true ∨ (is_rbtnode lt2 = true ∧ ¬(color lt2 = some false)))) ∧
              ∃ (inv_2 : Int),
                (inv_2 ≥ 0) ∧ (inv_2 < inv) ∧ (inv_2 = inv - 1) ∧
                ∃ (h_1 : Int),
                  (h_1 ≥ 0) ∧ (h_1 + h_1 + 1 = inv_2) ∧ (h_1 = h - 1) ∧
                  ∃ (rt2 : irbtree),
                    (no_red_red rt2 true) ∧ (num_black rt2 h_1 true) ∧
                    ((h_1 = 0) → (is_rbtleaf rt2 = true ∨ (is_rbtnode rt2 = true ∧ ¬(color rt2 = some false)))) ∧
                    ∃ (x_13 : Int),
                      (is_rbtnode v = true) ∧ (color v = some false) ∧
                      (value v = some x_13) ∧ (left v = some lt2) ∧ (right v = some rt2))

-- To test: uncomment the z3_auto lines below (requires Z3 on PATH)
z3 goal_simplified
z3 goal_unsimplified
