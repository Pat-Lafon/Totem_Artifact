-- Failed subtyping query #0
-- To debug: prove or find a counterexample for the theorem below.
-- The axioms are assumptions from the coverage type system.

import ProofAutomation

-- Preamble for failed subtyping queries (rbtree only)
-- This file is prepended to each dumped Lean file.
-- The section Axioms at the end is closed by lean_dump.ml after the axioms.

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

def numblack : irbtree → Int → Prop
  | .Rbtleaf, n => n = 0
  | .Rbtnode c l _ r, n =>
    if ¬c then numblack l (n - 1) ∧ numblack r (n - 1)
    else numblack l n ∧ numblack r n

def noredred : irbtree → Prop
  | .Rbtleaf => True
  | .Rbtnode c l _ r =>
    if ¬c then noredred l ∧ noredred r
    else
      match l, r with
      | .Rbtnode c' _ _ _, .Rbtnode c'' _ _ _ =>
          ¬c' ∧ ¬c'' ∧ noredred l ∧ noredred r
      | .Rbtnode c' _ _ _, .Rbtleaf => ¬c' ∧ noredred l
      | .Rbtleaf, .Rbtnode c'' _ _ _ => ¬c'' ∧ noredred r
      | .Rbtleaf, .Rbtleaf => True

def hdcolor : irbtree → Bool → Prop
  | .Rbtleaf, _ => False
  | .Rbtnode c _ _ _, c' => c = c'

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

def rbtree_invariant_impl (t : irbtree) (h : Int) : Bool :=
  no_red_red_impl t && num_black_impl t h

def rbtree_invariant (t : irbtree) (h : Int) (res : Bool) : Prop :=
  rbtree_invariant_impl t h = res

-- Axiom section: definitions are available to grind/simp for proving axioms.
-- lean_dump.ml emits 'end Axioms' after the axioms, before the subtyping query.
section Axioms
  attribute [local simp] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red
    rbtree_invariant_impl rbtree_invariant
  attribute [local grind cases] irbtree Bool
  attribute [local grind =] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red
    rbtree_invariant_impl rbtree_invariant
theorem ax_0 : ∀ (t : irbtree), (∀ (h : Int), (∀ (res : Bool), ((num_black t h res) → ((is_rbtleaf t) → (((h == 0) ∧ (res)) ∨ (¬(h == 0) ∧ ¬(res))))))) := by
  prove_axiom

theorem ax_1 : ∀ (t : irbtree), (∀ (h : Int), (∀ (res : Bool), ((is_rbtleaf t) → ((((h == 0) ∧ (res)) ∨ (¬(h == 0) ∧ ¬(res))) → (num_black t h res))))) := by
  prove_axiom

theorem ax_2 : ∀ (t : irbtree), (∀ (h : Int), (∀ (res : Bool), ((is_rbtleaf t) → ((num_black t h res) → (((h == 0) ∧ (res)) ∨ (¬(h == 0) ∧ ¬(res))))))) := by
  prove_axiom

theorem ax_3 : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), ((num_black t h res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬(c) → (∃ (res_0 : Bool), ((num_black l (h - 1) res_0) → (∃ (res_1 : Bool), ((num_black r (h - 1) res_1) ∧ ((((res_0) ∧ (res_1)) ∧ (res)) ∨ (¬((res_0) ∧ (res_1)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_4 : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬(c) → (∃ (res_0 : Bool), ((num_black l (h - 1) res_0) → ((∃ (res_1 : Bool), ((num_black r (h - 1) res_1) ∧ ((((res_0) ∧ (res_1)) ∧ (res)) ∨ (¬((res_0) ∧ (res_1)) ∧ ¬(res))))) → (num_black t h res))))))))))) := by
  prove_axiom

theorem ax_5 : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), (¬(c) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((num_black t h res) → (∃ (res_0 : Bool), (∃ (res_1 : Bool), ((num_black l (h - 1) res_0) ∧ ((num_black r (h - 1) res_1) ∧ ((((res_0) ∧ (res_1)) ∧ (res)) ∨ (¬((res_0) ∧ (res_1)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_6 : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), ((num_black t h res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → (∃ (res_2 : Bool), ((num_black l h res_2) → (∃ (res_3 : Bool), ((num_black r h res_3) ∧ ((((res_2) ∧ (res_3)) ∧ (res)) ∨ (¬((res_2) ∧ (res_3)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_7 : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → (∃ (res_2 : Bool), ((num_black l h res_2) → ((∃ (res_3 : Bool), ((num_black r h res_3) ∧ ((((res_2) ∧ (res_3)) ∧ (res)) ∨ (¬((res_2) ∧ (res_3)) ∧ ¬(res))))) → (num_black t h res))))))))))) := by
  prove_axiom

theorem ax_8 : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), (¬¬(c) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((num_black t h res) → (∃ (res_2 : Bool), (∃ (res_3 : Bool), ((num_black l h res_2) ∧ ((num_black r h res_3) ∧ ((((res_2) ∧ (res_3)) ∧ (res)) ∨ (¬((res_2) ∧ (res_3)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_9 : ∀ (t : irbtree), (∀ (res : Bool), ((no_red_red t res) → ((is_rbtleaf t) → (true == res)))) := by
  prove_axiom

theorem ax_10 : ∀ (t : irbtree), (∀ (res : Bool), ((is_rbtleaf t) → ((true == res) → (no_red_red t res)))) := by
  prove_axiom

theorem ax_11 : ∀ (t : irbtree), (∀ (res : Bool), ((is_rbtleaf t) → ((no_red_red t res) → (true == res)))) := by
  prove_axiom

theorem ax_12 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), ((no_red_red t res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬(c) → (∃ (res_4 : Bool), ((no_red_red l res_4) → (∃ (res_5 : Bool), ((no_red_red r res_5) ∧ ((((res_4) ∧ (res_5)) ∧ (res)) ∨ (¬((res_4) ∧ (res_5)) ∧ ¬(res)))))))))))))) := by
  prove_axiom

theorem ax_13 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬(c) → (∃ (res_4 : Bool), ((no_red_red l res_4) → ((∃ (res_5 : Bool), ((no_red_red r res_5) ∧ ((((res_4) ∧ (res_5)) ∧ (res)) ∨ (¬((res_4) ∧ (res_5)) ∧ ¬(res))))) → (no_red_red t res)))))))))) := by
  prove_axiom

theorem ax_14 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), (¬(c) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((no_red_red t res) → (∃ (res_4 : Bool), (∃ (res_5 : Bool), ((no_red_red l res_4) ∧ ((no_red_red r res_5) ∧ ((((res_4) ∧ (res_5)) ∧ (res)) ∨ (¬((res_4) ∧ (res_5)) ∧ ¬(res)))))))))))))) := by
  prove_axiom

theorem ax_15 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c' : Bool), (∀ (c'' : Bool), (∀ (res : Bool), ((no_red_red t res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → (((is_rbtnode l) ∧ ((color l) == c')) → (((is_rbtnode r) ∧ ((color r) == c'')) → (∃ (res_6 : Bool), ((no_red_red l res_6) → (∃ (res_7 : Bool), ((no_red_red r res_7) ∧ (((¬(c') ∧ (¬(c'') ∧ ((res_6) ∧ (res_7)))) ∧ (res)) ∨ (¬(¬(c') ∧ (¬(c'') ∧ ((res_6) ∧ (res_7)))) ∧ ¬(res)))))))))))))))))) := by
  prove_axiom

theorem ax_16 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c' : Bool), (∀ (c'' : Bool), (∀ (res : Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → (((is_rbtnode l) ∧ ((color l) == c')) → (((is_rbtnode r) ∧ ((color r) == c'')) → (∃ (res_6 : Bool), ((no_red_red l res_6) → ((∃ (res_7 : Bool), ((no_red_red r res_7) ∧ (((¬(c') ∧ (¬(c'') ∧ ((res_6) ∧ (res_7)))) ∧ (res)) ∨ (¬(¬(c') ∧ (¬(c'') ∧ ((res_6) ∧ (res_7)))) ∧ ¬(res))))) → (no_red_red t res)))))))))))))) := by
  prove_axiom

theorem ax_17 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c' : Bool), (∀ (c'' : Bool), (∀ (res : Bool), (((is_rbtnode r) ∧ ((color r) == c'')) → (((is_rbtnode l) ∧ ((color l) == c')) → (¬¬(c) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((no_red_red t res) → (∃ (res_6 : Bool), (∃ (res_7 : Bool), ((no_red_red l res_6) ∧ ((no_red_red r res_7) ∧ (((¬(c') ∧ (¬(c'') ∧ ((res_6) ∧ (res_7)))) ∧ (res)) ∨ (¬(¬(c') ∧ (¬(c'') ∧ ((res_6) ∧ (res_7)))) ∧ ¬(res)))))))))))))))))) := by
  prove_axiom

theorem ax_18 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c' : Bool), (∀ (res : Bool), ((no_red_red t res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → (((is_rbtnode l) ∧ ((color l) == c')) → ((is_rbtleaf r) → (∃ (res_8 : Bool), ((no_red_red l res_8) ∧ (((¬(c') ∧ (res_8)) ∧ (res)) ∨ (¬(¬(c') ∧ (res_8)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_19 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c' : Bool), (∀ (res : Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → (((is_rbtnode l) ∧ ((color l) == c')) → ((is_rbtleaf r) → ((∃ (res_8 : Bool), ((no_red_red l res_8) ∧ (((¬(c') ∧ (res_8)) ∧ (res)) ∨ (¬(¬(c') ∧ (res_8)) ∧ ¬(res))))) → (no_red_red t res))))))))))) := by
  prove_axiom

theorem ax_20 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c' : Bool), (∀ (res : Bool), ((is_rbtleaf r) → (((is_rbtnode l) ∧ ((color l) == c')) → (¬¬(c) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((no_red_red t res) → (∃ (res_8 : Bool), ((no_red_red l res_8) ∧ (((¬(c') ∧ (res_8)) ∧ (res)) ∨ (¬(¬(c') ∧ (res_8)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_21 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c'' : Bool), (∀ (res : Bool), ((no_red_red t res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → ((is_rbtleaf l) → (((is_rbtnode r) ∧ ((color r) == c'')) → (∃ (res_9 : Bool), ((no_red_red r res_9) ∧ (((¬(c'') ∧ (res_9)) ∧ (res)) ∨ (¬(¬(c'') ∧ (res_9)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_22 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c'' : Bool), (∀ (res : Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → ((is_rbtleaf l) → (((is_rbtnode r) ∧ ((color r) == c'')) → ((∃ (res_9 : Bool), ((no_red_red r res_9) ∧ (((¬(c'') ∧ (res_9)) ∧ (res)) ∨ (¬(¬(c'') ∧ (res_9)) ∧ ¬(res))))) → (no_red_red t res))))))))))) := by
  prove_axiom

theorem ax_23 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (c'' : Bool), (∀ (res : Bool), (((is_rbtnode r) ∧ ((color r) == c'')) → ((is_rbtleaf l) → (¬¬(c) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((no_red_red t res) → (∃ (res_9 : Bool), ((no_red_red r res_9) ∧ (((¬(c'') ∧ (res_9)) ∧ (res)) ∨ (¬(¬(c'') ∧ (res_9)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_24 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), ((no_red_red t res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → ((is_rbtleaf l) → ((is_rbtleaf r) → (true == res)))))))))) := by
  prove_axiom

theorem ax_25 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬¬(c) → ((is_rbtleaf l) → ((is_rbtleaf r) → ((true == res) → (no_red_red t res)))))))))) := by
  prove_axiom

theorem ax_26 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), ((is_rbtleaf r) → ((is_rbtleaf l) → (¬¬(c) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((no_red_red t res) → (true == res)))))))))) := by
  prove_axiom

theorem ax_27 : ∀ (t : irbtree), (∀ (h : Int), (∀ (res : Bool), ((rbtree_invariant t h res) → (∃ (res_10 : Bool), ((no_red_red t res_10) → (∃ (res_11 : Bool), ((num_black t h res_11) ∧ ((((res_10) ∧ (res_11)) ∧ (res)) ∨ (¬((res_10) ∧ (res_11)) ∧ ¬(res)))))))))) := by
  prove_axiom

theorem ax_28 : ∀ (t : irbtree), (∀ (h : Int), (∀ (res : Bool), (∃ (res_10 : Bool), ((no_red_red t res_10) → ((∃ (res_11 : Bool), ((num_black t h res_11) ∧ ((((res_10) ∧ (res_11)) ∧ (res)) ∨ (¬((res_10) ∧ (res_11)) ∧ ¬(res))))) → (rbtree_invariant t h res)))))) := by
  prove_axiom

/- theorem ax_num_black_to_leaf_proposed : ∀ (t : irbtree), num_black t 0 true → is_rbtleaf t := by
  intros t
  cases t with
  | Rbtleaf =>
    grind
  | Rbtnode c' l' v' r' =>
    intro h
    false_or_by_contra
    simp at h
    sorry -/

theorem ax_num_black_unique_res : ∀ (t : irbtree) (h : Int) (res1 res2 : Bool), num_black t h res1 → num_black t h res2 → res1 == res2 := by
  prove_axiom

theorem ax_4_proposed : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res res_0 res_1: Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬(c) → (((num_black l (h - 1) res_0) → ((((num_black r (h - 1) res_1) ∧ ((((res_0) ∧ (res_1)) ∧ (res)) ∨ (¬((res_0) ∧ (res_1)) ∧ ¬(res))))) → (num_black t h res))))))))))) := by
  prove_axiom

end Axioms

theorem failed_subtyping_0 : ∀ (inv : Int), ((inv >= 0) → (∀ (clr : Bool), (∀ (h : Int), (((h >= 0) ∧ (((clr) → ((h + h) == inv)) ∧ (¬(clr) → (((h + h) + 1) == inv)))) → (∀ (v : irbtree), (((h > 0) ∧ ((clr) ∧ (∃ (inv_1 : Int), ((inv_1 >= 0) ∧ ((inv_1 < inv) ∧ ((inv_1 == (inv - 1)) ∧ (∃ (h_0 : Int), ((h_0 >= 0) ∧ ((((h_0 + h_0) + 1) == inv_1) ∧ ((h_0 == (h - 1)) ∧ (∃ (lt2 : irbtree), ((num_black lt2 h_0 true) ∧ ((no_red_red lt2 true) ∧ (((h_0 == 0) → ((is_rbtleaf lt2) ∨ ((is_rbtnode lt2) ∧ ¬((color lt2) == false)))) ∧ (∃ (inv_2 : Int), ((inv_2 >= 0) ∧ ((inv_2 < inv) ∧ ((inv_2 == (inv - 1)) ∧ (∃ (h_1 : Int), ((h_1 >= 0) ∧ ((((h_1 + h_1) + 1) == inv_2) ∧ ((h_1 == (h - 1)) ∧ (∃ (rt2 : irbtree), ((num_black rt2 h_1 true) ∧ ((no_red_red rt2 true) ∧ (((h_1 == 0) → ((is_rbtleaf rt2) ∨ ((is_rbtnode rt2) ∧ ¬((color rt2) == false)))) ∧ (∃ (x_13 : Int), ((is_rbtnode v) ∧ (((color v) == false) ∧ (((value v) == x_13) ∧ (((left v) == lt2) ∧ ((right v) == rt2)))))))))))))))))))))))))))))))) → ((h > 0) ∧ ((clr) ∧ ((num_black v h true) ∧ ((no_red_red v true) ∧ ((clr) → ((is_rbtleaf v) ∨ ((is_rbtnode v) ∧ ¬((color v) == true)))))))))))))) := by
  intros inv h1 clr h h2 v h3
  simp_hyps
  subst_vars
  clear h1 h_8 h_15 h_16 h_17 h_28 h_30 h_29 h_32 h_19
  simp_goal
  · cases v with
    | Rbtleaf => contradiction
    | Rbtnode c' l' v' r' =>
      have h3 := (ax_4_proposed (irbtree.Rbtnode false l' v' r') h false l' r' true true true (by grind) (by grind) (by grind) (by grind))
      grind
  · cases v with
    | Rbtleaf => contradiction
    | Rbtnode c' l' v' r' =>
      simp at h_42 h_41 h_43 h_45
      subst_vars
      clear h_40
      propose_axiom "ax_noredred_proposed" h_26 h_38

#eval ppTheoremsAsOcamlAxioms "_proposed"
