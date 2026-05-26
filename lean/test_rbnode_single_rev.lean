-- Failed subtyping query #3
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

theorem ax_27 : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), (∀ (res_0 : Bool), (∀ (res_1 : Bool), (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬(c) → ((num_black l (h - 1) res_0) → (((num_black r (h - 1) res_1) ∧ ((((res_0) ∧ (res_1)) ∧ (res)) ∨ (¬((res_0) ∧ (res_1)) ∧ ¬(res)))) → (num_black t h res)))))))))))) := by
  prove_axiom

theorem ax_28 : ∀ (t : irbtree), (∀ (l' : irbtree), (∀ (v' : Int), (∀ (r' : irbtree), ((no_red_red l' true) → ((no_red_red r' true) → ((((((is_rbtnode t) ∧ ((color t) == false)) ∧ ((left t) == l')) ∧ ((value t) == v')) ∧ ((right t) == r')) → (no_red_red t true))))))) := by
  prove_axiom

theorem ax_29 : ∀ (t : irbtree), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), ((no_red_red t res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬(c) → (∃ (res_4 : Bool), ((no_red_red l res_4) ∧ (∃ (res_5 : Bool), ((no_red_red r res_5) ∧ ((((res_4) ∧ (res_5)) ∧ (res)) ∨ (¬((res_4) ∧ (res_5)) ∧ ¬(res)))))))))))))) := by
  prove_axiom

@[grind →]
theorem ax_31 : ∀ (t : irbtree), (∀ (h : Int), ((num_black t h true) → (h >= 0))) := by
  prove_axiom

grind_pattern ax_31 => num_black_impl t h

theorem ax_30 : ∀ (t : irbtree), (∀ (c'' : Bool), (∀ (l'' : irbtree), (∀ (v'' : Int), (∀ (r'' : irbtree), ((((((is_rbtnode t) ∧ ((color t) == c'')) ∧ ((left t) == l'')) ∧ ((value t) == v'')) ∧ ((right t) == r'')) → ((num_black t 0 true) → (c''))))))) := by
  prove_axiom

theorem ax_32 : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool), (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool), ((num_black t h res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) → (¬(c) → (∃ (res_0 : Bool), ((num_black l (h - 1) res_0) ∧ (∃ (res_1 : Bool), ((num_black r (h - 1) res_1) ∧ ((((res_0) ∧ (res_1)) ∧ (res)) ∨ (¬((res_0) ∧ (res_1)) ∧ ¬(res))))))))))))))) := by
  prove_axiom

theorem ax_33 : ∀ (t : irbtree), (∀ (l' : irbtree), (∀ (v' : Int), (∀ (r' : irbtree), ((((((is_rbtnode t) ∧ ((color t) == true)) ∧ ((left t) == l')) ∧ ((value t) == v')) ∧ ((right t) == r')) → ((no_red_red l' true) → ((no_red_red r' true) → (((is_rbtleaf l') ∨ ((is_rbtnode l') ∧ ¬((color l') == true))) → (((is_rbtleaf r') ∨ ((is_rbtnode r') ∧ ¬((color r') == true))) → (no_red_red t true))))))))) := by
  prove_axiom

theorem ax_34 : ∀ (t : irbtree), (∀ (h_3 : Int), (∀ (l' : irbtree), (∀ (v' : Int), (∀ (r' : irbtree), ((((((is_rbtnode t) ∧ ((color t) == true)) ∧ ((left t) == l')) ∧ ((value t) == v')) ∧ ((right t) == r')) → ((num_black l' h_3 true) → ((num_black r' h_3 true) → (num_black t h_3 true)))))))) := by
  prove_axiom

theorem ax_35 : ∀ (t : irbtree), (∀ (h : Int), (∀ (l' : irbtree), (∀ (v' : Int), (∀ (r' : irbtree), ((((((is_rbtnode t) ∧ ((color t) == false)) ∧ ((left t) == l')) ∧ ((value t) == v')) ∧ ((right t) == r')) → ((num_black l' (h - 1) true) → ((num_black r' (h - 1) true) → (num_black t h true)))))))) := by
  prove_axiom

theorem ax_36 : ∀ (t : irbtree), (∀ (l' : irbtree), (∀ (v' : Int), (∀ (r' : irbtree), ((((((is_rbtnode t) ∧ ((color t) == true)) ∧ ((left t) == l')) ∧ ((value t) == v')) ∧ ((right t) == r')) → ((no_red_red l' true) → (((is_rbtleaf l') ∨ ((is_rbtnode l') ∧ ¬((color l') == true))) → ((no_red_red r' true) → (((is_rbtleaf r') ∨ ((is_rbtnode r') ∧ ¬((color r') == true))) → (no_red_red t true))))))))) := by
  prove_axiom

theorem ax_37 : ∀ (t : irbtree), (∀ (h : Int), (∀ (l' : irbtree), (∀ (v' : Int), (∀ (r' : irbtree), ((((((is_rbtnode t) ∧ ((color t) == false)) ∧ ((left t) == l')) ∧ ((value t) == v')) ∧ ((right t) == r')) → ((no_red_red l' true) → ((((h - 1) == 0) → ((is_rbtleaf l') ∨ ((is_rbtnode l') ∧ ¬((color l') == false)))) → ((no_red_red r' true) → ((((h - 1) == 0) → ((is_rbtleaf r') ∨ ((is_rbtnode r') ∧ ¬((color r') == false)))) → (no_red_red t true)))))))))) := by
  prove_axiom

theorem ax_38 : ∀ (t : irbtree), (∀ (h : Int), (∀ (l' : irbtree), (∀ (v' : Int), (∀ (r' : irbtree), ((((((is_rbtnode t) ∧ ((color t) == true)) ∧ ((left t) == l')) ∧ ((value t) == v')) ∧ ((right t) == r')) → ((num_black l' h true) → ((num_black r' h true) → (num_black t h true)))))))) := by
  prove_axiom

end Axioms

theorem failed_subtyping_3 : ∀ (inv : Int), ((inv >= 0) → (∀ (clr : Bool), (∀ (h : Int), (((h >= 0) ∧ (((clr) → ((h + h) == inv)) ∧ (¬(clr) → (((h + h) + 1) == inv)))) → (∀ (v : irbtree), (((is_rbtleaf v) ∨ (((is_rbtnode v) ∧ ¬((color v) == false)) ∧ ((is_rbtnode v) ∧ (((color v) == true) ∧ ((num_black v 0 true) ∧ ((no_red_red v true) ∧ (clr))))))) → (∃ (t : irbtree), ((is_rbtleaf t) ∧ ((is_rbtnode v) ∧ (((color v) == true) ∧ (((is_rbtleaf v) ∨ ((is_rbtnode v) ∧ ¬((color v) == false))) ∧ ((clr) ∧ (((left v) == t) ∧ ((right v) == t)))))))))))))) := by
  intros inv h1 clr h h2 v h3
  simp_hyps
  cases v with
  | Rbtleaf =>
    simp_all
    propose_counterexample 42
    sorry
  | Rbtnode c l v r =>
    simp_hyps

    refine ⟨irbtree.Rbtleaf, ?_⟩
    have := ax_8 (irbtree.Rbtnode true l v r) (0) true l r true (by grind) (by grind) (by grind)
    simp_hyps
    cases l with
    | Rbtleaf =>
      simp_goal
      cases r with
      | Rbtleaf =>
        grind
      | Rbtnode c' l' v' r' =>
        have := ax_21 (irbtree.Rbtnode true irbtree.Rbtleaf v (irbtree.Rbtnode c' l' v' r')) true irbtree.Rbtleaf (irbtree.Rbtnode c' l' v' r') c' true h_26 (by grind) (by grind) (by grind) (by grind)
        simp_hyps
        have := ax_30 (irbtree.Rbtnode false l' v' r') false l' v' r' (by grind) (by grind)
        grind
    | Rbtnode c' l' v' r' =>
      simp
      cases r with
      | Rbtleaf =>
        have := ax_18 (irbtree.Rbtnode true (irbtree.Rbtnode c' l' v' r') v
irbtree.Rbtleaf) true (irbtree.Rbtnode c' l' v' r') irbtree.Rbtleaf c' true h_26 (by grind) (by grind) (by grind) (by grind)
        simp_hyps
        have := ax_30 (irbtree.Rbtnode false l' v' r') false l' v' r' (by grind) (by grind)
        grind
      | Rbtnode c'' l'' v'' r'' =>
        have := ax_17 (irbtree.Rbtnode true (irbtree.Rbtnode c' l' v' r') v (irbtree.Rbtnode c'' l'' v'' r'')) true (irbtree.Rbtnode c' l' v' r') (irbtree.Rbtnode c'' l'' v'' r'') c' c'' true (by grind) (by grind) (by grind) (by grind) h_26
        simp_hyps
        have := ax_30 (irbtree.Rbtnode false l' v' r') false l' v' r' (by grind) (by grind)
        grind


-- Lift the PBT witness back to the outer theorem statement.
-- Witness: inv = 0, clr = true, h = 0, v = Rbtleaf.
-- Then h3 holds via the `is_rbtleaf v` disjunct, but the conclusion requires
-- `is_rbtnode v` which is false on Rbtleaf — so the existential body is False.
theorem failed_subtyping_3_refutation :
    ¬ (∀ (inv : Int), ((inv >= 0) → (∀ (clr : Bool), (∀ (h : Int), (((h >= 0) ∧ (((clr) → ((h + h) == inv)) ∧ (¬(clr) → (((h + h) + 1) == inv)))) → (∀ (v : irbtree), (((is_rbtleaf v) ∨ (((is_rbtnode v) ∧ ¬((color v) == false)) ∧ ((is_rbtnode v) ∧ (((color v) == true) ∧ ((num_black v 0 true) ∧ ((no_red_red v true) ∧ (clr))))))) → (∃ (t : irbtree), ((is_rbtleaf t) ∧ ((is_rbtnode v) ∧ (((color v) == true) ∧ (((is_rbtleaf v) ∨ ((is_rbtnode v) ∧ ¬((color v) == false))) ∧ ((clr) ∧ (((left v) == t) ∧ ((right v) == t))))))))))))))) := fun H => by
  have inst := H 0 (by omega) true 0
    ⟨by omega, fun _ => by simp, fun h => absurd rfl h⟩
    irbtree.Rbtleaf (Or.inl (by simp))
  obtain ⟨_, _, hnode, _⟩ := inst
  simp at hnode

/- z3 failed_subtyping_3 [ax_8, ax_17, ax_18, ax_21, ax_30] -/
