-- Failed subtyping query #12
-- To debug: prove or find a counterexample for the theorem below.
-- The axioms are assumptions from the coverage type system.

import ProofAutomation

-- Preamble for failed subtyping queries (rbtree only)
-- This file is prepended to each dumped Lean file.
-- The namespace Axioms at the end is closed by lean_dump.ml after the
-- axioms; a top-level `open Axioms` keeps bare `ax_<n>` references
-- working in the `failed_subtyping_*` body and `z3?` calls below.

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

-- Axiom namespace: definitions are available to grind/simp for proving axioms.
-- lean_dump.ml emits 'end Axioms' + 'open Axioms' after the axioms, before the
-- subtyping query.
namespace Axioms
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

open Axioms

theorem failed_subtyping_12 : ∀ (inv : Int), ((inv >= 0) → (∀ (clr : Bool), (∀ (h : Int), (((h >= 0) ∧ (((clr) → ((h + h) == inv)) ∧ (¬(clr) → (((h + h) + 1) == inv)))) → (∀ (v : irbtree), ((∃ (x_0 : Bool), (((x_0) ↔ (h == 0)) ∧ (¬(x_0) ↔ (h > 0)) ∧ (num_black v h true) ∧ (no_red_red v true) ∧ ((clr) → ((is_rbtleaf v) ∨ ((is_rbtnode v) ∧ ¬((color v) == true)))) ∧ (¬(clr) → ((h == 0) → ((is_rbtleaf v) ∨ ((is_rbtnode v) ∧ ¬((color v) == false))))))) → (∃ (x_0 : Bool), (((x_0) ↔ (h == 0)) ∧ (¬(x_0) ↔ (h > 0)) ∧ (((x_0) ∧ (((clr) ∧ (is_rbtleaf v) ∧ (num_black v 0 true)) ∨ (¬(clr) ∧ (∃ (x_1 : Bool), (((x_1) ∧ (is_rbtleaf v) ∧ (num_black v 0 true)) ∨ (¬(x_1) ∧ (∃ (x_2 : irbtree), ((is_rbtleaf x_2) ∧ (num_black x_2 0 true) ∧ (∃ (x_3 : Int), (∃ (x_4 : irbtree), ((is_rbtleaf x_4) ∧ (num_black x_4 0 true) ∧ (is_rbtnode v) ∧ ((color v) == true) ∧ ((value v) == x_3) ∧ ((left v) == x_4) ∧ ((right v) == x_2)))))))))))) ∨ (¬(x_0) ∧ (((clr) ∧ (∃ (inv_1 : Int), ((inv_1 >= 0) ∧ (inv_1 < inv) ∧ (inv_1 == (inv - 1)) ∧ (∃ (h_0 : Int), ((h_0 >= 0) ∧ ((false) → ((h_0 + h_0) == inv_1)) ∧ (¬(false) → (((h_0 + h_0) + 1) == inv_1)) ∧ (h_0 == (h - 1)) ∧ (∃ (lt2 : irbtree), ((num_black lt2 h_0 true) ∧ (no_red_red lt2 true) ∧ ((false) → ((is_rbtleaf lt2) ∨ ((is_rbtnode lt2) ∧ ¬((color lt2) == true)))) ∧ (¬(false) → ((h_0 == 0) → ((is_rbtleaf lt2) ∨ ((is_rbtnode lt2) ∧ ¬((color lt2) == false))))) ∧ (∃ (inv_2 : Int), ((inv_2 >= 0) ∧ (inv_2 < inv) ∧ (inv_2 == (inv - 1)) ∧ (∃ (h_1 : Int), ((h_1 >= 0) ∧ ((false) → ((h_1 + h_1) == inv_2)) ∧ (¬(false) → (((h_1 + h_1) + 1) == inv_2)) ∧ (h_1 == (h - 1)) ∧ (∃ (rt2 : irbtree), ((num_black rt2 h_1 true) ∧ (no_red_red rt2 true) ∧ ((false) → ((is_rbtleaf rt2) ∨ ((is_rbtnode rt2) ∧ ¬((color rt2) == true)))) ∧ (¬(false) → ((h_1 == 0) → ((is_rbtleaf rt2) ∨ ((is_rbtnode rt2) ∧ ¬((color rt2) == false))))) ∧ (∃ (x_13 : Int), ((is_rbtnode v) ∧ (((color v) == false) ∧ (((value v) == x_13) ∧ (((left v) == lt2) ∧ ((right v) == rt2))))))))))))))))))) ∨ (¬(clr) ∧ (∃ (c : Bool), (((c) ∧ (∃ (inv_3 : Int), ((inv_3 >= 0) ∧ (inv_3 < inv) ∧ (inv_3 == (inv - 1)) ∧ (∃ (h_2 : Int), ((h_2 >= 0) ∧ ((true) → ((h_2 + h_2) == inv_3)) ∧ (¬(true) → (((h_2 + h_2) + 1) == inv_3)) ∧ (h_2 == h) ∧ (∃ (lt3 : irbtree), ((num_black lt3 h_2 true) ∧ (no_red_red lt3 true) ∧ ((true) → ((is_rbtleaf lt3) ∨ ((is_rbtnode lt3) ∧ ¬((color lt3) == true)))) ∧ (¬(true) → ((h_2 == 0) → ((is_rbtleaf lt3) ∨ ((is_rbtnode lt3) ∧ ¬((color lt3) == false))))) ∧ (∃ (inv_4 : Int), ((inv_4 >= 0) ∧ (inv_4 < inv) ∧ (inv_4 == (inv - 1)) ∧ (∃ (h_3 : Int), ((h_3 >= 0) ∧ ((true) → ((h_3 + h_3) == inv_4)) ∧ (¬(true) → (((h_3 + h_3) + 1) == inv_4)) ∧ (h_3 == h) ∧ (∃ (rt3 : irbtree), ((num_black rt3 h_3 true) ∧ (no_red_red rt3 true) ∧ ((true) → ((is_rbtleaf rt3) ∨ ((is_rbtnode rt3) ∧ ¬((color rt3) == true)))) ∧ (¬(true) → ((h_3 == 0) → ((is_rbtleaf rt3) ∨ ((is_rbtnode rt3) ∧ ¬((color rt3) == false))))) ∧ (∃ (x_20 : Int), ((is_rbtnode v) ∧ (((color v) == true) ∧ (((value v) == x_20) ∧ (((left v) == lt3) ∧ ((right v) == rt3))))))))))))))))))) ∨ (¬(c) ∧ (∃ (inv_5 : Int), ((inv_5 >= 0) ∧ (inv_5 < inv) ∧ (inv_5 == ((inv - 1) - 1)) ∧ (∃ (h_4 : Int), ((h_4 >= 0) ∧ ((false) → ((h_4 + h_4) == inv_5)) ∧ (¬(false) → (((h_4 + h_4) + 1) == inv_5)) ∧ (h_4 == (h - 1)) ∧ (∃ (lt4 : irbtree), ((num_black lt4 h_4 true) ∧ (no_red_red lt4 true) ∧ ((false) → ((is_rbtleaf lt4) ∨ ((is_rbtnode lt4) ∧ ¬((color lt4) == true)))) ∧ (¬(false) → ((h_4 == 0) → ((is_rbtleaf lt4) ∨ ((is_rbtnode lt4) ∧ ¬((color lt4) == false))))) ∧ (∃ (inv_6 : Int), ((inv_6 >= 0) ∧ (inv_6 < inv) ∧ (inv_6 == ((inv - 1) - 1)) ∧ (∃ (h_5 : Int), ((h_5 >= 0) ∧ ((false) → ((h_5 + h_5) == inv_6)) ∧ (¬(false) → (((h_5 + h_5) + 1) == inv_6)) ∧ (h_5 == (h - 1)) ∧ (∃ (rt4 : irbtree), ((num_black rt4 h_5 true) ∧ (no_red_red rt4 true) ∧ ((false) → ((is_rbtleaf rt4) ∨ ((is_rbtnode rt4) ∧ ¬((color rt4) == true)))) ∧ (¬(false) → ((h_5 == 0) → ((is_rbtleaf rt4) ∨ ((is_rbtnode rt4) ∧ ¬((color rt4) == false))))) ∧ (∃ (x_31 : Int), ((is_rbtnode v) ∧ (((color v) == false) ∧ (((value v) == x_31) ∧ (((left v) == lt4) ∧ ((right v) == rt4))))))))))))))))))))))))))))))))) := by
  intros inv h1 clr h h2 v h3
  simp_hyps
  refine ⟨x_0, ?_⟩
  cases v with
  | Rbtleaf =>
    cases clr with
    | true =>
      cases x_0 with
      | true =>
        simp_goal
      | false =>
        simp_hyps
        simp_goal
        exfalso
        clear h_24
        z3_local only [ax_0]
    | false =>
      cases x_0 with
      | true =>
        simp_hyps
        simp_goal
        refine ⟨true, ?_⟩; rotate_left
        simp_goal
      | false =>
        simp_hyps
        simp_goal
        -- Workaround for Lean bug: `cases ?c with | true | false` overflows
        -- the elaborator. Instead, prove BOTH disjunction-witness branches
        -- via a conjunction, then pick either side to assemble the existential.
        suffices h :
            (∃ inv_3, inv_3 ≥ 0 ∧ inv_3 < inv ∧ (inv_3 == inv - 1) = true ∧
              ∃ h_2, h_2 ≥ 0 ∧ (true = true → (h_2 + h_2 == inv_3) = true) ∧
                (¬true = true → (h_2 + h_2 + 1 == inv_3) = true) ∧
                (h_2 == h) = true ∧
              ∃ lt3, num_black lt3 h_2 true ∧ no_red_red lt3 true ∧
                (true = true → is_rbtleaf lt3 = true ∨ is_rbtnode lt3 = true ∧ ¬(color lt3 == some true) = true) ∧
                (¬true = true → (h_2 == 0) = true →
                  is_rbtleaf lt3 = true ∨ is_rbtnode lt3 = true ∧ ¬(color lt3 == some false) = true) ∧
              ∃ inv_4, inv_4 ≥ 0 ∧ inv_4 < inv ∧ (inv_4 == inv - 1) = true ∧
              ∃ h_3, h_3 ≥ 0 ∧ (true = true → (h_3 + h_3 == inv_4) = true) ∧
                (¬true = true → (h_3 + h_3 + 1 == inv_4) = true) ∧
                (h_3 == h) = true ∧
              ∃ rt3, num_black rt3 h_3 true ∧ no_red_red rt3 true ∧
                (true = true → is_rbtleaf rt3 = true ∨ is_rbtnode rt3 = true ∧ ¬(color rt3 == some true) = true) ∧
                (¬true = true → (h_3 == 0) = true →
                  is_rbtleaf rt3 = true ∨ is_rbtnode rt3 = true ∧ ¬(color rt3 == some false) = true) ∧
              ∃ x_20, is_rbtnode irbtree.Rbtleaf = true ∧
                (color irbtree.Rbtleaf == some true) = true ∧
                (value irbtree.Rbtleaf == some x_20) = true ∧
                (left irbtree.Rbtleaf == some lt3) = true ∧
                (right irbtree.Rbtleaf == some rt3) = true)
            ∧
            (∃ inv_5, inv_5 ≥ 0 ∧ inv_5 < inv ∧ (inv_5 == inv - 1 - 1) = true ∧
              ∃ h_4, h_4 ≥ 0 ∧ (false = true → (h_4 + h_4 == inv_5) = true) ∧
                (¬false = true → (h_4 + h_4 + 1 == inv_5) = true) ∧
                (h_4 == h - 1) = true ∧
              ∃ lt4, num_black lt4 h_4 true ∧ no_red_red lt4 true ∧
                (false = true → is_rbtleaf lt4 = true ∨ is_rbtnode lt4 = true ∧ ¬(color lt4 == some true) = true) ∧
                (¬false = true → (h_4 == 0) = true →
                  is_rbtleaf lt4 = true ∨ is_rbtnode lt4 = true ∧ ¬(color lt4 == some false) = true) ∧
              ∃ inv_6, inv_6 ≥ 0 ∧ inv_6 < inv ∧ (inv_6 == inv - 1 - 1) = true ∧
              ∃ h_5, h_5 ≥ 0 ∧ (false = true → (h_5 + h_5 == inv_6) = true) ∧
                (¬false = true → (h_5 + h_5 + 1 == inv_6) = true) ∧
                (h_5 == h - 1) = true ∧
              ∃ rt4, num_black rt4 h_5 true ∧ no_red_red rt4 true ∧
                (false = true → is_rbtleaf rt4 = true ∨ is_rbtnode rt4 = true ∧ ¬(color rt4 == some true) = true) ∧
                (¬false = true → (h_5 == 0) = true →
                  is_rbtleaf rt4 = true ∨ is_rbtnode rt4 = true ∧ ¬(color rt4 == some false) = true) ∧
              ∃ x_31, is_rbtnode irbtree.Rbtleaf = true ∧
                (color irbtree.Rbtleaf == some false) = true ∧
                (value irbtree.Rbtleaf == some x_31) = true ∧
                (left irbtree.Rbtleaf == some lt4) = true ∧
                (right irbtree.Rbtleaf == some rt4) = true) by
          grind
        refine ⟨?_, ?_⟩ <;>
          (exfalso; simp [num_black, num_black_impl] at h_22; omega)
  | Rbtnode c' l' v' r' =>
    simp_hyps
    simp_goal
    cases x_0 with
    | true =>
      z3_local only [ax_18, ax_17, ax_30, ax_8, ax_21, ax_5, ax_31]
      /- simp_hyps
      cases clr with
      | true =>
        simp_hyps
        subst_vars
        cases h_18 with
        | inl h2 =>
          contradiction
        | inr h2 =>
          simp_hyps
          simp at h_47
          subst_vars
          have := ax_5 (irbtree.Rbtnode false l' v' r') 0 false l' r' true (by grind) (by grind) (by grind)
          simp_hyps
          have := ax_31 l' (-1) (by grind)
          contradiction
      | false => -/
        /- simp_goal
        refine ⟨false, ?_⟩
        simp_goal
        refine ⟨irbtree.Rbtleaf, ?_⟩
        simp_goal
        · apply ax_1 <;> grind
        · simp_hyps
          subst_vars
          simp_hyps
          refine ⟨v', ?_⟩
          refine ⟨l', ?_⟩
 -/
          /- cases h_20 with
          | inl h1 => contradiction
          | inr h1 => -/

            /- simp_hyps
            simp at h_48
            subst_vars
            clear h
            have := (ax_8 (irbtree.Rbtnode true l' v' r') 0 true l' r' true (by grind) (by grind) h_17)
            simp_hyps
            simp_goal
            ·
/-
              cases l' with
              | Rbtleaf =>
                simp
              | Rbtnode c l v r =>
                simp
                cases c with
                | true =>

                  /- clear h h_17 h_32
                  cases r' with
                  | Rbtleaf =>

                   /-  have := (ax_18 (irbtree.Rbtnode true (irbtree.Rbtnode true l v r) v' irbtree.Rbtleaf) true (irbtree.Rbtnode true l v r) irbtree.Rbtleaf true true (by grind) (by grind) (by grind) (by grind) (by grind))
                    simp_hyps -/
                  | Rbtnode c'' l'' v'' r'' =>
                    have := (ax_17 (irbtree.Rbtnode true (irbtree.Rbtnode true l v r) v' (irbtree.Rbtnode c'' l'' v'' r'')) true (irbtree.Rbtnode true l v r) (irbtree.Rbtnode c'' l'' v'' r'') true c'' true (by grind) (by grind) (by grind) (by grind) (by grind))
                    simp_hyps -/
                | false =>
                  clear h_16 h_17
                  have := (ax_30 (irbtree.Rbtnode false l v r) false l v r (by grind) (by grind))
                  grind -/
            · cases r' with
              | Rbtleaf => simp
              | Rbtnode c l v r =>
                simp
                have := (ax_30 (irbtree.Rbtnode c l v r) c l v r (by grind) (by grind))
                subst_vars
                cases l' with
                | Rbtleaf =>
                  have := (ax_21 (irbtree.Rbtnode true irbtree.Rbtleaf v' (irbtree.Rbtnode true l v r)) true irbtree.Rbtleaf (irbtree.Rbtnode true l v r) true true (by grind) (by grind) (by grind) (by grind) (by grind))
                  simp_hyps
                | Rbtnode c'' l'' v'' r'' =>
                  clear h h_32 h_17
                  have := (ax_17 (irbtree.Rbtnode true (irbtree.Rbtnode c'' l'' v'' r'') v' (irbtree.Rbtnode true l v r)) true (irbtree.Rbtnode c'' l'' v'' r'') (irbtree.Rbtnode true l v r) c'' true true (by grind) (by grind) (by grind) (by grind) (by grind))
                  simp_hyps -/
    | false =>
      z3_local only [ax_5, ax_14, ax_30, ax_17, ax_20, ax_8, ax_0]
      /- clear h_8
      cases clr with
      | true =>
        z3_local only [ax_30, ax_14, ax_5]
        /-  simp_goal
        refine ⟨l', ?_ ⟩
        simp_hyps
        cases h_18 with
        | inl h2 => contradiction
        | inr h2 =>
          simp at h2
          subst_vars
          have := (ax_5 (irbtree.Rbtnode false l' v' r') h false l' r' true (by grind) (by grind) (by grind))
          simp_hyps
          have := (ax_14 (irbtree.Rbtnode false l' v' r') false l' r' true (by grind) (by grind) (by grind)) -/

          /- simp_hyps
          simp_goal
          ·

            /- intros h2 h3
            simp_hyps
            rw [h3] at h_52 h_54
            cases l' with
            | Rbtleaf => grind
            | Rbtnode c l v r =>
              simp_goal
              have := (ax_30 (irbtree.Rbtnode c l v r) c l v r (by grind) (by grind))
              grind -/
          · refine ⟨r', ?_⟩
            simp_goal
            · intros h2 h3
              simp_hyps
              rw [h3] at h_52 h_54
              cases r' with
              | Rbtleaf => grind
              | Rbtnode c l v r =>
                simp_goal
                have := (ax_30 (irbtree.Rbtnode c l v r) c l v r (by grind) (by grind))
                grind
            · refine ⟨v', ?_⟩
              simp_goal -/
      | false =>
        z3_local only [ax_5, ax_14, ax_30, ax_17, ax_20, ax_8, ax_0] -/
        /- simp_goal
        simp_hyps
        refine ⟨c', ?_⟩
        cases c' with
        | true =>
          z3_local only [ax_17, ax_20, ax_8, ax_0]
          /- simp_goal
          refine ⟨l', ?_⟩
          simp_goal
          · have := (ax_8 (irbtree.Rbtnode true l' v' r') h true l' r' true (by grind) (by grind) (by grind))
            simp_hyps
            grind
          · propose_axiom "ax_lazy_1_proposed" h_16
          ·
            /- intro h3
            cases l' with
            | Rbtleaf => grind
            | Rbtnode c l v r =>
              simp_goal
              simp -/
          · z3_local only [ax_17, ax_0, ax_8] -/
            /- refine ⟨r', ?_ ⟩
            have := (ax_8 (irbtree.Rbtnode true l' v' r') h true l' r' true (by grind) (by grind) (by grind))
            simp_hyps
            simp_goal
            · search_axioms h_16
              z3_local only [ax_17, ax_0]
              /- propose_axiom "ax_lazy_3_proposed" h_16 -/
            · z3_local only [ax_17, ax_23]
              /-
              intros h2
              cases r' with
              | Rbtleaf => grind
              | Rbtnode c l v r =>
                simp_goal
                simp
                /- propose_axiom "ax_lazy_4_proposed" h_16 -/ -/
            · refine ⟨v', ?_ ⟩
              simp_goal -/
        | false =>
          z3_local only [ax_5, ax_14, ax_30] -/
          /- simp_goal
          refine ⟨l', ?_ ⟩
          simp_goal
          · z3_local only [ax_5]
          · z3_local only [ax_14]
          · intros h2 h3
            simp_hyps
            cases l' with
            | Rbtleaf => grind
            | Rbtnode c l v r =>
              simp_goal
              simp
              z3_local only [ax_30, ax_32]
          · z3_local only [ax_5, ax_14, ax_30] -/
            /-
            refine ⟨r', ?_⟩ simp_goal
            · z3_local only [ax_5]
            · z3_local only [ax_14]
            · intros h2 h3
              simp_hyps
              cases r' with
              | Rbtleaf => grind
              | Rbtnode c l v r =>
                simp_goal
                simp
                clear h_16
                z3_local only [ax_5, ax_30]
                /- z3_local only [ax_5] -/
                /- propose_axiom "ax_lazy_6_proposed" h_17 h3 -/
            · z3_local only [] -/

-- The full-axiom verbose dispatch hits the rbtree accessor blowup:
-- 39 axioms saturate Z3's e-matching on `right(Rbtnode(..))` and the
-- solver returns `unknown` (then errors on `(get-unsat-core)` after
-- the non-unsat verdict, surfacing as exit-1 in the wrapper). See
-- `project_z3_accessor_blowup.md` — the manual 10-axiom subset below
-- closes the goal cleanly. Re-enable when the accessor-blowup
-- mitigation lands (TODO.md "Lean Z3 Tactic").
-- z3? failed_subtyping_12

z3 failed_subtyping_12 only [ax_0, ax_1, ax_5, ax_8, ax_14, ax_17, ax_18, ax_21, ax_30, ax_31]
