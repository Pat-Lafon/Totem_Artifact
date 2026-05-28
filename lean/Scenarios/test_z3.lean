import ProofAutomation

-- Inlined preamble (formerly `import Preamble`)

inductive itree where
  | Leaf
  | Node (value : Int) (left : itree) (right : itree)
  deriving DecidableEq

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

def depth : itree → Int → Prop
  | .Leaf, n => n = 0
  | .Node _ l r, n => ∃ dl dr : Int, depth l dl ∧ depth r dr ∧ n = 1 + max dl dr

namespace Axioms
  attribute [local simp] is_leaf is_node value left right depth
  attribute [local grind cases] itree Bool
  attribute [local grind =] is_leaf is_node value left right depth
end Axioms
open Axioms

-- ============================================================
-- Part 1: Z3 datatype translation unit tests (MyList)
-- ============================================================

inductive MyList where
  | MNil
  | MCons (head : Int) (tail : MyList)

def myIsNil : MyList → Bool
  | .MNil => true
  | .MCons _ _ => false

def myIsCons : MyList → Bool
  | .MNil => false
  | .MCons _ _ => true

def myHead : MyList → Option Int
  | .MNil => none
  | .MCons h _ => some h

def myTail : MyList → Option MyList
  | .MNil => none
  | .MCons _ t => some t

axiom z3_arith : ∀ (x : Int), x > 0 → x ≥ 1
z3 z3_arith only []

axiom z3_recognizer : ∀ (l : MyList), myIsNil l = true ∨ myIsCons l = true
z3 z3_recognizer only []

axiom z3_accessor : ∀ (h : Int) (t : MyList), myHead (MyList.MCons h t) = some h
z3 z3_accessor only []

axiom z3_ctor_rec : myIsNil MyList.MNil = true
z3 z3_ctor_rec only []

axiom z3_not_nil : ∀ (h : Int) (t : MyList), myIsNil (MyList.MCons h t) = false
z3 z3_not_nil only []

axiom z3_tail_accessor : ∀ (h : Int) (t : MyList), myTail (MyList.MCons h t) = some t
z3 z3_tail_accessor only []

axiom z3_ctor_inject : ∀ (h1 h2 : Int) (t : MyList),
    myHead (MyList.MCons h1 t) = some h2 → h1 = h2
z3 z3_ctor_inject only []

axiom z3_arith_quant : ∀ (x y : Int), x ≥ 0 → y ≥ 0 → x + y ≥ 0
z3 z3_arith_quant only []

-- Negative test: this is FALSE — z3! verifies Z3 correctly rejects it
axiom z3_should_fail : ∀ (x : Int), x > 0 → x ≥ 2
z3! z3_should_fail only []

-- ============================================================
-- Part 2: Depth-tree axioms (shared by subtyping checks #0 and #146)
-- ============================================================

namespace Axioms

axiom ax_0 : ∀ (t : itree), (∀ (n : Int), ((depth t n) → (n >= 0)))
axiom ax_1 : ∀ (t : itree), (∀ (res : Int), ((depth t res) → ((is_leaf t) → (0 == res))))
axiom ax_2 : ∀ (t : itree), (∀ (res : Int), ((is_leaf t) → ((0 == res) → (depth t res))))
axiom ax_3 : ∀ (t : itree), (∀ (res : Int), ((depth t res) → ((0 == res) → (is_leaf t))))
axiom ax_4 : ∀ (t : itree), (∀ (res : Int), ((is_leaf t) → ((depth t res) → (0 == res))))
axiom ax_5 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), ((∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ (res_0 > res_1)))) → ((depth l res_0) → ((1 + res_0) == res))))))))))
axiom ax_6 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), ((∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ (res_0 > res_1)))) → ((depth l res_0) → (((1 + res_0) == res) → (depth t res))))))))))
axiom ax_7 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), (∃ (res_0 : Int), ((∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ (res_0 > res_1)))) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((depth t res) → ((depth l res_0) ∧ ((1 + res_0) == res))))))))))
axiom ax_8 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((((depth l res_0) ∧ ((depth r res_1) ∧ ¬(res_0 > res_1))) ∧ (depth r res_1)) → ((1 + res_1) == res))))))))))
axiom ax_9 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((((depth l res_0) ∧ ((depth r res_1) ∧ ¬(res_0 > res_1))) ∧ (depth r res_1)) → (((1 + res_1) == res) → (depth t res))))))))))
axiom ax_10 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), (∃ (res_0 : Int), (∃ (res_1 : Int), (((depth l res_0) ∧ ((depth r res_1) ∧ ¬(res_0 > res_1))) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((depth t res) → ((depth r res_1) ∧ ((1 + res_1) == res)))))))))))
axiom ax_11 : ∀ (t : itree), (∀ (res : Int), (∀ (res2 : Int), ((depth t res) → ((depth t res2) → (res2 == res)))))
axiom ax_12 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ ((res_0 > res_1) → ((1 + res_0) == res))))))))))))
axiom ax_13 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((depth l res_0) ∧ ((depth r res_1) ∧ (¬(res_0 > res_1) → ((1 + res_1) == res))))))))))))
axiom ax_14 : ∀ (t : itree), (∀ (res : Int), ((depth t res) → ((res > 0) → (is_node t))))
axiom ax_15 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res_0 : Int), (∀ (res_1 : Int), (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (((depth l res_0) ∧ ((depth r res_1) ∧ (res_0 > res_1))) → ((depth l res_0) → (∃ (res : Int), (((1 + res_0) == res) ∧ (depth t res)))))))))))
axiom ax_16 : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res_0 : Int), (∀ (res_1 : Int), (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((((depth l res_0) ∧ ((depth r res_1) ∧ ¬(res_0 > res_1))) ∧ (depth r res_1)) → (∃ (res : Int), (((1 + res_1) == res) ∧ (depth t res))))))))))

-- Proposed axioms (proved manually in test3.lean / test2.lean)
axiom ax_proposed : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res : Int), ((depth t res) → (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → (∃ (res_0 : Int), (∃ (res_1 : Int), ((((depth l res_0) ∧ (depth r res_1) ∧ res_0 < res ∧ res_1 < res )))))))))))
axiom ax_6_proposed : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res_0 : Int), (∀ (res_1 : Int), (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((( ((depth l res_0) ∧ ((depth r res_1) ∧ (res_0 > res_1)))) → ((depth l res_0) → (∃ (res : Int), (((1 + res_0) == res) ∧ (depth t res))))))))))))
axiom ax_9_proposed : ∀ (t : itree), (∀ (v : Int), (∀ (l : itree), (∀ (r : itree), (∀ (res_0 : Int), (∀ (res_1 : Int), (((is_node t) ∧ (((value t) == v) ∧ (((left t) == l) ∧ ((right t) == r)))) → ((((depth l res_0) ∧ ((depth r res_1) ∧ ¬(res_0 > res_1))) ∧ (depth r res_1)) → (∃ (res : Int), ((1 + res_1) == res) ∧ (depth t res)))))))))

end Axioms

-- ============================================================
-- Part 3: Failed subtyping check #0
-- ============================================================

axiom failed_subtyping_0 : ∀ (s : Int), ((0 <= s) → (∀ (v : itree), ((∃ (x_0 : Bool), (((x_0) ↔ (s == 0)) ∧ (¬(x_0) ↔ (s > 0)) ∧ (∃ (u : Int), ((depth v u) ∧ (u <= s))))) → (∃ (x_0 : Bool), (((x_0) ↔ (s == 0)) ∧ (¬(x_0) ↔ (s > 0)) ∧ (((x_0) ∧ (is_leaf v) ∧ (depth v 0)) ∨ (¬(x_0) ∧ (∃ (x_1 : Bool), (((x_1) ∧ (is_leaf v) ∧ (depth v 0)) ∨ (¬(x_1) ∧ (∃ (s_2 : Int), ((0 <= s_2) ∧ (s_2 >= 0) ∧ (s_2 < s) ∧ (s_2 == (s - 1)) ∧ (∃ (lt : itree), ((∃ (u : Int), ((depth lt u) ∧ (u <= s_2))) ∧ (∃ (s_3 : Int), ((0 <= s_3) ∧ (s_3 >= 0) ∧ (s_3 < s) ∧ (s_3 == (s - 1)) ∧ (∃ (rt : itree), ((∃ (u : Int), ((depth rt u) ∧ (u <= s_3))) ∧ (∃ (n : Int), ((is_node v) ∧ (((value v) == n) ∧ (((left v) == lt) ∧ ((right v) == rt)))))))))))))))))))))))

z3 failed_subtyping_0 only [ax_0, ax_2, ax_3, ax_11, ax_12, ax_13, ax_proposed]

-- ============================================================
-- Part 4: Failed subtyping check #146
-- ============================================================

axiom failed_subtyping_146 : ∀ (s : Int), ((0 <= s) → (∀ (v : itree), (
(∃ (idx1_0 : Int),((∃ (x_3 : Bool), ((((x_3) → (s == 0)) ∧ ((s == 0) → (x_3))) ∧ ((¬(x_3) → (s > 0)) ∧ ((s > 0) → ¬(x_3))) ∧ ¬(x_3))) ∧ (∃ (idx20_7 : itree), ((∃ (s_6 : Int), ((0 <= s_6) ∧ (s_6 >= 0) ∧ (s_6 < s) ∧ (s_6 == (s - 1)) ∧ (∃ (idx20 : itree), ((∃ (u : Int), ((depth idx20 u) ∧ (u <= s_6))) ∧ (idx20_7 == idx20))))) ∧ (∃ (idx20_8 : itree), ((∃ (s_6 : Int), ((0 <= s_6) ∧ (s_6 >= 0) ∧ (s_6 < s) ∧ (s_6 == (s - 1)) ∧ (∃ (idx20 : itree), ((∃ (u : Int), ((depth idx20 u) ∧ (u <= s_6))) ∧ (idx20_8 == idx20))))) ∧ (∃ (idx63 : itree), ((is_node idx63) ∧ ((value idx63) == idx1_0) ∧ ((left idx63) == idx20_7) ∧ ((right idx63) == idx20_8) ∧ (v == idx63))))))))) →
((∃ (x_3 : Bool), ((((x_3) → (s == 0)) ∧ ((s == 0) → (x_3))) ∧ ((¬(x_3) → (s > 0)) ∧ ((s > 0) → ¬(x_3))) ∧ ¬(x_3))) ∧ (¬(is_leaf v) ∧ ¬(s == 0)) ∧ (∃ (u : Int), ((depth v u) ∧ (u <= s)))))))

z3 failed_subtyping_146 only [ax_0, ax_11, ax_12, ax_13, ax_6_proposed, ax_9_proposed]
