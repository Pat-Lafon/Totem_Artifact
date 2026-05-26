import ProofAutomation

/-! # Tests.ProveAxiom — regression suite for `prove_axiom`.

The rbtree fixture is defined inside `namespace Tests.ProveAxiom` so the
inductive lives in the *current* file: `Helpers.isUserInductive` checks
`getModuleIdxFor? = none`, which is only true for same-file decls. An
imported `irbtree` would not be considered for the `cases` strategy. -/

namespace Tests.ProveAxiom

inductive irbtree where
  | Rbtleaf
  | Rbtnode (color : Bool) (left : irbtree) (value : Int) (right : irbtree)
  deriving DecidableEq

def is_rbtleaf : irbtree → Bool | .Rbtleaf => true | .Rbtnode _ _ _ _ => false
def is_rbtnode : irbtree → Bool | .Rbtleaf => false | .Rbtnode _ _ _ _ => true
def color : irbtree → Option Bool | .Rbtleaf => none | .Rbtnode c _ _ _ => some c
def value : irbtree → Option Int | .Rbtleaf => none | .Rbtnode _ _ v _ => some v
def left : irbtree → Option irbtree | .Rbtleaf => none | .Rbtnode _ l _ _ => some l
def right : irbtree → Option irbtree | .Rbtleaf => none | .Rbtnode _ _ _ r => some r

def num_black_impl : irbtree → Int → Bool
  | .Rbtleaf, h => h == 0
  | .Rbtnode c l _ r, h =>
    if ¬c then num_black_impl l (h - 1) && num_black_impl r (h - 1)
    else num_black_impl l h && num_black_impl r h
def num_black (t : irbtree) (h : Int) (res : Bool) : Prop := num_black_impl t h = res

def no_red_red_impl : irbtree → Bool
  | .Rbtleaf => true
  | .Rbtnode c l _ r =>
    if ¬c then no_red_red_impl l && no_red_red_impl r
    else match l, r with
      | .Rbtnode c' _ _ _, .Rbtnode c'' _ _ _ => !c' && !c'' && no_red_red_impl l && no_red_red_impl r
      | .Rbtnode c' _ _ _, .Rbtleaf => !c' && no_red_red_impl l
      | .Rbtleaf, .Rbtnode c'' _ _ _ => !c'' && no_red_red_impl r
      | .Rbtleaf, .Rbtleaf => true
def no_red_red (t : irbtree) (res : Bool) : Prop := no_red_red_impl t = res

def rbtree_invariant_impl (t : irbtree) (h : Int) : Bool :=
  no_red_red_impl t && num_black_impl t h
def rbtree_invariant (t : irbtree) (h : Int) (res : Bool) : Prop :=
  rbtree_invariant_impl t h = res

section TestProveAxiom
  attribute [local simp] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red
    rbtree_invariant_impl rbtree_invariant
  attribute [local grind cases] irbtree Bool
  attribute [local grind =] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red
    rbtree_invariant_impl rbtree_invariant

  -- Strategy 1 (grind).
  theorem test_prove_leaf : ∀ (t : irbtree), (∀ (h : Int), (∀ (res : Bool),
    ((num_black t h res) → ((is_rbtleaf t) → (((h == 0) ∧ (res)) ∨ (¬(h == 0) ∧ ¬(res))))))) := by
    prove_axiom

  -- Strategy 2 (cases + simp_all + grind), with existentials.
  theorem test_prove_node_exists : ∀ (t : irbtree), (∀ (h : Int), (∀ (c : Bool),
    (∀ (l : irbtree), (∀ (r : irbtree), (∀ (res : Bool),
    ((num_black t h res) → (((is_rbtnode t) ∧ (((color t) == c) ∧ (((left t) == l) ∧ ((right t) == r)))) →
    (¬(c) → (∃ (res_0 : Bool), ((num_black l (h - 1) res_0) →
    (∃ (res_1 : Bool), ((num_black r (h - 1) res_1) ∧
    ((((res_0) ∧ (res_1)) ∧ (res)) ∨ (¬((res_0) ∧ (res_1)) ∧ ¬(res))))))))))))))) := by
    prove_axiom

  -- rbtree_invariant decomposition (using color accessor).
  theorem test_prove_invariant : ∀ (t : irbtree), (∀ (h : Int), (∀ (res : Bool),
    ((rbtree_invariant t h res) → (∃ (res_10 : Bool), ((no_red_red t res_10) →
    (∃ (res_11 : Bool), ((num_black t h res_11) →
    (((is_rbtnode t) ∧ ((color t) == (some false)) ∧ res_10 ∧ res_11 ∧ res) ∨
    (¬((is_rbtnode t) ∧ ((color t) == (some false)) ∧ res_10 ∧ res_11) ∧ ¬res))))))))) := by
    prove_axiom

  -- Strategy 4 (early induction + simp_all + grind): num_black height
  -- non-negativity. Mirrors `ax_num_black_pos_proposed` from
  -- `integration_tests/rbtree/program_axioms.ml`. Strategies 1–3 cannot
  -- discharge this — the Rbtnode case needs the IH at `h - 1`, which only
  -- appears after `induction t` with `h` still quantified.
  theorem test_prove_num_black_pos : ∀ (t : irbtree), (∀ (h : Int),
    ((num_black t h true) → (h ≥ 0))) := by
    prove_axiom

end TestProveAxiom

end Tests.ProveAxiom

/-! ## Trust-anchor assertions

Any *new* axiom dependency surfacing here (especially `sorryAx` or
`z3SmtTrusted`) is a regression. -/

/-- info: 'Tests.ProveAxiom.test_prove_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.ProveAxiom.test_prove_leaf

/-- info: 'Tests.ProveAxiom.test_prove_node_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.ProveAxiom.test_prove_node_exists

/-- info: 'Tests.ProveAxiom.test_prove_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.ProveAxiom.test_prove_invariant

/-- info: 'Tests.ProveAxiom.test_prove_num_black_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.ProveAxiom.test_prove_num_black_pos
