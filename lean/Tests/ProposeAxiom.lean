import ProofAutomation

/-! # Tests.ProposeAxiom — regression suite for `propose_axiom`.

Fixtures inlined in this file's namespace so the rbtree inductive is
defined in the *current* module — `propose_axiom`'s internal
`prove_axiom` call needs same-file inductives to fire its `cases`
strategy. -/

namespace Tests.ProposeAxiom

inductive irbtree where
  | Rbtleaf
  | Rbtnode (color : Bool) (left : irbtree) (value : Int) (right : irbtree)
  deriving DecidableEq

def is_rbtleaf : irbtree → Bool | .Rbtleaf => true | .Rbtnode _ _ _ _ => false
def is_rbtnode : irbtree → Bool | .Rbtleaf => false | .Rbtnode _ _ _ _ => true
def color : irbtree → Option Bool | .Rbtleaf => none | .Rbtnode c _ _ _ => some c

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

section TestProposeAxiom
  attribute [local simp] is_rbtleaf is_rbtnode color no_red_red_impl no_red_red
  attribute [local grind cases] irbtree Bool
  attribute [local grind =] is_rbtleaf is_rbtnode color no_red_red_impl no_red_red

  -- Simple axiom formulated + proved from one hypothesis.
  theorem test_propose_simple :
      ∀ (v : irbtree), is_rbtnode v = true → (color v == some false) = true →
        is_rbtleaf v = false := by
    intros v h1 _h2
    propose_axiom "test_ax" h1

  -- Nested-constructor shape: hypothesis and goal both mention
  -- `Rbtnode true (Rbtnode c l v r) v' r'`. Reproducer for
  -- Scenarios/test_rbtree_typecheck_timeout.lean:390.
  theorem test_propose_nested_accessor (v' : Int) (r' : irbtree) (c : Bool) (l : irbtree) (v : Int) (r : irbtree)
      (h_16 : no_red_red (irbtree.Rbtnode true (irbtree.Rbtnode c l v r) v' r') true) :
      no_red_red (irbtree.Rbtnode c l v r) true := by
    propose_axiom "test_ax_nested_accessor" h_16

end TestProposeAxiom

end Tests.ProposeAxiom

/-! ## Trust-anchor assertions -/

/-- info: 'Tests.ProposeAxiom.test_propose_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.ProposeAxiom.test_propose_simple

/-- info: 'Tests.ProposeAxiom.test_propose_nested_accessor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Tests.ProposeAxiom.test_propose_nested_accessor
