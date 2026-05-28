import ProofAutomation

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

def num_black_impl : irbtree → Int → Bool
  | .Rbtleaf, h => h == 0
  | .Rbtnode c l _ r, h =>
    if ¬c then num_black_impl l (h - 1) && num_black_impl r (h - 1)
    else num_black_impl l h && num_black_impl r h

def num_black (t : irbtree) (h : Int) (res : Bool) : Prop :=
  num_black_impl t h = res

section Axioms
  attribute [local simp] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red
  attribute [local grind cases] irbtree Bool
  attribute [local grind =] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red

-- Axiom needed for the test
theorem ax_no_red_red_black_bwd : ∀ (t : irbtree) (c : Bool) (l r : irbtree) (res : Bool),
    (is_rbtnode t = true) → (color t = some c) → (left t = some l) → (right t = some r) →
    (¬c = true) →
    (∃ (res_4 : Bool), (no_red_red l res_4) ∧
      (∃ (res_5 : Bool), (no_red_red r res_5) ∧
        ((res_4 = true ∧ res_5 = true ∧ res = true) ∨ (¬(res_4 = true ∧ res_5 = true) ∧ res = false)))) →
    (no_red_red t res) := by prove_axiom

end Axioms

/-!
## Issue 1: accessor form derivation failure

The theorem below should be provable by propose_axiom but fails with:
  "proved constructor form but could not derive accessor form"

This is the exact theorem from test_rbnode_color_false_node.lean that fails.
-/

-- Minimal reproduction: propose_axiom on a goal involving red node + both subtrees.
-- Was failing because deriveAccessorForm's single-variable cases + simp_all left residual
-- match expressions when the definition (no_red_red_impl) pattern-matches on multiple
-- arguments. Fixed by adding a multi-cases strategy that case-splits all inductive vars.
example (t l' : irbtree) (v' : Int) (r' : irbtree)
    (h1 : ((is_rbtnode t = true ∧ color t = some true) ∧ left t = some l') ∧
           value t = some v' )
    (h2 : right t = some r')
    (h3 : no_red_red l' true)
    (h4 : is_rbtleaf l' = true ∨ is_rbtnode l' = true ∧ ¬(color l' == some true) = true)
    (h5 : no_red_red r' true)
    (h6 : is_rbtleaf r' = true ∨ is_rbtnode r' = true ∧ ¬(color r' == some true) = true)
    : no_red_red t true := by
  propose_axiom "ax_no_red_red_false_node_proposed" h1 h2 h3 h4 h5 h6

/-!
## Issue 2: cross-branch theorem registration

Theorems registered by propose_axiom in one case-split branch
should be accessible in sibling branches, but they aren't.
-/

-- This demonstrates the scoping issue:
-- After propose_axiom registers a theorem in the inl branch,
-- the inr branch cannot access it by name.
example (h : True ∨ True) : True := by
  cases h with
  | inl _ =>
    -- If propose_axiom registered "my_thm" here, it would be
    -- available within this branch but NOT in the inr branch below.
    trivial
  | inr _ =>
    -- exact my_thm  -- would fail: unknown identifier
    trivial

/-!
## Issue 3: simp_hyps should split Iff

`simp_hyps` should split `h : A ↔ B` into its forward and backward
implications so they can be specialized by subsequent iterations.
-/

-- Iff gets split into two fresh-named implications, then trivial premises specialized
example (h : true = true ↔ (0 == 0) = true) : (0 == 0) = true := by
  simp_hyps
  simp

-- Iff with non-trivial sides: both directions become available with fresh names
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  simp_hyps  -- splits h into h_N : P → Q and h_M : Q → P, specializes with hp
  assumption
