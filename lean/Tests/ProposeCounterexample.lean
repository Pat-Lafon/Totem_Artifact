import ProofAutomation

/-! # Tests.ProposeCounterexample — regression suite for `propose_counterexample`. -/

set_option synthInstance.maxSize 256

namespace Tests.ProposeCounterexample

/-! ## `Int`-shaped outers (`∧`, `∨`) -/

axiom bad_thm : ∀ (n : Int), n ≥ 0 → n + 1 ≥ 0 ∧ n = 0

example : ¬ (∀ (n : Int), n ≥ 0 → n + 1 ≥ 0 ∧ n = 0) := by
  intro H
  have H1 := H 1 (by native_decide)
  obtain ⟨_, h_1⟩ := H1
  exact absurd h_1 (by native_decide)

/--
info: propose_counterexample produced scaffold:

-- spec-bug refutation candidate for `Tests.ProposeCounterexample.bad_thm`
example : ¬ (∀ (n : Int), n ≥ 0 → n + 1 ≥ 0 ∧ n = 0) := by
  intro H
  have H1 := H 1 (by first | native_decide | grind | sorry)
  first | (simp_hyps; done) | sorry
-/
#guard_msgs(info, drop warning) in
example (n : Int) (_h1 : n ≥ 0) : n + 1 ≥ 0 ∧ n = 0 := by
  propose_counterexample bad_thm 42
 sorry
axiom bad_thm3 : ∀ (n : Int), n ≥ 0 → (n = 0) ∨ (n < 0)

example : ¬ (∀ (n : Int), n ≥ 0 → (n = 0) ∨ (n < 0)) := by
  intro H
  have H1 := H 1 (by native_decide)
  rcases H1 with h_0 | h_1
  · exact absurd h_0 (by native_decide)
  · exact absurd h_1 (by native_decide)

/--
info: propose_counterexample produced scaffold:

-- spec-bug refutation candidate for `Tests.ProposeCounterexample.bad_thm3`
example : ¬ (∀ (n : Int), n ≥ 0 → n = 0 ∨ n < 0) := by
  intro H
  have H1 := H 1 (by first | native_decide | grind | sorry)
  rcases H1 with h_0 | h_1
  ·
    first | (simp_hyps; done) | sorry
  ·
    first | (simp_hyps; done) | sorry
-/
#guard_msgs(info, drop warning) in
example (n : Int) (_h1 : n ≥ 0) : (n = 0) ∨ (n < 0) := by
  propose_counterexample bad_thm3 42
 sorry
/-! ## rbtree-shaped outer with a case-split.

`buildSigma` falls back to `recoverCaseSplitWitness` for binders missing
from the local context. Recovery uses the goal's case tag to name the
constructor; for 0-arity constructors the witness is the constructor
itself, for positive-arity it scans the lctx for a contiguous window of
fvars whose types line up with the constructor's signature.

When recovery can't reconstruct the witness (the outer's binder was
specialized at the signature level, not by an in-proof `cases`), the
tactic falls through to the original hard error. -/

inductive irbtree where
  | Rbtleaf
  | Rbtnode (color : Bool) (left : irbtree) (value : Int) (right : irbtree)
  deriving DecidableEq, Repr

def num_black_impl : irbtree → Int → Bool
  | .Rbtleaf, h => h == 0
  | .Rbtnode c l _ r, h =>
    if ¬c then num_black_impl l (h - 1) && num_black_impl r (h - 1)
    else num_black_impl l h && num_black_impl r h
@[reducible] def num_black (t : irbtree) (h : Int) (res : Bool) : Prop :=
  num_black_impl t h = res

deriving instance Plausible.Arbitrary for irbtree

axiom bad_rbtree : ∀ (h : Int) (t : irbtree),
  h > 0 → num_black t h true →
    ∃ (l r : irbtree) (v : Int), t = .Rbtnode false l v r ∧ num_black l h true

example : ¬ (∀ (h : Int) (t : irbtree),
    h > 0 → num_black t h true →
      ∃ (l r : irbtree) (v : Int), t = .Rbtnode false l v r ∧ num_black l h true) := by
  intro H
  have H1 := H 1 (.Rbtnode false .Rbtleaf 0 .Rbtleaf) (by decide) (by decide)
  obtain ⟨_, _, _, h_eq, h_nb⟩ := H1
  injection h_eq with _ h_l _ _
  subst h_l
  exact absurd h_nb (by decide)

/--
error: propose_counterexample: outer binders not present in local context (likely case-split during proof): t
The outer is `Tests.ProposeCounterexample.bad_rbtree`. Either `intro`/rename to expose these binders locally, or hand-construct the refutation using the witnesses below.
  PBT witnesses available:
    l' := Tests.ProposeCounterexample.irbtree.Rbtleaf
    h := 1
    v' := 0
    r' := Tests.ProposeCounterexample.irbtree.Rbtleaf
-/
#guard_msgs(error, drop info, drop warning) in
example (h : Int) (l' r' : irbtree) (v' : Int) :
    h > 0 → num_black (.Rbtnode false l' v' r') h true →
    num_black l' h true := by
  intros
  propose_counterexample bad_rbtree 42
 sorry
/-! ### Case-split recovery: 0-arity constructor.

When the outer's binder is consumed by `cases ... with | Ctor =>` and the
constructor takes no fields, `recoverCaseSplitWitness` produces the bare
constructor as the witness. -/

axiom case_split_outer : ∀ (t : irbtree), t = .Rbtleaf → False

/--
info: propose_counterexample produced scaffold:

-- spec-bug refutation candidate for `Tests.ProposeCounterexample.case_split_outer`
example : ¬ (∀ (t : irbtree), t = irbtree.Rbtleaf → False) := by
  intro H
  have H1 := H Tests.ProposeCounterexample.irbtree.Rbtleaf (by first | native_decide | grind | sorry)
  first | (simp_hyps; done) | sorry
-/
#guard_msgs(info, drop warning) in
example (t : irbtree) (_h : t = .Rbtleaf) : False := by
  cases t with
  | Rbtleaf =>
    propose_counterexample case_split_outer 42
   sorry  | Rbtnode _ _ _ _ => cases _h

/-! ### Case-split recovery: positive-arity constructor + witness substitution.

When `cases t with | Rbtnode c l v r => ...` consumes the outer's binder
and a subsequent `refine` buries `Rbtnode` mid-tag, recovery scans every
tag component for a matching ctor. Field-window fvars (`c`, `l`, `v`, `r`)
are then substituted with their PBT witness values so the scaffold
compiles standalone — `(irbtree.Rbtnode <w_c> <w_l> <w_v> <w_r>)` rather
than `(irbtree.Rbtnode c l v r)` (the bare fvars would be unbound when
the scaffold is pasted outside the proof). -/

axiom positive_arity_outer : ∀ (t : irbtree), t = irbtree.Rbtleaf

/--
info: propose_counterexample produced scaffold:

-- spec-bug refutation candidate for `Tests.ProposeCounterexample.positive_arity_outer`
example : ¬ (∀ (t : irbtree), t = irbtree.Rbtleaf) := by
  intro H
  have H1 := H (Tests.ProposeCounterexample.irbtree.Rbtnode true Tests.ProposeCounterexample.irbtree.Rbtleaf 0 Tests.ProposeCounterexample.irbtree.Rbtleaf)
  first | (simp_hyps; done) | sorry
-/
#guard_msgs(info, drop warning) in
example (t : irbtree) : t = irbtree.Rbtleaf ∧ True := by
  cases t with
  | Rbtleaf => exact ⟨rfl, trivial⟩
  | Rbtnode c l v r =>
    refine ⟨?_, ?_⟩
    · propose_counterexample positive_arity_outer 42
     sorry    · trivial

/-! ## No-ident form: in-body invocation auto-detects the enclosing theorem.

The tactic recovers the enclosing decl's name via `Term.getDeclName?` and its
type by scanning the metavariable context (`findRootOuterType`). Tested on
both params-after-colon and params-before-colon signatures. -/

/--
info: propose_counterexample produced scaffold:

-- spec-bug refutation candidate for `Tests.ProposeCounterexample.in_body_after_colon`
example : ¬ (∀ (n : Int), n ≥ 0 → n + 1 ≥ 0 ∧ n = 0) := by
  intro H
  have H1 := H 1 (by first | native_decide | grind | sorry)
  first | (simp_hyps; done) | sorry
-/
#guard_msgs(info, drop warning) in
theorem in_body_after_colon : ∀ (n : Int), n ≥ 0 → n + 1 ≥ 0 ∧ n = 0 := by
  intro n _
  propose_counterexample 42
 sorry
/--
info: propose_counterexample produced scaffold:

-- spec-bug refutation candidate for `Tests.ProposeCounterexample.in_body_before_colon`
example : ¬ (∀ (n : Int), n ≥ 0 → n + 1 ≥ 0 ∧ n = 0) := by
  intro H
  have H1 := H 1 (by first | native_decide | grind | sorry)
  first | (simp_hyps; done) | sorry
-/
#guard_msgs(info, drop warning) in
theorem in_body_before_colon (n : Int) (_h1 : n ≥ 0) : n + 1 ≥ 0 ∧ n = 0 := by
  propose_counterexample 42
 sorry
/-! ## Nested-implication premises: NamedBinder forwarding (`PBT.lean` instances).

Pre-fix, `Testable` synth on `(P → Q) → R` shapes — produced when a Cobb-shaped
spec like `(clr → P) ∧ (¬clr → Q)` gets destructured by `simp_hyps` into two
separate implication hypotheses and then reverted — failed because
`NamedBinder n (P → Q)` blocked `Decidable.implies` resolution. The forwarding
instances in `ProofAutomation/PBT.lean` unblock the pathway. -/

/--
info: propose_counterexample produced scaffold:

-- spec-bug refutation candidate for `Tests.ProposeCounterexample.nested_impl_outer`
example : ¬ (∀ (inv : Int),
  0 ≤ inv → ∀ (clr : Bool) (h : Int), 0 ≤ h → (clr = true → h + h = inv) → (clr = false → h + h + 1 = inv) → False) := by
  intro H
  have H1 := H 0 (by first | native_decide | grind | sorry) true 0 (by first | native_decide | grind | sorry) (by first | native_decide | grind | sorry) (by first | native_decide | grind | sorry)
  first | (simp_hyps; done) | sorry
-/
#guard_msgs(info, drop warning) in
theorem nested_impl_outer : ∀ (inv : Int), 0 ≤ inv → ∀ (clr : Bool) (h : Int),
    0 ≤ h → (clr = true → h + h = inv) → (clr = false → h + h + 1 = inv) → False := by
  intro inv _ clr h _ _ _
  propose_counterexample 42
 sorry
/-! ## Error-path coverage (PBT-budget exhaustion + `synthInstance?` failure) -/

axiom triv_outer : ∀ (n : Int), n = n

/--
error: propose_counterexample: PBT did not find a counterexample within budget
-/
#guard_msgs(error, drop info, drop warning) in
example : True := by
  propose_counterexample triv_outer

opaque P : Int → Prop

/--
error: propose_counterexample: could not synthesize
  Plausible.Testable Plausible.NamedBinder "n" (∀ (n : Int), P n)
-/
#guard_msgs(error, drop info, drop warning) in
example : ∀ (n : Int), P n := by
  propose_counterexample triv_outer

end Tests.ProposeCounterexample
