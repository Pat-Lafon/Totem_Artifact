import ProofAutomation.PBT

-- Plausible's `Testable` synth on these propositions exceeds the default 128.
-- Error explicitly recommends bumping `synthInstance.maxSize` to a higher
-- power of two. 256 is sufficient for every example below.
set_option synthInstance.maxSize 256

/-! # Tests.PBT — regression suite for PBT-based counterexample refutation.

Four examples mirroring `sorry` sites in
`Scenarios/test_rbtree_typecheck_timeout.lean`. Uses `Plausible.Configuration.quiet
:= true` so the resulting error is the deterministic bare message
`Found a counter-example!`. Each `example` is wrapped in `#guard_msgs
(error) in`, which makes "PBT still refutes" a build-time assertion
rather than a manual eyeball check on `lake build` errors.

If PBT stops refuting (e.g. because shrinker / generator changes mask the
counterexample), the expected `error: Found a counter-example!` won't fire
and `lake test` will report the snapshot mismatch — that's the regression
signal. -/

namespace Tests.PBT

inductive irbtree where
  | Rbtleaf
  | Rbtnode (color : Bool) (left : irbtree) (value : Int) (right : irbtree)
  deriving DecidableEq, Repr

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

def color : irbtree → Option Bool | .Rbtleaf => none | .Rbtnode c _ _ _ => some c

-- Plausible's `Testable` synth doesn't unfold `def`-wrapped predicates, so
-- supply `Decidable` + `PrintableProp` instances explicitly.
instance (t : irbtree) (h : Int) (res : Bool) : Decidable (num_black t h res) :=
  inferInstanceAs (Decidable (num_black_impl t h = res))
instance (t : irbtree) (res : Bool) : Decidable (no_red_red t res) :=
  inferInstanceAs (Decidable (no_red_red_impl t = res))
instance (t : irbtree) (h : Int) (res : Bool) : Plausible.PrintableProp (num_black t h res) :=
  inferInstanceAs (Plausible.PrintableProp (num_black_impl t h = res))
instance (t : irbtree) (res : Bool) : Plausible.PrintableProp (no_red_red t res) :=
  inferInstanceAs (Plausible.PrintableProp (no_red_red_impl t = res))

deriving instance Plausible.Arbitrary for irbtree
-- Universal `Shrinkable` fallback is provided by `ProofAutomation.PBT`.

/-! ### Counterexample refutations

Each `example` mirrors a `sorry` site in
`Scenarios/test_rbtree_typecheck_timeout.lean`. PBT finds a witness that satisfies
the local hypotheses but falsifies the goal — i.e. refutes the spec. The
`#guard_msgs` block asserts the deterministic "Found a counter-example!"
error fires. -/

-- timeout.lean:405 — outer goal in the `c = false` branch.
/-- error: Found a counter-example! -/
#guard_msgs in
example (inv h : Int) (l' r' : irbtree) (v' : Int) :
    inv ≥ 0 → h > 0 → h + h + 1 = inv →
    num_black (.Rbtnode false l' v' r') h true →
    no_red_red (.Rbtnode false l' v' r') true →
    num_black l' h true := by
  plausible (config := { numInst := 10000, maxSize := 30, quiet := true })

-- timeout.lean:417 — symmetric to :405, right side.
/-- error: Found a counter-example! -/
#guard_msgs in
example (inv h : Int) (l' r' : irbtree) (v' : Int) :
    inv ≥ 0 → h > 0 → h + h + 1 = inv →
    num_black (.Rbtnode false l' v' r') h true →
    no_red_red (.Rbtnode false l' v' r') true →
    num_black r' h true := by
  plausible (config := { numInst := 10000, maxSize := 30, quiet := true })

-- timeout.lean:414 — after `cases l' with | Rbtnode c l v r => ...`
/-- error: Found a counter-example! -/
#guard_msgs in
example (inv h v' : Int) (r' : irbtree) (c : Bool) (l : irbtree) (v : Int) (r : irbtree) :
    inv ≥ 0 → h > 0 → h + h + 1 = inv →
    num_black (.Rbtnode false (.Rbtnode c l v r) v' r') h true →
    no_red_red (.Rbtnode false (.Rbtnode c l v r) v' r') true →
    ¬(color (.Rbtnode c l v r) == some true) = true := by
  plausible (config := { numInst := 50000, maxSize := 10, quiet := true })

-- timeout.lean:432 — symmetric to :414, right side.
/-- error: Found a counter-example! -/
#guard_msgs in
example (inv h v' : Int) (l' : irbtree) (c : Bool) (l : irbtree) (v : Int) (r : irbtree) :
    inv ≥ 0 → h > 0 → h + h + 1 = inv →
    num_black (.Rbtnode false l' v' (.Rbtnode c l v r)) h true →
    no_red_red (.Rbtnode false l' v' (.Rbtnode c l v r)) true →
    ¬(color (.Rbtnode c l v r) == some true) = true := by
  plausible (config := { numInst := 50000, maxSize := 10, quiet := true })

/-! ### auto_pbt_decidable smoke test

Sweep registers `Decidable` for `num_black` and `no_red_red`. The
hand-written instances above keep working; the sweep adds parallel
`num_black.autoDecidable` / `no_red_red.autoDecidable` entries.

`#guard_msgs(drop info, drop warning)` asserts that the sweep runs
without throwing; the explicit `inferInstance` lines afterward confirm
the registered instances are actually findable. -/

#guard_msgs(drop info, drop warning) in
auto_pbt_decidable

example : Decidable (num_black .Rbtleaf 0 true) := inferInstance
example : Decidable (no_red_red .Rbtleaf true) := inferInstance

end Tests.PBT
