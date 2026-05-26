/-
  PBT.lean — Type-agnostic Plausible setup for counterexample search.

  Re-exports `Plausible` and ships the universal low-priority Shrinkable
  fallback so custom datatypes don't need per-type opt-in. Plausible's
  specific shrinkers (`Int`, `Bool`, …) keep their default priority and
  still win where declared.

  Datatype-specific routing (e.g. `Decidable num_black` / `no_red_red`
  for rbtree) lives in the test file or per-feature module. Note: the
  inlined fixtures in `Tests/PBT.lean` are required, not redundant —
  `prove_axiom`'s `cases` strategy depends on same-file inductives (see
  `CLAUDE.md` "Test suite" section).
-/
import Plausible

instance (priority := low) {α : Type _} : Plausible.Shrinkable α := {}

/- Forward `Decidable` / `PrintableProp` through `Plausible.NamedBinder`.

`Plausible.NamedBinder n p` is semantically `p`, but the wrapper is a `def`
(not `abbrev`), so instance resolution does not unfold it. Without these
two forwarders, `decGuardTestable`'s `[Decidable p]` premise cannot be
discharged when `p` itself is a propositional implication, even though
`Decidable.implies` exists for `Decidable P → Decidable Q → Decidable (P → Q)`.
Diagnostic walk: see `TODO_Counterexamples.md` "T2" entry. -/

instance (n : String) (p : Prop) [d : Decidable p] :
    Decidable (Plausible.NamedBinder n p) := d

instance (n : String) (p : Prop) [pr : Plausible.PrintableProp p] :
    Plausible.PrintableProp (Plausible.NamedBinder n p) := pr
