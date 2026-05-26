# CLAUDE.md — `lean/`

Project-level Lean 4 workspace. Hosts the `ProofAutomation` library plus
ad-hoc test/debug files (failed subtyping queries dumped from Cobb,
counterexample searches, scratch experiments).

The Lake package is defined at `../lakefile.lean`. Three `lean_lib`s live
under `srcDir := "lean"`:

- `ProofAutomation` (root `ProofAutomation`) — the tactic library.
- `test_rbtree_typecheck_timeout` (root `test_rbtree_typecheck_timeout`) —
  one specific failed subtyping query, exposed as a lib so other files
  can import it.
- `Tests` (root `Tests`) — the regression test suite, run via
  `lake test`.

Toolchain: `../lean-toolchain` (currently Lean v4.28.0). The package
requires `plausible` from git (currently pinned at `v4.28.0`).

## Layout

- `ProofAutomation.lean` — umbrella import (re-exports every submodule).
- `ProofAutomation/` — library source. One module per tactic/command.
- `test*.lean` — failed subtyping query dumps from Cobb (mostly with
  `sorry` in places where the proof got stuck). Most are scratch — only
  `test_rbtree_typecheck_timeout.lean` is currently exposed as a
  buildable lib (so PBT can `import` it).
- `Tests/` — regression tests for the tactics in `ProofAutomation/`,
  run via `lake test`. Treat as the canonical usage examples. See the
  "Test suite" section below for the per-module breakdown.

## PBT counterexample workflow

`ProofAutomation/PBT.lean` re-exports `Plausible` and ships the universal
low-priority `Shrinkable` fallback used by every PBT-running file. Two
entry points consume it:

- **`Tests/PBT.lean`** — the regression suite: four `#guard_msgs (error)`
  examples mirroring `sorry` sites in `test_rbtree_typecheck_timeout.lean`.
  Uses `Plausible.Configuration.quiet := true` so the asserted error is
  the deterministic `Found a counter-example!`.
- **`ProofAutomation/ProposeCounterexample.lean`** — the tactic: runs PBT
  at the current proof state, lifts the witness to outer-theorem
  variables, and emits a paste-ready `¬ outer` proof scaffold. Leaves
  are `sorry` for the user to complete.

Per-datatype setup (e.g. `Decidable num_black t h res` / `no_red_red t res`)
lives in each test file because Plausible's `Testable` synth doesn't
unfold `def`-wrapped predicates.

## ProofAutomation modules

Each tactic lives in its own file under `ProofAutomation/`. All depend on
`Helpers.lean`.

| File | Provides | Purpose |
|---|---|---|
| `Helpers.lean` | name/env predicates, tactic combinators, `ProofAutomation.Trusted.z3SmtTrusted` | Shared utilities. `isAxiomName` recognizes Cobb-Totem `ax_<n>` theorems. Trust axiom is the shared TCB anchor for SMT-dispatching tactics (`z3_local`); surfaces in `#print axioms`. |
| `OcamlFormat.lean` | `ppOcamlType`, expression printers | Pretty-print Lean exprs back to OCaml-shaped syntax (used by `propose_axiom`). |
| `ProveAxiom.lean` | `prove_axiom` | Multi-strategy auto-prover for Cobb-shaped axioms (grind → simp_all+grind → cases+simp_all+grind → early induction). |
| `ProposeAxiom.lean` | `propose_axiom` | Formulate an axiom from current hypotheses, prove it, print it in OCaml syntax, and apply it. |
| `SearchAxioms.lean` | `search_axioms [goal\|hyps\|h]` | Find applicable axioms by unifying axiom premises/conclusions against hypotheses or the goal. |
| `SimpHyps.lean` | `simp_hyps` | Iterate: destruct ∧, normalize BEq, specialize implications, clear contradicted implications, close by false hypothesis. |
| `SimpGoal.lean` | `simp_goal` | Goal-side analogue of `simp_hyps`: phase-array loop that splits ∧, auto-witnesses ∃ via equality conjuncts, picks the live branch of `∨`, and finishes with `grind`. |
| `RefineExistsEq.lean` | `refine_exists_eq` | If `∃ x, P[x]` has a pinning equality `x = e` / `(x == e) = true`, refine with `e`. |
| `Z3Tactic.lean` | `z3 thm [only [ax₁, …]]` command (+ `z3?` / `z3!` / `z3!?` variants) | Translate goal + auto-collected current-file `ax_<n>` axioms to SMT-LIB and dispatch to Z3. `only [...]` restricts the auto-collected pool. SMT file written under `/tmp/` for inspection. |
| `Z3Local.lean` | `z3_local`, `z3_local only [ax_<n>,*]` tactic | Tactic-mode SMT dispatch: folds current lctx + main target into a closed conjecture, gathers `ax_<n>` theorems (optionally restricted by `only [...]`), dispatches to Z3, closes via `z3SmtTrusted` on `unsat`. Use `clear` to drop lctx hypotheses. |

## Conventions

- All tactics assume Cobb-Totem-shaped terms: `let[@axiom]` lowered into
  Lean theorems under a `namespace Axioms` block (so the fully-qualified
  name has `Axioms` as some prefix component), with wrapper predicates
  marked `@[simp, grind =]`. `Helpers.isAxiomName` is the scoping filter
  — it accepts any name with `Axioms` anywhere in its hierarchical
  prefix (`Axioms.ax_0`, `Tests.Z3Command.Axioms.ax_zero`).
- **Leaf-file rule:** files containing a `namespace Axioms ... end
  Axioms` block must not be imported by any other Lean module. Cross-
  file `Axioms.foo` collisions would otherwise surface as `addDecl`
  errors at the importer. Lean cannot enforce this — keep `Axioms`
  blocks out of `ProofAutomation/` (every leaf file imports it) and
  confined to scratch/test/dump leaf files.
- The umbrella import `ProofAutomation` is what scratch/test files (and
  the dumped subtyping queries) import. New tactics must be added to
  `ProofAutomation.lean`.
- The shared preamble for dumped subtyping queries lives in
  `Cobb/underapproximation_type/data/predefined/lean_preamble*.lean` and
  imports `ProofAutomation`. Keep tactic surface stable so dumped files
  keep building.

## Workflow

After editing any `.lean` file under this directory, verify it builds
before claiming the change is correct (per the root CLAUDE.md).

```bash
# Run the full regression suite (canonical).
lake test                                         # builds the `Tests` lib

# Targeted library builds (from repo root)
lake build ProofAutomation
lake build Tests.ProveAxiom                       # one test module
lake build test_rbtree_typecheck_timeout

# Single-file check (works for scratch test files not exposed as libs)
lake env lean lean/ProofAutomation/SimpHyps.lean
```

The `lean-lsp` MCP tools (`lean_diagnostic_messages`, `lean_goal`,
`lean_multi_attempt`, etc.) are the preferred way to iterate on proofs
without round-tripping through the build.

### Test suite (`lean/Tests/`)

Wired as `testDriver := "Tests"` in `lakefile.lean`. Each file mirrors a
`ProofAutomation/` module and asserts via `#guard_msgs` so regressions
fail the build:

- `ProveAxiom`, `SimpHyps`, `SimpGoal`, `ProposeAxiom`, `RefineExistsEq`
  — tactic correctness + `#print axioms` snapshots pinning trust anchors.
- `Z3Local` — requires Z3 on PATH; asserts every proof depends on
  `ProofAutomation.Trusted.z3SmtTrusted` (and nothing else).
- `Z3Command`, `Z3CommandFilter` — command-mode `z3` happy paths,
  excludeName preservation, untranslatable-axiom contract, and
  `only [...]` filter error messages. Filter tests are split into their
  own file so the env-pool stays single-axiom and the
  `Available axioms:` list pinned in errors stays stable.
- `Snapshots` — `ppOcamlAxiom`, `search_axioms` output.
- `PBT` — Plausible counterexample refutation using
  `Plausible.Configuration.quiet := true` so the resulting error is the
  deterministic `Found a counter-example!`, asserted via
  `#guard_msgs (error)`.
- `ProposeCounterexample` — paired per-outer regression: a closed
  `¬ outer` proof confirming the spec is genuinely refutable, plus a
  `propose_counterexample` smoke test guarded by
  `#guard_msgs(drop info, drop warning)` (asserts no throw, does NOT
  pin scaffold text).

Each test file is wrapped in its own `namespace Tests.<Module>` and
inlines the rbtree (or other) fixture. This is deliberate:
`Helpers.isUserInductive` requires inductives declared in the *current*
file (`getModuleIdxFor? = none`); imported inductives would be skipped
by `prove_axiom`'s `cases` strategy.

## When adding a new tactic

1. Create `ProofAutomation/<Name>.lean` with `import ProofAutomation.Helpers`.
2. Add `import ProofAutomation.<Name>` to `ProofAutomation.lean`.
3. Add regression cases to `Tests/<Name>.lean` (mirror the module name,
   wrap in `namespace Tests.<Name>`, assert via `#guard_msgs`).
4. Verify with `lake build ProofAutomation` and `lake test`.
