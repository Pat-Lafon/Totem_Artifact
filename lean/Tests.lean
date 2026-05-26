import Tests.ProveAxiom
import Tests.SimpHyps
import Tests.ProposeAxiom
import Tests.SimpGoal
import Tests.RefineExistsEq
import Tests.Z3Local
import Tests.Z3Command
import Tests.Z3CommandFilter
import Tests.Snapshots
import Tests.PBT

/-! # Tests — regression suite for `ProofAutomation`.

Driven by `lake test` (see `package.testDriver` in `lakefile.lean`). Each
sub-module mirrors a module in `ProofAutomation/`; assertions are encoded
inline via `example`, `#guard`, and `#guard_msgs` so a successful
`lake build Tests` means all regressions pass. -/
