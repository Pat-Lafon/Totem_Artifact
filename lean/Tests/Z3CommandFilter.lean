import ProofAutomation

/-! # Tests.Z3CommandFilter — `only [...]` filter error contracts.

Split from `Tests.Z3Command` so the `Available axioms` list pinned in
`#guard_msgs` stays stable: `gatherUserAxioms` walks the entire current
module's env, and any sibling `ax_<n>` in the same file leaks into the
error message. Each test here owns a single-axiom env. -/

namespace Tests.Z3CommandFilter

namespace Axioms
theorem ax_only : (1 : Int) = 1 := rfl
end Axioms
open Axioms

theorem test_thm : (1 : Int) = 1 := rfl

-- Unresolved ident — distinct error from the resolves-but-not-in-pool case.
-- The wrapper appends the underlying resolver message (`Unknown constant …`
-- here; would be `Ambiguous identifier …` for an overload clash) so the user
-- can tell the two failure modes apart.
/--
error: z3: failed to resolve axiom name 'no_such_axiom': Unknown constant `no_such_axiom`
Available axioms: [Tests.Z3CommandFilter.Axioms.ax_only]
-/
#guard_msgs in z3 Tests.Z3CommandFilter.test_thm only [no_such_axiom]

-- Name resolves but isn't in the Axioms namespace — second branch of decision 9.
theorem not_an_axiom : True := trivial
/--
error: z3: name 'not_an_axiom' resolves to 'Tests.Z3CommandFilter.not_an_axiom' but isn't in the current-file Axioms namespace.
Available axioms: [Tests.Z3CommandFilter.Axioms.ax_only]
-/
#guard_msgs in z3 Tests.Z3CommandFilter.test_thm only [not_an_axiom]

end Tests.Z3CommandFilter
