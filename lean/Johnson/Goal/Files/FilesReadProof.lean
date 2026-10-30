-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Files/FilesReadProof.lean: `FilesRead` (Ladder.lean) as a theorem: the two named sets
of public files (`storedPublicFiles`, `zGap`, Ladder/Stored.lean) are in scope of the goals and are read as
expected: the first states exact match, the second the policy (25856, 512, 1). One theorem.

  **`VerifierAndGoals.filesRead : FilesRead`**: by `Read.scope_of_check` (Ladder/FilesReadLaws.lean) at the
    tests that the kernel has evaluated (Johnson/Goal/Files/FilesReadChecks.lean).

What it buys. `G3'pol` asks nothing unless the named files are in scope and read; the ties
that speak of the stored full-size files by name (`nearest…_at_full`, the two bars,
Ladder/PackageTies.lean) take `FilesRead` as a premise. Ladder/Guards.lean checks it by evaluation
alone. This theorem gives that premise.

Limits. It speaks of the bytes written in Ladder/Stored.lean. That they are the bytes of the
top-level folder examples/ is not said. It says nothing of any description or verifier: no goal is
met by it.

-/
import Johnson.Goal.Files.FilesReadChecks

set_option autoImplicit false

namespace VerifierAndGoals

/- The next three are true by definition. They are stated apart, each with the named file unfolded
first: left to find them by itself, Lean compares the two parameter files byte by byte and runs out
of stack. -/

/-- The stored full-size example's parameter file is `policyFile` at the stored free numbers. -/
theorem pol_zFull : storedPublicFiles.pol = policyFile storedLines := by
  unfold storedPublicFiles
  rfl

/-- The second named set has the stored layout file. -/
theorem lay_zGap : zGap.lay = storedPublicFiles.lay := by
  unfold zGap
  dsimp only

/-- Its parameter file is `policyFile` at its free numbers. -/
theorem pol_zGap : zGap.pol = policyFile Read.gapLines := by
  unfold zGap Read.gapLines
  rfl

/-- **The two named sets of public files are in scope and are read as expected.** -/
theorem filesRead : FilesRead where
  full := Read.scope_of_check (Z := storedPublicFiles) (v := storedLines) (Eq.refl storedPublicFiles.lay) pol_zFull
    Read.polFull Read.klFull
  other := Read.scope_of_check (Z := zGap) (v := Read.gapLines) lay_zGap pol_zGap Read.polGap
    Read.klGap

end VerifierAndGoals

#print axioms VerifierAndGoals.Read.polScan_eq
#print axioms VerifierAndGoals.Read.klFileOf_eq
#print axioms VerifierAndGoals.Read.scope_of_check
#print axioms VerifierAndGoals.Read.klWord_wordsFile
#print axioms VerifierAndGoals.Read.klFull
#print axioms VerifierAndGoals.Read.klGap
#print axioms VerifierAndGoals.filesRead
