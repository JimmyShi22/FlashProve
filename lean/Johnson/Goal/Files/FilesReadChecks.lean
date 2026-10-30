-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Files/FilesReadChecks.lean: the tests of Ladder/FilesReadLaws.lean evaluated by Lean's
kernel at the two named sets of public files (`storedPublicFiles`, `zGap`, Ladder/Stored.lean). Statements with
proofs.

Main names (namespace `VerifierAndGoals.Read`).
  `kl_zFull`, `kl_zGap`: by definition the stored scale file is `wordsFile scalesF`
    (OnBytes/Tie/Pv/Plan/PlanKits.lean), and the second named set has the same scale file.
  `polFull`, `polGap`: the first half of the test, on each parameter file's bytes.
  `restFull`, `restGap`: of the second half all but the layers' words, at each set's free numbers.
  `rowsStored`: the words of all 48 layers, off the written list `scalesF`, are the reference's. It
    serves both sets: they have one scale file and the same two constants in a layer's words.
  `klFull`, `klGap`: the second half at the two sets.

On `decide +kernel`. Five statements here are proved so. The kernel itself evaluates the test and
compares the result with `true`; no compiled code of this library takes part and no axiom is added
(the lines on axioms at the foot of Johnson/Goal/Files/FilesReadProof.lean). So it is within what
the head of Ladder.lean admits as a proof: no decision by compiled code, and no axiom beyond Lean's
three.

Limits. The tests speak of the bytes written in Ladder/Stored.lean. That these are the bytes of the
repository's folder examples/ is not said here. Nothing on a verifier.

-/
import Ladder.FilesReadLaws

set_option autoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifierAndGoals.Read
open OnBytes.Tie.Pv.Plan

/-- The stored scale file is the file of the written words. The named file is unfolded first: left
to find this by itself, Lean compares whole files byte by byte. -/
theorem kl_zFull : storedPublicFiles.KL = wordsFile scalesF := by
  unfold storedPublicFiles
  rfl

/-- The second named set has the stored scale file. -/
theorem kl_zGap : zGap.KL = storedPublicFiles.KL := by
  unfold zGap
  dsimp only

/-- The first half at the stored full-size example's parameter file. -/
theorem polFull : checkPol storedPublicFiles.pol.data.toList storedLines = true := by decide +kernel

/-- The first half at the parameter file with the other policy. -/
theorem polGap : checkPol zGap.pol.data.toList gapLines = true := by decide +kernel

/-- Of the second half all but the layers' words, at the stored free numbers. -/
theorem restFull : restOK storedPublicFiles.KL storedLines = true := by decide +kernel

/-- The same at the free numbers with the other policy. -/
theorem restGap : restOK storedPublicFiles.KL gapLines = true := by decide +kernel

/-- The words of all 48 layers, off the written list. -/
theorem rowsStored : rowsL (List.finRange 48) scalesF 53687 53687 = true := by decide +kernel

/-- The second half at the stored full-size example's files. -/
theorem klFull : CheckKL storedPublicFiles.KL storedLines :=
  ⟨restFull, by rw [kl_zFull, rowsOK_wordsFile]; exact rowsStored⟩

/-- The second half at the files with the other policy. -/
theorem klGap : CheckKL zGap.KL gapLines := by
  rw [kl_zGap]
  exact ⟨restGap, by rw [kl_zFull, rowsOK_wordsFile]; exact rowsStored⟩

end VerifierAndGoals.Read
