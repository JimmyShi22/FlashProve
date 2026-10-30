-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/PublicOfFileOkD.lean: AT THE KEY FILE's DESCRIPTION `Key.descriptionFromSource X N P`: WHAT THE FILE's OWN TESTS ON THE PLAN HAND A PAYER: PublicOfFileOk.lean [not in this library] carried. A trial file.
Main names. `fileOk_of_planOk'`: general in the description, by a proof that does not count `planOkCore`'s conjuncts · `clause_of_fileOkD` · `admitted_of_fileOkD` («ranges») · `stages_of_planOkD`: **`(Key.descriptionFromSource X N P).planOk = true → X.Y.k.oneTime.ranges.stages.length ≤ 34`** · `cut_of_planOkD`: «cut»: the shape and the ranges' parameters that are read back out of the parameter bytes are the planner's sized ones.
OBJECT: `Key.descriptionFromSource`'s field fileOk; `Key.fileClauses`; `Key.sourceClauses` · USER: none · LETTERS: X N P.
Nothing on soundness.

-/
import Johnson.Top.Fire.Code.StagesFew
import Johnson.Desc.Key.Desc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open VerifiableInference.Desc
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource fileClauses sourceClauses)

/-- **The tests on the plan hold the file's own.** -/
theorem fileOk_of_planOk' {XI : Type} (F : FileDescription XI) (h : F.planOk = true) : F.fileOk = true := by
  cases hf : F.fileOk with
  | true => rfl
  | false =>
    unfold FileDescription.planOk FileDescription.planOkCore at h
    simp [hf] at h

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

theorem clause_of_fileOkD (h : (descriptionFromSource X N P).fileOk = true) (c : String × Bool) (hc : c ∈ sourceClauses X.Y) : c.2 = true := by
  have h' : ((fileClauses X N P _ _ _).all (·.2) && _) = true := h
  rw [Bool.and_eq_true] at h'
  exact List.all_eq_true.1 h'.1 c (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc)))

theorem admitted_of_fileOkD (h : (descriptionFromSource X N P).fileOk = true) :
    OnBytes.Wf.admitted X.Y.k.oneTime.codes X.Y.k.oneTime.ranges (OnBytes.Wf.matrixOf X.Y.k.oneTime.lin) = true :=
  clause_of_fileOkD X N P h ("ranges", OnBytes.Wf.admitted X.Y.k.oneTime.codes X.Y.k.oneTime.ranges (OnBytes.Wf.matrixOf X.Y.k.oneTime.lin))
    (by simp [sourceClauses])

/-- **At most 34 stages, from what the fence hands.** -/
theorem stages_of_planOkD (h : (descriptionFromSource X N P).planOk = true) : X.Y.k.oneTime.ranges.stages.length ≤ 34 :=
  stages_le_of_admitted _ _ _ (admitted_of_fileOkD X N P (fileOk_of_planOk' _ h))

/-- **The clause «cut», from what the fence hands.** -/
theorem cut_of_planOkD (h : (descriptionFromSource X N P).planOk = true) : X.Y.k.oneTime.lin = X.Y.cutShape ∧ X.Y.k.oneTime.ranges = X.Y.cutRanges := by
  have hc := clause_of_fileOkD X N P (fileOk_of_planOk' _ h)
    ("cut", X.Y.cutShape == X.Y.k.oneTime.lin && X.Y.cutCodes.1 == X.Y.k.oneTime.codes && X.Y.cutCodes.2.1 == X.Y.k.oneTime.codes && X.Y.cutCodes.2.2 == X.Y.k.oneTime.codes &&
      X.Y.cutIdx == X.Y.k.oneTime.indexMasks && X.Y.cutRanges == X.Y.k.oneTime.ranges && X.Y.cutSamples == X.Y.k.oneTime.given.plan.samples)
    (by simp [sourceClauses])
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, _⟩, _⟩, _⟩, _⟩, h6⟩, _⟩ := hc
  exact ⟨(eq_of_beq h1).symm, (eq_of_beq h6).symm⟩

end LPFD

#print axioms LPFD.fileOk_of_planOk'
#print axioms LPFD.stages_of_planOkD
#print axioms LPFD.cut_of_planOkD
