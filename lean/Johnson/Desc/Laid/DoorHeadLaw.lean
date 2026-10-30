-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Laid/DoorHeadLaw.lean: WHAT A YES OF A ROW OVER THE SHARED PLAN GIVES. A law file.

  planOf_some   the shared plan is the value that the maker of the IOP as written returns
  every_yes     a yes of `every`: a plan is made, and the test accepts it
  atFull_yes    a yes of `atFull`: a plan is made, and at the full size's key the test accepts it
  atFull_no     a no of `atFull`: no plan is made, or the key is the full size's and the test
                rejects

Nothing on soundness.

-/
import Johnson.Desc.Laid.DoorHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Door

/-- **The shared plan is the maker's own value.** -/
theorem planOf_some {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub} :
    planOf o pol lay KL = some Z ↔ ProofFile.pureRoad.pub o pol lay KL = .ok Z := by
  unfold planOf
  cases h : ProofFile.pureRoad.pub o pol lay KL with
  | error e => simp [Except.toOption]
  | ok W => simp [Except.toOption]

/-- **A yes of a row that is asked at every size.** -/
theorem every_yes {M : Option ProofFile.Pub} {t : ProofFile.Pub → Bool} (h : every M t = true) :
    ∃ Z, M = some Z ∧ t Z = true := by
  cases M with
  | none => simp [every] at h
  | some Z => exact ⟨Z, rfl, by simpa [every] using h⟩

/-- **A yes of a row of the full size alone.** -/
theorem atFull_yes {M : Option ProofFile.Pub} {t : ProofFile.Pub → Bool} (h : atFull M t = true) :
    ∃ Z, M = some Z ∧ (atFullKey Z = true → t Z = true) := by
  cases M with
  | none => simp [atFull] at h
  | some Z =>
    refine ⟨Z, rfl, fun hk => ?_⟩
    simpa [atFull, hk] using h

/-- **What a no rejects.** -/
theorem atFull_no {M : Option ProofFile.Pub} {t : ProofFile.Pub → Bool} (h : atFull M t = false) :
    M = none ∨ ∃ Z, M = some Z ∧ atFullKey Z = true ∧ t Z = false := by
  cases M with
  | none => exact .inl rfl
  | some Z =>
    refine .inr ⟨Z, rfl, ?_⟩
    simpa [atFull] using h

end VerifiableInference.Desc.Door

#print axioms VerifiableInference.Desc.Door.planOf_some
#print axioms VerifiableInference.Desc.Door.every_yes
#print axioms VerifiableInference.Desc.Door.atFull_yes
#print axioms VerifiableInference.Desc.Door.atFull_no
