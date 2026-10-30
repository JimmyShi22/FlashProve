-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstDoor.lean: THE SHARED TABLE's CONSTANT AT THE IOP AS WRITTEN IN LEAN
THAT THE VERIFIER ITSELF MAKES OF ITS FILES (onlineDescription): the last letter of the parameters at the
seat, G, is laid, and the one Bool that Johnson/Desc/K14/Law/SharedConstAt.lean left in front of the
named tests (chainOkAt) is had from the verifier's own test on what it has made (FileDescription.planOk).

  Sh.chainOk_descPure  onlineDescription … = .ok F → F.planOk = true → there are the public value Z that the
                       road has made of the files and the places N off it, and chainOkAt Z N = true
  Sh.tests_descPure    **so, where Written Z x holds of that Z, all the named tests on the
                       parameters accept at planAt Z N F**
HOW. chainOk_descPure is the first half of the proof of ToldDesc.shared_fits_descPure
(Johnson/ToldDescR/PlacesAtTable.lean), which has this fact inside and does not state it.
WHAT IS NOT HERE. No law. Written Z x. The tests that read open letters, and K12's.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Sh
open ProofFile ToldDesc
open OnBytes OnBytes.Params
open VerifiableInference.Desc (FileDescription blocksOk)
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)

/-- **Where the verifier's own test on what it has made accepts, chainOkAt accepts.** -/
theorem chainOk_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4), pureRoad.pub o pol lay KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧ chainOkAt Z N = true := by
  have hs := ToldDesc.shared_ok_of_planOk F hp
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, hA, -, rfl⟩ := pureZ_make h
  have hA' : laterShared Z = some A := hA
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    unfold laterShared Desc.K14.sharedSeatAt at hA'
    rw [hN] at hA'
    exact nomatch hA'
  | ok N =>
    have hs' : blocksOk A.chain.blocksInOrder = true :=
      (blocksOk_retype (Cl' := ProofFile.Cl) A.chain (shared_links hA')).symm.trans hs
    have hA'' := hA'
    unfold laterShared Desc.K14.sharedSeatAt at hA''
    rw [hN] at hA''
    have e := Option.some.inj hA''
    refine ⟨Z, N, hZ, hN, ?_⟩
    unfold chainOkAt
    rw [← e] at hs'
    exact hs'

/-- **All the named tests on the parameters, at what the verifier itself has made.** -/
theorem tests_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true) {x : LinSized}
    (hx : realSized = some (x, codesFull2)) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4), pureRoad.pub o pol lay KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧ (Written Z x → Tests (planAt Z N F)) := by
  obtain ⟨Z, N, hZ, hN, hc⟩ := chainOk_descPure h hp
  exact ⟨Z, N, hZ, hN, fun hW => tests_at hx hW hN F hc⟩

end Desc.K14.Law.Sh

#print axioms Desc.K14.Law.Sh.chainOk_descPure
#print axioms Desc.K14.Law.Sh.tests_descPure
