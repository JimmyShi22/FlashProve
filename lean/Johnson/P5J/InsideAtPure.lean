-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/InsideAtPure.lean: WHEREVER THE IOP AS WRITTEN IN LEAN IS RETURNED, AN ELEMENT OF AN
ARRAY OF THE LAYOUT LIES INSIDE ITS ORACLE MESSAGE's RANGES AND OFF THE PAD OF ITS OOD SAMPLE. Two
theorems, proved: A JOIN OF TWO FAMILIES OF THEOREMS; nothing new is shown of either.

  `three_at_pure`: where `ProofFile.onlineDescription o pol lay KL` returns: at its public part Z:
    `Z.first.codes.lengthsOk`, `reqShapeOk Z.first.shape` and `reqLayoutOk Z.first.codes
    Z.first.shape Z.first.layout` accept. By
    `ProofFile.Law.descPure_startOk` (Johnson/Desc/ProofFile/Law/PureMade.lean: the four tests of
    `S.startOk` hold there) and `Meaning.three_of_four` (Johnson/Goal/Meaning/LaidInsidePlan.lean).
  `inside_at_pure`: so, there: for every array A of every link l of the layout and every element (i,
    c) that `laidAt` (Johnson/Desc/LaidAt.lean) places at (r, p): the message m that A names is
    there in the request's shape, (r, p) lies inside its main rows' ranges (`InMsg`,
    Johnson/Desc/Sound/World.lean) and at no place of the pad (`padB`, Johnson/Desc/SeatAt.lean). By
    `Meaning.laidAt_inside` (Johnson/Goal/Meaning/LaidInside.lean).
CAN THE PREMISE BE MET? It is "the IOP as written is returned": the premise of every statement in
scope. NO EXAMPLE IN THIS FILE, AND NONE NAMED HERE, SHOWS `ProofFile.onlineDescription`
RETURNING AT THE RELEASE's OWN THREE PUBLIC FILES; in runs outside Lean's kernel its public part and
its first chain were made at a stored small set of public files. That the three tests can hold
together, and that none can be dropped: `Meaning.inside_met` and three negative examples
(Johnson/Goal/Meaning/LaidInsideMember.lean [not in this library]), at a toy request.
Limits. MAIN ROWS ALONE: the layout's arrays lie in main rows; nothing is said of an entry of a mask
row. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.PureMade
import Johnson.Goal.Meaning.LaidInsidePlan
import Johnson.Desc.Sound.World

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc (FileDescription laidAt padB)
open VerifiableInference.Desc.Sound (InMsg)

theorem three_at_pure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ Z.first.codes.lengthsOk = true ∧
      reqShapeOk Z.first.shape = true ∧
      reqLayoutOk Z.first.codes Z.first.shape Z.first.layout = true := by
  obtain ⟨Z, hZ, h4⟩ := ProofFile.Law.descPure_startOk h
  refine ⟨Z, hZ, Meaning.three_of_four
    (n := (VerifiableInference.Desc.First.parP Z.first).samples) ?_⟩
  unfold VerifiableInference.Desc.First.S.startOk at h4
  simpa only [Bool.and_assoc] using h4

/-- **Inside the ranges, off the pad, wherever the IOP as written is returned.** -/
theorem inside_at_pure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      ∀ (l : ℕ) (as : List ReqArray) (A : ReqArray) (i c r p : ℕ),
        Z.first.layout.link[l]? = some as → A ∈ as → laidAt A i c = some (r, p) →
        ∃ m, Meaning.messageAt Z.first.shape l A.message = some m ∧
          InMsg Z.first.codes m.shape false r p ∧ padB Z.first.codes m.shape false r p = false := by
  obtain ⟨Z, hZ, hC, hS, hL⟩ := three_at_pure h
  refine ⟨Z, hZ, fun l as A i c r p hl hA hat => ?_⟩
  obtain ⟨m, e, hr, hp, hB⟩ := Meaning.laidAt_inside hC hS hL hl hA hat
  refine ⟨m, e, ?_, hB⟩
  unfold InMsg
  rw [if_neg (by decide)]
  exact ⟨hr, hp⟩

end P5J

#print axioms P5J.three_at_pure
#print axioms P5J.inside_at_pure
