-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/LaysRoomPub.lean: AT A MADE PUBLIC PART THE TEST msgFits
(Honest/LaidData.lean) SAYS YES AT EVERY MESSAGE OF THE REQUEST's SHAPE, AND THE CODES' LENGTHS ARE
POWERS OF TWO: the test that the filling's "lays" and "ready" ask (laidData, Honest/LaidData.lean),
and the premise codes.lengthsOk of the laws of Honest/Law/LaysRoom.lean: both paid wherever the
public part is made. A statement and its proof. PUBLIC: no coin, no witness, no input.

  msgFits_pub   from ProofFile.pureRoad.pub o pol ly KL = .ok Z: msgFits at Z's codes, shape and layout,
                at every message of every segment; and Codes.lengthsOk

By pub_start (Johnson/IMR/RecRun.lean: the made public part has passed S.startOk), three_of_four
(Johnson/Goal/Meaning/LaidInsidePlan.lean: that conjunction holds the three tests),
reqLayoutFits_eq (Johnson/Desc/Own/ReqAgree.lean), msgFits_of_plan. KIN IN THE LIBRARY:
three_at_pure, inside_at_pure (Johnson/P5J/InsideAtPure.lean): the three tests, and the forward
form, wherever the description is returned.

Limits. That a public part is made at any files is not said here. Of the layout and the shapes
alone. On hiding nothing is said. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.LaysRoom
import Johnson.Goal.Meaning.LaidInsidePlan
import Johnson.IMR.RecRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.Own (reqLayoutFits_eq)

/-- **At a made public part msgFits says yes at every message, and the lengths are powers of
two.** -/
theorem msgFits_pub {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol ly KL = .ok Z) {l m : Nat}
    (hm : m < (Z.first.shape.link.getD l default).messages.length) :
    msgFits Z.first.codes Z.first.shape Z.first.layout l m = true ∧
      Z.first.codes.lengthsOk = true := by
  have hs := Meaning.K2.pub_start h
  unfold VerifiableInference.Desc.First.S.startP at hs
  split at hs
  · rename_i hk
    unfold VerifiableInference.Desc.First.S.startOk at hk
    obtain ⟨hC, hS, hL⟩ := Meaning.three_of_four (n := Z.P.samples)
      (by simpa only [Bool.and_assoc] using hk)
    rw [← reqLayoutFits_eq] at hL
    exact ⟨msgFits_of_plan _ _ _ hS hL hm, hC⟩
  · cases hs

end ProofFile.Honest

#print axioms ProofFile.Honest.msgFits_pub
