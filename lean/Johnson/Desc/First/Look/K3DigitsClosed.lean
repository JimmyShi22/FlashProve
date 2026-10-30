-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3DigitsClosed.lean (at the kind's ledger's own letters: the
place behind is MgAt.nextOf l true): the lookup on the digits of a segment's approximate range
proof: TWO OF THE TESTS OF DigOwedR (Johnson/Desc/Sound/MgAt/K3Owed.lean: what is
owed at one digits' place) AS CLOSED FACTS ON THE FULL SIZE's WRITTEN LISTS, at all twenty-five
segments. One evaluation by the kernel, one negative test, one lemma. NO SOUNDNESS IS CLAIMED.

Main names.
  digClosedB l: the place behind (MgAt.nextOf l true, Johnson/Desc/Sound/MgAt/K3Pins.lean) stands in
    the same segment's stand as the digits' place (sameStand) · the segment's three pins are open in
    front (digitsOpenB, K3DigitsMean.lean). digClosed_full: TRUE AT ALL 25, by the kernel.
  digClosed_control: A NEGATIVE TEST, foretold by reading, untried
    (Where this and lean/THEOREM.md differ,
    the page holds.): read at the CALLS' border of
    segment 0 the test says false (the pins of the moments 2 and 1 are not open there).
  digClosed_at: so the fields hfitS, hOp at (IM.k3Place l true, MgAt.nextOf l true, k3K l true): NO
    PREMISE BUT l < 25.
OBJECT. Functions with code of the table of joints at the full size's written lists.
USER. Johnson/Desc/Sound/MgAt/K3DigitsOwed.lean calls digClosed_at.
LETTERS. l.
IS IT EMPTY? No premise.



Compiled with the whole library.
Limits. The full size's lists alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsMean
import Johnson.Desc.First.Look.K3Base
import Johnson.Desc.Sound.MgAt.K3Pins
import Johnson.Desc.First.ShapeRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (sameStand)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- Two tests on the full size's written lists, at segment l. -/
def digClosedB (l : ℕ) : Bool :=
  sameStand linksFull (IM.k3Place l true) (MgAt.nextOf l true) &&
    digitsOpenB linksFull PS (k3K l true) l

set_option maxRecDepth 100000 in
theorem digClosed_full : (List.range 25).all digClosedB = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **A negative test.** -/
theorem digClosed_control : digitsOpenB linksFull PS (k3K 0 false) 0 = false := by decide +kernel

/-- **hfitS, hOp.** -/
theorem digClosed_at (l : ℕ) (hl : l < 25) :
    sameStand linksFull (IM.k3Place l true) (MgAt.nextOf l true) = true ∧
      digitsOpenB linksFull PS (k3K l true) l = true := by
  have h := List.all_eq_true.1 digClosed_full l (List.mem_range.2 hl)
  unfold digClosedB at h
  exact Eq.mp (Bool.and_eq_true _ _) h

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digClosed_full
#print axioms VerifiableInference.OnPublicFiles.digClosed_control
#print axioms VerifiableInference.OnPublicFiles.digClosed_at
