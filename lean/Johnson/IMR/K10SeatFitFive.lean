-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/IMR/K10SeatFitFive.lean: NUMBER (7) OF THE CLOSED FACTS ON THE PLAN FOR THE CLOSING KIND
K10's PREMISE hCar, AT LINK 0's FIVE-LIST: "THE SEAT FITS" (SeatFitAt) AT EVERY MEMBER OF loFive
(Johnson/Desc/First/Close/Law/LinkZeroFive.lean: the first written list without the index masks'
message) AT THE SEATS seatFive (FiveAtFull.lean beside it), UNDER THE ONE HEAD P5J.AtMg. It
completes Johnson/IMR/K10SeatFit.lean, which at link 0 stands at the six.

WHAT IT IS NOT, FIRST. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction, with
fixedConfigurationDigest in the digest's place; side library AtFullSide/Top/); so what rests on the head counts as
proved there alone. Link 0 alone. The full size alone. No soundness.

  cover_five        BY THE KERNEL: the cover test says yes at the written entries, loFive and
                    seatsFive
  cover_five_can_fail   A NEGATIVE LINE: loFive against the SIX's seats: no
  **seatFit_five_at_head**   under the head: SeatFitAt (F0T o Zp Np cF) (At.cs Zp) loFive seatFive
                    i, at every i. At every function o in the second hash function's place.
The test coverB and its law seatFit_of_cover are K10SeatFit.lean's.

-/
import Johnson.IMR.K10SeatFit
import Johnson.Desc.First.Close.Law.FiveAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.K10

open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2Caller (SeatFitAt)
open VerifiableInference.Desc.First.Close (seatsOfLink loFive seatsFive seatFive)
open OnBytes.Maker (WholeD)
open P5J

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL.** -/
theorem cover_five : coverB P5T.psFull loFive seatsFive = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line: the five-list against the six's seats. -/
theorem cover_five_can_fail : coverB P5T.psFull loFive (seatsOfLink P5T.psFull 0) = false := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **(7) at link 0's five-list, under the head.** -/
theorem seatFit_five_at_head (h : AtMg o Z D r Zp Np cF) (i : Fin loFive.length) :
    SeatFitAt (F0T o Zp Np cF) (At.cs Zp) loFive seatFive i := by
  have hs : At.pseats Zp = P5T.psFull := h.seats
  exact seatFit_of_cover _ _ _ h.plan.fit loFive seatsFive (by rw [hs]; exact cover_five) i

end IM.K10

#print axioms IM.K10.cover_five
#print axioms IM.K10.cover_five_can_fail
#print axioms IM.K10.seatFit_five_at_head
