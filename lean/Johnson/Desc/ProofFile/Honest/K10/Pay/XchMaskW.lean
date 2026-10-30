-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchMaskW.lean: the closing of a segment (K10): closed tests, by Lean's kernel, at the written
plan, for Pay/XchMaskAt.lean; in a file of their own because they take minutes.

  `maskTest`, `mask_seat_written`   at links 1 to 24, at the plan's number of the segment's fresh mask: the written list of the first
                    chain's messages has there the shape of the code switch's last message; the written plan's list of places
                    has there (q.j, q.t + d), d = 0, q the seat of "link l, moment 0" at the last message's place
  `mask_seat_bent`    THE TEST CAN FAIL: at d = 1 it rejects at every link

Limits. Written values alone, at the full size.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSeatsAt
import Johnson.Desc.ProofFile.Honest.K10.Pay.FoldAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (maskNo seatsPlanW)
open VerifiableInference.Desc.First.K2Hands (MList)
open VerifiableInference.Desc.K13.Law (LFull)
open ProofFile.Honest.K2 (switchSent switchSeatIn)
open ProofFile.Honest.K2.Law (placesW)

/-- The test at link l. d: a number added to the tenant that is asked for: 0 in the test. -/
def maskTest (d l : Nat) : Bool :=
  match placesW.find? (·.link == l) with
  | some p =>
    match switchSeatIn P5T.seatsAllFull l ((switchSent p.sizes p.others).size - 1) with
    | some q =>
      decide (MList[maskNo seatsPlanW P5T.psFull l]? =
        some ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape) &&
      decide (LFull.places[maskNo seatsPlanW P5T.psFull l]? = some (q.j, q.t + d))
    | none => false
  | none => false

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem mask_seat_written : ((List.range 24).all fun i => maskTest 0 (i + 1)) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem mask_seat_bent : ((List.range 24).any fun i => maskTest 1 (i + 1)) = false := by decide +kernel

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.mask_seat_written
#print axioms ProofFile.Honest.K10.mask_seat_bent
