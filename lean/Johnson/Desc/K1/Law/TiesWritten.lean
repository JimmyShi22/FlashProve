-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TiesWritten.lean: the tests with code that the law on the sub-protocol K1 asks
of the table's numbers and of the list of seats at its TWO OTHER PLACES, the first segment's opening
(number 2 of the first chain's sub-protocols) and W's commitment (number 356), AT THE WRITTEN VALUES
OF THE FULL SIZE: closed facts, each with a negative test. Definitions and statements with their
proofs. The fifty later places: TestsWritten.lean (this folder).

THE ARGUMENTS, EACH WITH ITS WRITTEN TERM:
  the places' parameters · `parGF` := `firstPar qFull gpFull` · `parWF` := `parW qFull gpFull 4
    wMsgFull` (Johnson/Desc/K1/Law/QFull.lean, Johnson/HB/LLHARD/PlanAtQFull.lean)
  the numbers' core · `P5T.N0Full` · the seats · `K13.Law.seatsFull` · the seats with an
    out-of-domain (OOD) sample · `smpdFull`, off `P5T.psFull` · the two counts at the borders ·
    `K13.Law.countsFull` · the request's shape · `shapeFull`

  `counts_four`: the two counts at the borders 2, 3, 356, 357: (0, 0), (5, 2), (197, 82), (199, 83).
  `sizes_two`: the opening lays 2 trees and sends 5 oracle messages, W's commitment 1 and 2; each
    place has one seed. `sizes_reject`.
  `seatsG_written`, `seatsW_written`: from the count of oracle messages in front on, the list of
    seats goes on with the place's seats. `seatsTwo_reject`: one message further on it does not.
  `ownSeats_written`: `ownSeatsB` at the opening. `ownSeats_rejects`: behind one tree.
  `planSeat_written`: W's seat is the seat that the place makes. `planSeat_rejects`.
  `planSits_written`: the three clauses of `planSitsB` at the written linear shape.
    `planSits_rejects`: at an empty table of codes.
  `find0_written`: the first place of segment 0 at piece 1 is the place number 2. `find0_rejects`.
  `samB`, `samG_written`, `samW_written`: a message of the place at whose seat a seat with an OOD
    sample stands has an OOD sample itself. `sam_bites`: each place has a message without one (the
    mask's), and with that message's seat among the seats the test rejects.
By evaluations in Lean's kernel (`decide +kernel`): all. The recursion limit is raised for the
elaboration of these evaluations alone (maxRecDepth 1000000).

What is not claimed. That a verifier computes these values. Closed facts on written values. Nothing
on soundness.

-/
import Johnson.Desc.K1.Law.TestsWritten
import Johnson.Desc.K1.Law.HeldAtOpening
import Johnson.Desc.K1.Law.Joined
import Johnson.Desc.K13.Law.AtTableW
import Johnson.Desc.K13.Law.SitsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (Numbers flatPlacesOf shift)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt countsFull seatsFull gpFull wMsgFull)
open VerifiableInference.Desc.ReqLit (shapeFull)
open P5T (N0Full psFull)

/-- The first segment's opening's parameters, at the written values. -/
def parGF : Par := firstPar qFull gpFull

/-- The parameters of W's commitment, at the written values. -/
def parWF : Par := parW qFull gpFull 4 wMsgFull

/-- The seats with an OOD sample, off the written seats. -/
def smpdFull : List (ℕ × ℕ) := (psFull.filter (·.smpd)).map (·.seat)

theorem counts_four : countsFull[2]? = some (0, 0) ∧ countsFull[2 + 1]? = some (5, 2) ∧
    countsFull[356]? = some (197, 82) ∧ countsFull[356 + 1]? = some (199, 83) := by
  decide +kernel

theorem sizes_two : (layOf parGF).shapes.size = 2 ∧ parGF.sent.size = 5 ∧ parGF.seeds = 1 ∧
    (layOf parWF).shapes.size = 1 ∧ parWF.sent.size = 2 ∧ parWF.seeds = 1 := by
  decide +kernel

/-- The negative test: the two places' sizes are not one another's. -/
theorem sizes_reject : (layOf parGF).shapes.size ≠ 1 ∧ parWF.sent.size ≠ 5 := by
  decide +kernel

theorem seatsG_written : ((List.range (shapesOf parGF).length).all fun j =>
    decide (seatsFull[0 + j]? = some (seatOfMsg parGF 0 j))) = true := by
  decide +kernel

theorem seatsW_written : ((List.range (shapesOf parWF).length).all fun j =>
    decide (seatsFull[197 + j]? = some (seatOfMsg parWF 82 j))) = true := by
  decide +kernel

/-- The negative test: one message further on. -/
theorem seatsTwo_reject : decide (seatsFull[1 + 0]? = some (seatOfMsg parGF 0 0)) = false ∧
    decide (seatsFull[198 + 0]? = some (seatOfMsg parWF 82 0)) = false := by
  decide +kernel

theorem ownSeats_written : ownSeatsB N0Full (openAt linksFull (flatPlacesOf linksFull true) (2 + 1))
    parGF (((shapeFull.link[0]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length
    0 = true := by
  decide +kernel

/-- The negative test: behind one tree. -/
theorem ownSeats_rejects : ownSeatsB N0Full
    (openAt linksFull (flatPlacesOf linksFull true) (2 + 1)) parGF
    (((shapeFull.link[0]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length
    1 = false := by
  decide +kernel

theorem planSeat_written :
    (N0Full.w == (82 + (layOf parWF).tree.getD 0 0, (layOf parWF).part.getD 0 0)) = true := by
  decide +kernel

/-- The negative test: behind one tree fewer. -/
theorem planSeat_rejects :
    (N0Full.w == (81 + (layOf parWF).tree.getD 0 0, (layOf parWF).part.getD 0 0)) = false := by
  decide +kernel

theorem planSits_written :
    (decide ((parWF.sent[0]?).map (·.shape) = some qFull.lin.w) && parWF.codes.lengthsOk &&
      decide (qFull.lin.w.code < parWF.codes.base.size)) = true := by
  decide +kernel

/-- The negative test: at an empty table of codes the third clause fails. -/
theorem planSits_rejects : decide (qFull.lin.w.code < ({} : Codes).base.size) = false := by
  decide +kernel

theorem find0_written : ((flatPlacesOf linksFull true).find? fun p =>
    p.link == some 0 && p.piece == 1 + ((linksFull[0]?).map shift).getD 0) =
      (flatPlacesOf linksFull true)[2]? := by
  decide +kernel

/-- The negative test: the place one further on is another. -/
theorem find0_rejects : ((flatPlacesOf linksFull true).find? fun p =>
    p.link == some 0 && p.piece == 1 + ((linksFull[0]?).map shift).getD 0) ≠
      (flatPlacesOf linksFull true)[3]? := by
  decide +kernel

/-- A test: a message of the place at whose seat, behind nT trees, one of the seats ss stands has an
OOD sample. -/
def samB (P : Par) (nT : ℕ) (ss : List (ℕ × ℕ)) : Bool :=
  (List.finRange (shapesOf P).length).all fun j =>
    !ss.contains (seatOfMsg P nT j.val) || decide (sampledAt P j)

theorem samG_written : samB parGF 0 smpdFull = true := by decide +kernel

theorem samW_written : samB parWF 82 smpdFull = true := by decide +kernel

/-- **The test bites**: with the mask's message's seat among the seats it rejects, at both
places. -/
theorem sam_bites : samB parGF 0 ((0, 3) :: smpdFull) = false ∧
    samB parWF 82 ((82, 1) :: smpdFull) = false := by
  decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.counts_four
#print axioms VerifiableInference.Desc.K1.sizes_two
#print axioms VerifiableInference.Desc.K1.sizes_reject
#print axioms VerifiableInference.Desc.K1.seatsG_written
#print axioms VerifiableInference.Desc.K1.seatsW_written
#print axioms VerifiableInference.Desc.K1.seatsTwo_reject
#print axioms VerifiableInference.Desc.K1.ownSeats_written
#print axioms VerifiableInference.Desc.K1.ownSeats_rejects
#print axioms VerifiableInference.Desc.K1.planSeat_written
#print axioms VerifiableInference.Desc.K1.planSeat_rejects
#print axioms VerifiableInference.Desc.K1.planSits_written
#print axioms VerifiableInference.Desc.K1.planSits_rejects
#print axioms VerifiableInference.Desc.K1.find0_written
#print axioms VerifiableInference.Desc.K1.find0_rejects
#print axioms VerifiableInference.Desc.K1.samG_written
#print axioms VerifiableInference.Desc.K1.samW_written
#print axioms VerifiableInference.Desc.K1.sam_bites
