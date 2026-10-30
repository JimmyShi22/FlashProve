-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Tables/FlatLengths.lean: HOW MANY SUB-PROTOCOLS THE PROOF FILE's FIRST AND SHARED CHAIN
HAVE, AT THE SEATED DESCRIPTION's OWN TERM (`P5J.F0T o Zp Np cF`, Johnson/P5J/AtTerm.lean):
as many as its table has places. The last chain's length is
`ToldDesc.third_length` (Johnson/ToldDescR/LengthsAtTable.lean) and is not here. These are
the left sides of the fields len₁ and len₂ of `TablesFitR`. The right sides are closed
lists; the left sides hang on Zp, Np and cF: so neither is a fact for Lean's kernel alone. Five
theorems: calls and lengths; no evaluation but of the closed lists' lengths.

  `f0T_is_descN`: the term is `descN` at the same letters: by unfolding.
  `shared_flat_of_pin`: the shared chain has `(sharedPlaces true).length`: in the goals' scope,
    where the description's tests on the plan accept and the pin on the declared rounds accepts: by
    `omega_some_in_scope` and `l1_at_seat` (Johnson/Loose/H2K12/).
  `shared_flat_length`: the same from `LaidAt`, which holds both accepts.
  `first_flat_of_places`: the first chain has `At.ps.length`, where its sub-protocols' places are
    the written list.
  `closed_lengths`: the three right sides: 358, 12, 4: so that the equations say something.

Limits. Nothing on soundness. THAT THE FIRST CHAIN's PLACES ARE THE WRITTEN LIST IS A PREMISE HERE:
PlacesPaid.lean has it: `At.places_paid`, in scope, from `LaidAt` at `OnBytes.secondHashFunction`: called in the
file over this one. That `LaidAt` can be met is shown by no theorem (its
head's tests have been evaluated at the full-size public files).
-/
import Johnson.P5J.LaidOpens
import Johnson.P5J.LettersAt
import Johnson.Loose.H2K12.SharedPlacesAtSeat
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Desc.Last.BordersLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Tables
open VerifiableInference.Desc.First (blockPlaces)
open VerifiableInference.Desc.Shared (placesFitS sharedPlaces)
open VerifiableInference.Desc.Last (lastPlaces)
open VerifiableInference.Desc.K12 (guardedProximityTestParts)
open OnBytes.Maker (WholeD)
open P5J (F0T LaidAt TS)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

/-- The seated description's own term is `descN` at the same letters. -/
theorem f0T_is_descN :
    F0T o Zp Np cF = H2K.JointK.descN o ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF := rfl

variable {o Zp Np cF}

/-- **The shared chain has as many sub-protocols as its table has places, at split := true.** -/
theorem shared_flat_of_pin {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    (hp : (F0T o Zp Np cF).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol (F0T o Zp Np cF) = true) :
    (F0T o Zp Np cF).shared.blocksInOrder.length = (sharedPlaces true).length := by
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope hS Zp ProofFile.pureRoad.links Np cF hp hpin
  have h := H2K.JointK.l1_at_seat o ProofFile.pureRoad.links Zp Np cF hp nO hO
  unfold placesFitS at h
  rw [beq_iff_eq] at h
  have e := congrArg List.length h
  rw [List.length_map] at e
  exact e

/-- The same from `LaidAt`. -/
theorem shared_flat_length {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    (hZ : VerifierAndGoals.InScope Z = true) (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    (F0T o Zp Np cF).shared.blocksInOrder.length = (sharedPlaces true).length :=
  shared_flat_of_pin hZ L.planOk (LPFD.asks_written L.asks)

/-- **The first chain has as many sub-protocols as its table has places**, where their places are
the written list. -/
theorem first_flat_of_places (h : blockPlaces cF.blocksInOrder = P5J.At.ps) :
    (F0T o Zp Np cF).first.blocksInOrder.length = P5J.At.ps.length := by
  have e := congrArg List.length h
  unfold blockPlaces at e
  rw [List.length_map] at e
  exact e

/-- The three right sides, counted. -/
theorem closed_lengths :
    (P5J.At.ps.length, (sharedPlaces true).length, lastPlaces.length) = (358, 12, 4) := by
  decide +kernel

end OnBytes.Road.Tables

#print axioms OnBytes.Road.Tables.f0T_is_descN
#print axioms OnBytes.Road.Tables.shared_flat_of_pin
#print axioms OnBytes.Road.Tables.shared_flat_length
#print axioms OnBytes.Road.Tables.first_flat_of_places
#print axioms OnBytes.Road.Tables.closed_lengths
