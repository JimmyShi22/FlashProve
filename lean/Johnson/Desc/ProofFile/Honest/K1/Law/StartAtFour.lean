-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/StartAtFour.lean: THE SHARED "SENDING" (the kind K1): WHERE,
AMONG THE OPENING's SENDER's COINS OF E, THE MASK ROWS OF ITS MESSAGE NUMBER 4 BEGIN: THE NUMBER:
8647; AND WHICH RIDE A JOB MADE BY placeJob HAS. PUBLIC DATA ALONE: a plan, a ride, a number: where
a run of coins begins, never what stands in it. Five theorems; no definition.

  - k1StartW: maskStart (Honest/K1/MaskLaw.lean) at the opening's written plan K1.parGF and the ride
    rideOf (firstFold K1.qFull), at message number 4, is 8647. By evaluation in Lean's kernel.
  - k1StartW_alone: A NEGATIVE TEST AND MORE: of the opening's messages number 4 ALONE has the start
    8647.
  - k1Start_head: UNDER h (the library's head: A HYPOTHESIS), O: the same number at the plan and the
    ride of the description's own ground.
  - placeJob_ride: the ride of a job that placeJob makes is rideOf at the letter "fold" that it was
    handed: by its text.
  - ride_of_job: so where a job J is such a job, J.ride is that.

For whom. A law of another kind's on the book of coins wants the number alone, and an equation on
J.ride: the record of premises K1Seated (Honest/K1/Seated.lean) is general in J, and NO FIELD OF IT
FIXES THE RIDE: two name it (fits: the public test at J.P and J.ride; hasCoins: the count dueR J.P
J.ride); neither is an equation on it. At the opening's real job (the first member of lotHalves,
Honest/K1/PlaceJob.lean; hJ in RecordAtWider.lean and RecordPaid.lean) fold is firstFold at the
ground's first parameters.

Kin. idxOwnerW (OwnerAtWritten.lean): the maker's own start for that message is this maskStart.

Limits. THE FULL SIZE ALONE. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- **THE NUMBER.** -/
theorem k1StartW : maskStart parGF (rideOf (firstFold K1.qFull)) 4 = 8647 := by
  decide +kernel

/-- Of the opening's messages number 4 alone has that start. -/
theorem k1StartW_alone : ((List.range parGF.sent.size).filter fun n =>
    maskStart parGF (rideOf (firstFold K1.qFull)) n == 8647) = [4] := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **THE SAME NUMBER AT THE PLAN AND THE RIDE OF THE DESCRIPTION's OWN GROUND**, under the head. -/
theorem k1Start_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    maskStart (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) 4 = 8647 := by
  rw [K1.eG_atAll h O (K1.pin1_atAll h),
    firstFold_shape (q' := K1.qFull) ((K1.hs_atAll h O (K1.pin1_atAll h)).trans ?_)]
  · exact k1StartW
  · rfl

/-- The ride of a job that placeJob makes: by its text. -/
theorem placeJob_ride {Xi X : Type} (P : K1.Par) (first : Nat)
    (fold : Option (Nat × FoldShape)) (Dt : RowDataOf Xi) (part : Nat) :
    (placeJob (X := X) P first fold Dt part).ride = rideOf fold := rfl

/-- Where a job is one that placeJob makes, its ride is rideOf at that fold. -/
theorem ride_of_job {Xi X : Type} {J : SendJob (PlaceIn Xi) X} {P : K1.Par} {first : Nat}
    {fold : Option (Nat × FoldShape)} {Dt : RowDataOf Xi} {part : Nat}
    (hJ : J = placeJob P first fold Dt part) : J.ride = rideOf fold := by
  rw [hJ]
  rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1StartW
#print axioms ProofFile.Honest.K1.k1StartW_alone
#print axioms ProofFile.Honest.K1.k1Start_head
#print axioms ProofFile.Honest.K1.placeJob_ride
#print axioms ProofFile.Honest.K1.ride_of_job
