-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RideAtPlans.lean: THE SHARED "SENDING" (the kind K1): WHICH
MESSAGES OF K1's PLANS HAVE A RIDING TABLE, AND AT WHICH NUMBERS (k, h): AT THE WRITTEN PLANS, AND
UNDER THE LIBRARY's HEAD. PUBLIC. Eight theorems; no definition.

  - rides_first_written: at the opening's written plan (K1.parGF, five messages), at the ride that
    the description's own terms make (rideOf (firstFold K1.qFull)): message 3 alone rides, at (k, h)
    = (8, 0): ONE ROW.
  - rides_w_written: at W's sending's written plan (K1.parWF, two messages), at rideOf (wFold
    K1.qFull.lin): message 1 alone rides, at (k, h) = (5, 1): TWO ROWS.
  - oneRow_first_written, oneRow_w_written_no: THE TEST "every riding table has h = 0" SAYS YES AT
    THE FIRST AND NO AT THE SECOND: each is the other's control.
  - ride_later: a job with no fold (laterJobAt, Honest/K1/PlaceJob.lean: the fifty) has no riding
    table.
  - ride_two_head, ride_w_head: UNDER THE HEAD (h, and the opening O out of h.laid.opened): the
    two rides at the head's own letters are the written ones.
  - w_not_one_row_head: under the head: the rider of W's sending has h ≠ 0.

The first four are evaluations in Lean's kernel (decide +kernel; no compiled code).

WHAT FOLLOWS. ride_sizes, ride_one, ride_one_beyond, held_ride_one (Honest/K1/RideOne.lean) and
no_other_ride (Honest/K1/NoOther.lean) stand under h0 : R.h = 0, and lay_one, lay_one_beyond and sig
(Honest/K1/RideLaw.lean) at a ride ⟨k, 0⟩: THEY SPEAK AT NUMBER 2's RIDER AND SAY NOTHING AT W's.
ride_coin (RideLaw.lean) is general in h.

Limits. THE FULL SIZE ALONE; the format's second hash function alone. It says where a table rides and at
which numbers: nothing on what is laid there. It stands over files of ours that are on no seal.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

/-- **THE OPENING's WRITTEN PLAN: MESSAGE 3 ALONE RIDES, AT (8, 0).** -/
theorem rides_first_written : (List.range K1.parGF.sent.size).map (rideOf (firstFold K1.qFull)) =
    [none, none, none, some ⟨8, 0⟩, none] := by
  decide +kernel

/-- **W's SENDING's WRITTEN PLAN: MESSAGE 1 ALONE RIDES, AT (5, 1).** -/
theorem rides_w_written : (List.range K1.parWF.sent.size).map (rideOf (wFold K1.qFull.lin)) =
    [none, some ⟨5, 1⟩] := by
  decide +kernel

/-- "Every riding table has one row": yes at the opening's plan. -/
theorem oneRow_first_written : ((List.range K1.parGF.sent.size).all fun k =>
    (rideOf (firstFold K1.qFull) k).all fun R => R.h == 0) = true := by
  decide +kernel

/-- "Every riding table has one row": NO at W's sending's plan. -/
theorem oneRow_w_written_no : ((List.range K1.parWF.sent.size).all fun k =>
    (rideOf (wFold K1.qFull.lin) k).all fun R => R.h == 0) = false := by
  decide +kernel

/-- Where no fold is handed in, no table rides. -/
theorem ride_later (k : Nat) : rideOf none k = none := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- **NUMBER 2's RIDE**, under the head, is the written one. -/
theorem ride_two_head : rideOf (firstFold Bs.G₀.first) = rideOf (firstFold K1.qFull) := by
  rw [firstFold_shape (q' := K1.qFull) ((K1.hs_atAll h O (K1.pin1_atAll h)).trans ?_)]
  rfl

/-- **NUMBER 356's RIDE**, under the head, is the written one. -/
theorem ride_w_head : rideOf (wFold Zp.first.lin) = rideOf (wFold K1.qFull.lin) := by
  rw [(K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).lin]
  rfl

/-- **UNDER THE HEAD W's RIDER HAS TWO ROWS**: message 1 rides at (5, 1): h is not 0. -/
theorem w_not_one_row_head :
    rideOf (wFold Zp.first.lin) 1 = some ⟨5, 1⟩ ∧
      ∀ R, rideOf (wFold Zp.first.lin) 1 = some R → R.h ≠ 0 := by
  have e : rideOf (wFold Zp.first.lin) 1 = some ⟨5, 1⟩ := by
    rw [ride_w_head h O]
    decide +kernel
  refine ⟨e, fun R hR => ?_⟩
  rw [e] at hR
  cases hR
  decide

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.rides_first_written
#print axioms ProofFile.Honest.K1.rides_w_written
#print axioms ProofFile.Honest.K1.oneRow_first_written
#print axioms ProofFile.Honest.K1.oneRow_w_written_no
#print axioms ProofFile.Honest.K1.ride_later
#print axioms ProofFile.Honest.K1.ride_two_head
#print axioms ProofFile.Honest.K1.ride_w_head
#print axioms ProofFile.Honest.K1.w_not_one_row_head
