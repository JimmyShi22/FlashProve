-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FitsWritten.lean: THE SHARED "SENDING" (the kind K1): TWO
PUBLIC TESTS OF THE RECORD OF PREMISES K1Seated (Honest/K1/Seated.lean), fits AND oneAns, HOLD AT
THE PLANS OF THE OPENING AND OF THE FIFTY LATER SENDINGS, AT THE DESCRIPTION's OWN GROUND, UNDER THE
LIBRARY's HEAD. Ten theorems; no definition.

What the two tests say. sendFits P ride (Honest/K1/Coins.lean): the codes' lengths, the messages'
shapes, the sampled messages' pads and the riding tables fit. answersAtMostOne P
(Honest/K1/ScriptAt.lean): AT MOST one answer at each message of the plan.

The road. Both are Bools on public numbers. They are evaluated IN THE KERNEL at the library's
written plans, and the library's own ties say that under its head the plans at the description's
ground are the written ones.

  - oneAns_first_written, oneAns_later_written, fits_first_written, fits_later_written: four closed
    sentences, by evaluation in the kernel: at K1.parGF (Johnson/Desc/K1/Law/TiesWritten.lean) with
    the ride rideOf (firstFold K1.qFull), and at K1.placeL l d
    (Johnson/Desc/AtSeats/MemsAtPlan.lean), l < 25, both d, with no ride.
  - firstFold_shape: firstFold (Honest/K1/PlaceJob.lean) reads the request's shape alone.
  - parL_written: UNDER h, O: K1.parL Zp Bs.G₀ l d = K1.placeL l d (parL_place,
    Johnson/Desc/AtSeats/FromTheCut.lean).
  - oneAns_two_head, fits_two_head: UNDER h (the library's head: A HYPOTHESIS) and O (the
    description opened: out of h.laid.opened): the two tests at K1.firstPar Bs.G₀.first (K1.gpOf
    Zp), fits at the ride rideOf (firstFold Bs.G₀.first) (eG_atAll,
    Johnson/Desc/K1/Law/TiesAtAll.lean).
  - oneAns_fifty_head, fits_fifty_head: UNDER h, O, hl : l < 25: at K1.parL Zp Bs.G₀ l d, fits at no
    ride.

Kin. The library evaluates its own tests at these plans so: own_first, own_fifty
(Johnson/Desc/K1/Law/PlanOwn.lean), radii_written (Johnson/Desc/K1/Law/TiesAtAll2.lean). Ours:
firstRide_eq (Honest/K1/PlaceJob.lean); written_sendFits (Honest/K1/FirstSentWritten.lean), at a
small plan. A law is said to give sendFits at all jobs of the kind from the description's own
test on the plan, without evaluation: not checked here; not called here.

Limits. 51 PLANS: W's sending is not here. THE FULL SIZE ALONE: the written plans stand at K1.qFull.
"AT MOST one answer", at these plans, under the head: no more is said. That a prover's job has these
plans and rides is not said here. Nothing on soundness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.Desc.AtSeats.FromTheCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

/-- At most one answer at each message of the opening's written plan. -/
theorem oneAns_first_written : answersAtMostOne K1.parGF = true := by decide +kernel

/-- The like at the fifty later sendings' written plans. -/
theorem oneAns_later_written : ((List.range 25).all fun l =>
    answersAtMostOne (K1.placeL l false) && answersAtMostOne (K1.placeL l true)) = true := by
  decide +kernel

/-- The opening's written plan fits, with the ride that the description's own terms make. -/
theorem fits_first_written : sendFits K1.parGF (rideOf (firstFold K1.qFull)) = true := by
  decide +kernel

/-- The fifty later sendings' written plans fit; no table rides. -/
theorem fits_later_written : ((List.range 25).all fun l =>
    sendFits (K1.placeL l false) (rideOf none) && sendFits (K1.placeL l true) (rideOf none)) =
      true := by
  decide +kernel

/-- firstFold reads the request's shape alone. -/
theorem firstFold_shape {q q' : OnBytes.Params.First} (hs : q.shape = q'.shape) :
    firstFold q = firstFold q' := by
  unfold firstFold K1.frame₀
  rw [hs]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- **oneAns AT NUMBER 2's PLAN**, under the head. -/
theorem oneAns_two_head : answersAtMostOne (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) = true := by
  rw [K1.eG_atAll h O (K1.pin1_atAll h)]
  exact oneAns_first_written

/-- **fits AT NUMBER 2's PLAN AND RIDE**, under the head. -/
theorem fits_two_head :
    sendFits (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) = true := by
  rw [K1.eG_atAll h O (K1.pin1_atAll h),
    firstFold_shape (q' := K1.qFull) ((K1.hs_atAll h O (K1.pin1_atAll h)).trans ?_)]
  · exact fits_first_written
  · rfl

/-- Under the head the plan of the fifty is the written one. -/
theorem parL_written (l : ℕ) (d : Bool) : K1.parL Zp Bs.G₀ l d = K1.placeL l d :=
  K1.parL_place (K1.hc_atAll h O (K1.pin1_atAll h)) (K1.hs_atAll h O (K1.pin1_atAll h))
    (K13.Law.gpOf_in_scope h.scope h.laid.pub (K1.pin1_atAll h)) l d

/-- **oneAns AT THE FIFTY's PLANS**, under the head. -/
theorem oneAns_fifty_head {l : ℕ} (hl : l < 25) (d : Bool) :
    answersAtMostOne (K1.parL Zp Bs.G₀ l d) = true := by
  rw [parL_written h O l d]
  have e := List.all_eq_true.1 oneAns_later_written l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at e
  cases d with
  | true => exact e.2
  | false => exact e.1

/-- **fits AT THE FIFTY's PLANS**, under the head; no table rides. -/
theorem fits_fifty_head {l : ℕ} (hl : l < 25) (d : Bool) :
    sendFits (K1.parL Zp Bs.G₀ l d) (rideOf none) = true := by
  rw [parL_written h O l d]
  have e := List.all_eq_true.1 fits_later_written l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at e
  cases d with
  | true => exact e.2
  | false => exact e.1

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.oneAns_first_written
#print axioms ProofFile.Honest.K1.oneAns_later_written
#print axioms ProofFile.Honest.K1.fits_first_written
#print axioms ProofFile.Honest.K1.fits_later_written
#print axioms ProofFile.Honest.K1.firstFold_shape
#print axioms ProofFile.Honest.K1.oneAns_two_head
#print axioms ProofFile.Honest.K1.fits_two_head
#print axioms ProofFile.Honest.K1.parL_written
#print axioms ProofFile.Honest.K1.oneAns_fifty_head
#print axioms ProofFile.Honest.K1.fits_fifty_head
