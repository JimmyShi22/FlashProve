-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04CondPaidB.lean: THE FIVE SENTENCES ALONG THE VERIFIER's RUN THAT ARE LEFT OF K4's
CONDITION (K4Cond, Johnson/Road/K4/K04Cond.lean: the four facts of its field wide that
Johnson/Road/K4/K04CondPaidA.lean leaves beside tidy, and its field room) BY THEIR AUTHORS'
THEOREMS: EACH CALLED, POINTWISE, at the relation "reached, with a condition Pp on the public part"
(RchPub, Johnson/Top/H0/Walk/ReachPub.lean), general in Pp and in the type Str of what stands
beside.

  `hRch_raw`, `hRch_below`, `hRch_fold`: that relation gives the premise on the letter Rch in each
    of the three forms in which the theorems called ask it.
  `seats_at_pub`, `shapes_at_pub`: seatsCarried, msgShapes, at ANY border k: seatsCarried_field,
    msgShapes_field (Johnson/IMR/SeatsField.lean).
  `pileMasks_at_pub`, `pileWithin_at_pub`: at ANY border k: pileMasks_field_at, pileWithin_field_at
    (Johnson/LPFK9R/ThreeK13Fields.lean).
  `r0_paid`: the field room, at 28 g + 4: room_field_paid (Johnson/P1L20R/RoomKeepAll.lean) and
    free0_is (Johnson/P1L20R/Free0Is.lean).
No new argument: calls.
Limits. PREMISES, NONE PAID HERE: the goals' scope and an opening (hS, hR, O): THAT THERE IS AN
OPENING IS SHOWN BY NO THEOREM · hF: the opening's value's test on the plan accepts · hp: every
sub-protocol's own test on the plan accepts · TWO TESTS WITH CODE ON THE PUBLIC PARAMETERS: hB
(sendsAreB) and hst (startB; a theorem under two premises: Johnson/Road/K4/StartWritten.lean) · hLd:
the list of seats E.d12.L is laidAtCodes' value · EQUATIONS ON THE PARAMETERS: hM, hfv, hf0. NO
MEMBER IS KNOWN: no place where the premises hold together is shown. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.IMR.SeatsField
import Johnson.LPFK9R.ThreeK13Fields
import Johnson.P1L20R.RoomKeepAll
import Johnson.P1L20R.Free0Is
import Johnson.Desc.Sound.MgWide
import Johnson.Top.H0.Walk.ReachPub
import Johnson.Top.H0.Walk.ReachPure
import Johnson.Road.K4.K04Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (WideData)
open Johnson.Desc.First.Walk.Tied (Reach RchPub rchAt_raw roomIsB)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- "Reached, with a condition on the public part" gives the premise hRch: by the chain's own
sub-protocols. -/
theorem hRch_raw {Str : Type} (Pp : ProofFile.InstPub → Prop) :
    ∀ (k : ℕ) (a : (ProofFile.InstPub × S) × Str), RchPub (descAt Z A B c) Pp k a →
      Reach 0 c.blocksInOrder (ProofFile.startS Z) k a.1 :=
  fun _ _ h => rchAt_raw h.1

/-- By the wrapped sub-protocols: the relation's own text. -/
theorem hRch_below {Str : Type} (Pp : ProofFile.InstPub → Prop) :
    ∀ (k : ℕ) (a : (ProofFile.InstPub × S) × Str), RchPub (descAt Z A B c) Pp k a →
      Reach 0 (c.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Z) k a.1 :=
  fun _ _ h => h.1

/-- As the return of a fold. -/
theorem hRch_fold {Str : Type} (Pp : ProofFile.InstPub → Prop) :
    ∀ (k : ℕ) (a : (ProofFile.InstPub × S) × Str), RchPub (descAt Z A B c) Pp k a →
      ∃ rs cols r q, VerifiableInference.Desc.foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z a.1.1)
        rs cols = .ok (a.1.2, r, q) :=
  fun _ _ h =>
    let ⟨_, rs, cols, e⟩ := Johnson.Desc.First.Walk.Tied.rch_pure_fold h.1
    ⟨rs, cols, [], [], e⟩

/-- **The fact seatsCarried at a reached state without a mark**, under hS hR O hF hB hLd. -/
theorem seats_at_pub (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358
      (VerifiableInference.Desc.K12.Door.snAt Z Bs.G₀ IM.placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 =
      some E.d12.L)
    {Str : Type} (Pp : ProofFile.InstPub → Prop) {k : ℕ} (a : (ProofFile.InstPub × S) × Str)
    (h : RchPub (descAt Z A B c) Pp k a) (hu : a.1.2.failed = none) :
    VerifiableInference.Desc.K12.Door.atFirstSeats E.d12.L a.1.2 = true :=
  IM.seatsCarried_field hS hR O (RchPub (descAt Z A B c) Pp) (fun a => a.1) (hRch_fold Pp) hF hB
    hLd k a h hu

/-- **The fact msgShapes at a reached state without a mark**, under hS hR O hF hB hM. -/
theorem shapes_at_pub (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hB : VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358
      (VerifiableInference.Desc.K12.Door.snAt Z Bs.G₀ IM.placesW) = true)
    (hM : E.d12.M = VerifiableInference.Desc.K12.Door.msgsOfChain Z.made.proof.1)
    {Str : Type} (Pp : ProofFile.InstPub → Prop) {k : ℕ} (a : (ProofFile.InstPub × S) × Str)
    (h : RchPub (descAt Z A B c) Pp k a) (hu : a.1.2.failed = none) :
    VerifiableInference.Desc.K12.Door.atFirstShapes E.d12.M a.1.2 = true := by
  rw [hM]
  exact IM.msgShapes_field hS hR O (RchPub (descAt Z A B c) Pp) (fun a => a.1) (hRch_fold Pp) hF
    hB k a h hu

/-- **The fact pileMasks at a reached state without a mark**, under hS hR O. -/
theorem pileMasks_at_pub
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {Str : Type} (Pp : ProofFile.InstPub → Prop) {k : ℕ} (a : (ProofFile.InstPub × S) × Str)
    (h : RchPub (descAt Z A B c) Pp k a) (hu : a.1.2.failed = none) :
    VerifiableInference.Desc.K13.pileMasksC a.1.2 = true :=
  LPFK9.pileMasks_field_at (Rch := RchPub (descAt Z A B c) Pp) (at_ := fun a => a.1) hS hR O
    (hRch_below Pp) k a h hu

/-- **The fact pileWithin at a reached state without a mark**, under O hF. -/
theorem pileWithin_at_pub
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hF : F.planOk = true)
    {Str : Type} (Pp : ProofFile.InstPub → Prop) {k : ℕ} (a : (ProofFile.InstPub × S) × Str)
    (h : RchPub (descAt Z A B c) Pp k a) (hu : a.1.2.failed = none) :
    VerifiableInference.Desc.K13.pileWithinC a.1.2 = true :=
  LPFK9.pileWithin_field_at (Rch := RchPub (descAt Z A B c) Pp) (at_ := fun a => a.1) O hF
    (hRch_below Pp) k a h hu

/-- **The field room**, under hS hR O hp hg hfv hf0 hst. -/
theorem r0_paid (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12)
    (hfv : E.dP.fvs = Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links)
    {M : List OracleShape} {ix : ℕ}
    (hf0 : E.dP.free0 = VerifiableInference.Desc.First.FillP1.free0Of Z.first.codes M ix)
    (hst : VerifiableInference.Desc.First.FillP1.startB Z M ix = true)
    {Str : Type} (Pp : ProofFile.InstPub → Prop) (a : (ProofFile.InstPub × S) × Str)
    (h : RchPub (descAt Z A B c) Pp (28 * g + 4) a) (hu : a.1.2.failed = none) :
    roomIsB E.dP.free0 E.dP.fvs (2 * g) a.1.2 = true := by
  have H := atK4_full g hg
  rw [hfv, hf0, ← P1L20.free0_is O hst]
  exact P1L20.room_field_paid hS hR O hp (Rch := RchPub (descAt Z A B c) Pp)
    (at_ := fun a => a.1) (hRch_raw Pp) (28 * g + 4) a (k4PlaceAt g) (2 * g) h hu H.here H.link
    (by rw [H.piece]; decide)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hRch_raw
#print axioms OnBytes.Road.K4.hRch_below
#print axioms OnBytes.Road.K4.hRch_fold
#print axioms OnBytes.Road.K4.seats_at_pub
#print axioms OnBytes.Road.K4.shapes_at_pub
#print axioms OnBytes.Road.K4.pileMasks_at_pub
#print axioms OnBytes.Road.K4.pileWithin_at_pub
#print axioms OnBytes.Road.K4.r0_paid
