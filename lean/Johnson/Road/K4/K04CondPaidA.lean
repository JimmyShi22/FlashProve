-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04CondPaidA.lean: TEN OF THE FIFTEEN FACTS OF THE FIELD wide OF K4's CONDITION
(K4Cond, Johnson/Road/K4/K04Cond.lean) BY OTHER AUTHORS' THEOREMS ALONG THE VERIFIER's RUN.
Pointwise, at the relation "reached, with a condition Pp on the public part" (RchPub,
Johnson/Top/H0/Walk/ReachPub.lean), general in Pp and in the type Str of what stands beside.

  `WideLeft Dm E x`: WHAT IS LEFT OF THE FIFTEEN (WideFacts, Johnson/Desc/Sound/MgWideFacts.lean),
    under the fields' own names and in their own texts: seatsCarried, msgShapes, pileMasks,
    pileWithin, tidy. Each has a theorem of its authors': not called here; called in
    Johnson/Road/K4/K04CondPaidB.lean (the first four) and K04CondPaidT.lean (tidy).
  `not_mem_of_lay7`: where the test of "K8.lay7" accepts, the state does not stand at the chain's
    end.
  `hRch_pub`: that relation gives the premise on the letter Rch of the theorems called.
  `wide_of_left`: at ANY border k: WideLeft and that test give WideFacts: bookInOrder, bookFits,
    codes, shape, layout, liveShape, liveLayout: Johnson/IMR/AtReach.lean · weightsOk, reqIs:
    Johnson/LTPileR/AtGate.lean · oneRow: oneRowC_not_mem (Johnson/Desc/K13/Law/WithinReached.lean).
No new argument: calls.
Limits. PREMISES, NONE PAID HERE: the goals' scope and an opening (hS, hR, O): THAT THERE IS AN
OPENING IS SHOWN BY NO THEOREM · hp: every sub-protocol's own test on the plan accepts · EQUATIONS
ON THE PARAMETERS: hcs, hsh, hly, hft, hreq · hl: the test of "K8.lay7" at the state · WideLeft. NO
MEMBER IS SHOWN. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.IMR.AtReach
import Johnson.LTPileR.AtGate
import Johnson.Desc.K13.Law.WithinReached
import Johnson.Desc.Sound.MgWideFacts
import Johnson.Top.H0.Walk.ReachPub
import Johnson.Road.K4.K04Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Ready (lay7B)
open VerifiableInference.Desc.Sound (MgData WideData WideFacts)
open Johnson.Desc.First.Walk.Tied (Reach RchPub rchAt_raw)

/-- **What is left of the fifteen facts**, under the fields' own names. -/
structure WideLeft {P : Type} (E : WideData P) (x : P × S) : Prop where
  seatsCarried : VerifiableInference.Desc.K12.Door.atFirstSeats E.d12.L x.2 = true
  msgShapes : VerifiableInference.Desc.K12.Door.atFirstShapes E.d12.M x.2 = true
  pileMasks : VerifiableInference.Desc.K13.pileMasksC x.2 = true
  pileWithin : VerifiableInference.Desc.K13.pileWithinC x.2 = true
  tidy : OnBytes.Means.tidy4B x.2.st = true

/-- Where the test of "K8.lay7" accepts, the state does not stand at the chain's end. -/
theorem not_mem_of_lay7 {o : Option HTailF2} {s : S}
    (h : (o.any fun t => lay7B t s) = true) : ∀ a, s.here ≠ .mem a := by
  intro a ha
  cases o with
  | none => simp at h
  | some t =>
    have h' : lay7B t s = true := by
      simpa using h
    simp [lay7B, S.tl?, ha] at h'

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- "Reached, with a condition on the public part" gives the premise hRch of the theorems called. -/
theorem hRch_pub {Str : Type} (Pp : ProofFile.InstPub → Prop) :
    ∀ (k : ℕ) (a : (ProofFile.InstPub × S) × Str), RchPub (descAt Z A B c) Pp k a →
      Reach 0 c.blocksInOrder (ProofFile.startS Z) k a.1 :=
  fun _ _ h => rchAt_raw h.1

/-- **The fifteen facts at a reached state without a mark, out of the five that are left and the
test of "K8.lay7"**, under hS hR O hp hcs hsh hly hft hreq. -/
theorem wide_of_left {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    (hcs : Dm.cs = (Meaning.K2.sentAt Z).codes) (hsh : Dm.shape = (Meaning.K2.sentAt Z).shape)
    (hly : Dm.layout = (Meaning.K2.sentAt Z).layout) (hft : E.d12.ft = 0)
    (hreq : E.reqW = fun p : ProofFile.InstPub => Verify.words32 p.request)
    {Str : Type} (Pp : ProofFile.InstPub → Prop) {k : ℕ} (a : (ProofFile.InstPub × S) × Str)
    (h : RchPub (descAt Z A B c) Pp k a) (hu : a.1.2.failed = none)
    {o : Option HTailF2} (hl : (o.any fun t => lay7B t a.1.2) = true)
    (Lf : WideLeft E a.1) : WideFacts Dm E a.1 where
  bookInOrder := by
    rw [hft]
    exact Meaning.K2.bookInOrder_field O hp (RchPub (descAt Z A B c) Pp) (fun a => a.1)
      (hRch_pub Pp) k a h hu
  seatsCarried := Lf.seatsCarried
  bookFits := Meaning.K2.bookFits_field O hp (RchPub (descAt Z A B c) Pp) (fun a => a.1)
    (hRch_pub Pp) k a h hu
  msgShapes := Lf.msgShapes
  weightsOk := Meaning.K2.weights_at_open O hp 0 k a.1 (hRch_pub Pp k a h)
  pileMasks := Lf.pileMasks
  pileWithin := Lf.pileWithin
  oneRow := VerifiableInference.Desc.K13.Law.oneRowC_not_mem (not_mem_of_lay7 hl)
  tidy := Lf.tidy
  codes := by
    rw [hcs]
    exact Meaning.K2.codes_field hS hR O hp (RchPub (descAt Z A B c) Pp) (fun a => a.1)
      (hRch_pub Pp) k a h hu
  shape := by
    rw [hsh]
    exact Meaning.K2.shape_field hS hR O hp (RchPub (descAt Z A B c) Pp) (fun a => a.1)
      (hRch_pub Pp) k a h hu
  layout := by
    rw [hly]
    exact Meaning.K2.layout_field hS hR O hp (RchPub (descAt Z A B c) Pp) (fun a => a.1)
      (hRch_pub Pp) k a h hu
  liveShape := by
    rw [hsh]
    exact Meaning.K2.liveShape_field hS hR O hp (RchPub (descAt Z A B c) Pp) (fun a => a.1)
      (hRch_pub Pp) k a h hu
  liveLayout := by
    rw [hly]
    exact Meaning.K2.liveLayout_field hS hR O hp (RchPub (descAt Z A B c) Pp) (fun a => a.1)
      (hRch_pub Pp) k a h hu
  reqIs := by
    rw [hreq]
    exact Meaning.K2.req_at_open O hp 0 k a.1 (hRch_pub Pp k a h) hu

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.not_mem_of_lay7
#print axioms OnBytes.Road.K4.hRch_pub
#print axioms OnBytes.Road.K4.wide_of_left
