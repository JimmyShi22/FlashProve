-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/MaskPaid.lean: a payment beneath the kind K11's conditions (the merge of the claims on the
committed table): THE FIELD mask OF `K11Tight` (CondOfTight.lean). Two theorems: a call and a
projection.

What is said. `mask_paid`: at the constant's own head h and an opening O at its letters, for every
"reached" Rch that lies within the description's own (hsub): the test `maskAtB` accepts at every
state with the table's condition at 346 that is reached and bears no mark: K11Tight's field mask, to
the letter. It is `maskAtB_seated` (MaskSeat.lean) at the constant's
numbers, the written list, the merge's place and the head's sort of segment.

THE PREMISES THAT ARE LEFT. Six facts on numbers, which read no state (hm, hlt, hnum, hx, hown,
hRb). Three facts along "reached", at 346: seatsCarried, msgShapes (both are fields of `K11Tight`
already) and liveShape: the copy in use has the shape sh.

`rch_within`: the head's own "reached" lies within the description's own, by its first half: hsub
there.

Limits. None of the nine is shown here; seven of them are no fields of `K11Tight`, which keeps mask.
The called theorem may speak of no state: its own head's caution stands. What is known beside: which
sub-protocol stands at numbers 339 and 342 is said in LiveAt339.lean and LiveAt339Cut.lean
(under the test on the plan and the written rows); these two files are imported by no file of this
chain and were compiled in another build; that a step there accepts at some state they do not
show. The shape sh, by which hnum's left side counts, and Bs.G₀.first.shape are tied by nothing.
Nothing on soundness.

-/
import Johnson.K11R.CondOfTight
import Johnson.K11R.MaskSeat
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes (OracleShape ceilLog2)
open OnBytes.Params (ReqShape)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstShapes)
open VerifiableInference.Desc.Sound.MgAt (mergeAt)
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_raw)
open P5J (AtMgA mgAtAll TS)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

set_option maxRecDepth 100000 in
/-- **The field mask of `K11Tight`, from nine premises.** -/
theorem mask_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B) {Fr : Frame}
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (hsub : ∀ a, Rch 346 a → RchAt (FD Zp A B cF) 346 a)
    (xM : Mem) (R O' : ℕ) (L : Laid) (M : List OracleShape) (sh : ReqShape) (m : ℕ)
    (hm : maskNoOf sh 24 = some m) (hlt : m < firstCount sh 24)
    (hnum : O' + (firstCount sh 24 + 1) +
      (momentCount Bs.G₀.first.shape 24 1 + momentCount Bs.G₀.first.shape 24 2) =
        h.𝔇.N.msgsAt (some mergeAt) + m)
    (hx : L.places[O']? = some (seatOf xM)) (hown : seatOf xM ∈ h.𝔇.N.group 24)
    (hRb : (M[O']?).map (fun y => ceilLog2 y.maskRows) = some R)
    (hseats : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
      atFirstSeats L a.1.2 = true)
    (hshapes : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
      atFirstShapes M a.1.2 = true)
    (hlive : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str, Rch 346 a → a.1.2.failed = none →
      a.1.2.live.frame.shape = sh) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
      onQ h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → a.1.failed = none →
      maskAtB (h.𝔇.N.group 24) (seatOf xM) R a.1 = true :=
  maskAtB_seated h.scope h.reads O (ft := 0) (start := ProofFile.startS Zp) Rch h.𝔇.N (mgAtAll h)
    linksFull (flatPlacesOf linksFull true) (h.𝔇.N.group 24) (seatOf xM) R O' L M mergeAt .head sh m
    (fun a h' => rchAt_raw (hsub a h')) hm hlt (by rw [total_addsAt]; exact hnum) k11_there
    (by decide +kernel) hx hown hRb hseats hshapes hlive

/-- The head's own "reached" lies within the description's own: `mask_paid`'s hsub there. -/
theorem rch_within (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : (ProofFile.InstPub × S) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str)
    (h' : h.toAtMg.rch 346 a) :
    RchAt (FD Zp (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) cF) 346 a :=
  h'.1

end K11

#print axioms K11.mask_paid
#print axioms K11.rch_within
