-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38J/DigAhead.lean: `DigAheadOk` behind the approximate range proof's draw, at
each of the 25 segments: the premise K of the law that gives the field "digits" of the condition on
the approximate range proof.

Why. `k08_digits_from_ahead` (Johnson/P1K8R/DigitsFromAhead.lean) gives that field
from the head and one premise K: `DigAheadOk` at the state behind the draw's accept, at whatever
place and parameters `digAt` returns at the segment. The end of the theorem here is K's
text, copied from that file sign for sign.

What is shown.
  `digAhead_of_fold`: **K, from the head, the facts on every reached state (`FoldFacts`) and the
    field "near" of the same condition.** A joining of two sides at one seat for each cell of the
    range: the side of the state (`digState_behind_draw`) and the closed side
    (`e_digClosed_at_head`): the seat that the closed side finds goes into the two clauses of the
    side of the state.

Grade. From the head, `FoldFacts` and "near". Of the fourteen entry tests, by the code: rows 1, 9
and 11 (rows 9 and 1 on both sides, row 11 on the closed side). `FoldFacts` is a premise: the rows
that its payer spends are not counted here.

One call short. `FoldFacts` stays a premise. `P5J.atMgR_of_head` (Johnson/P5J/StartAtHead.lean)
draws it from the head by one call; that file is not imported here, and which entry tests it spends
was not read. Johnson/P1K8R/KindOfOwnSizes.lean, which spends this theorem, has `FoldFacts` at
hand where it calls it.

Limits. No state is shown at which the premises hold together. A member of the head is proved at the
second hash function `OnBytes.secondHashFunction`, at the two written sets of public files `VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap`, in the side library (AtFullSide/Top/: `headMember_zFull`, `headMember_zGap`); at
other files or another hash none is shown. At `OnBytes.secondHashFunction` alone. The full size alone. Nothing
on soundness.


-/
import Johnson.HB.LLHARD.Q38J.DigState
import Johnson.HB.LLHARD.Q38E.DigClosedAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace Q38

open Iop
open OnBytes OnBytes.Model OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Numbers FoldFacts flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (FrameIs MemAt SeatOk)
open VerifiableInference.Desc.K9 (Ahead aheadIn rowBitsOf placeBitsOf aheadPlanSizeB)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 40000 in
/-- **`DigAheadOk` behind the draw.** -/
theorem digAhead_of_fold (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps)
    (hnear : aheadPlanSizeB (P1K8T.n0At Zp l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l)
      Xl.arrayOf G.first.layout Zp.first.shape l Xl.tl.ix.ZZ = true) :
    ∀ (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2),
      VerifiableInference.Desc.First.Look.digAt (P5J.At.X Zp) l = some (x, tl) →
      ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str)
      (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs =
        .ok b.1) →
      VerifiableInference.OnPublicFiles.DigAheadOk x tl h.𝔇.sent h.𝔇.l3.rad
        (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr h.𝔇.ms h.𝔇.N l b.1 w := by
  intro x tl hx z a b w h1 h2 h3 h4
  obtain ⟨p, hp, s1, s2, s3, s4, arms⟩ :=
    digState_behind_draw h hG hl e3 hRch FF hnear hx z a b h1 h2 h3 h4
  refine ⟨p, hp, s1, s2, s3, s4, fun μ hμ u hu i hi bb hb => ?_⟩
  obtain ⟨zz, c1, c2, c3, c6⟩ := e_digClosed_at_head h hl hx w μ hμ u hu i hi bb hb
  obtain ⟨c4, c5⟩ := arms zz u _ c1
  exact ⟨zz, c1, c2, c3, c4, c5, c6⟩

end Q38

#print axioms Q38.digAhead_of_fold
