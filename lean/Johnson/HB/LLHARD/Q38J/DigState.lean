-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38J/DigState.lean: the side of the state of `DigAheadOk` behind the approximate
range proof's draw, at each of the 25 segments: all that names neither a witness nor a string.

Why. `DigAheadOk` (Johnson/Desc/First/Look/K3DigitsAhead.lean) asks, of the state behind the draw:
the open segment's part is there; four equations on it; and at each cell of its range six clauses on
one seat. Two of the six speak of the state. This file pays the part, the four equations and these
two clauses at every seat of a cell of the digits' array. The four other clauses are another file's.

What is shown.
  `digState_behind_draw`: **under the head, the facts on every reached state, and the field "near"
    of the condition on the approximate range proof: at every state a that is reached without a mark
    in front of the draw of segment l, and every state b that the draw's accept returns: the part of
    b is there, with the four equations and the two clauses.** A joining: the nine equations in
    front of the draw (`k08_fold_at`); the draw writes its own part of the state alone
    (`drawn_of_yes`, `segAt_behind_draw`); the frame's four facts and the codes (`frameIs_at_draw`,
    `codes_at_draw`); the list of arrays and the layout (`arr_at`, `layout_at`); the reader's value
    for a message that is still ahead (`ahead_of_seats` at `aheadSeats_at_head`); its rectangles
    (`matrixOk_ahead` at `lawful_at_head`); the array's number (`j_zz_built`); the two clauses
    (`ahead_arms`).

Grade. From the head, `FoldFacts` and "near". Of the thirteen entry tests, by the code: rows 9 and
1, both inside `aheadSeats_at_head`. Nothing in this file spends row 11: that `digAt` answers is a
premise here. `FoldFacts` is a premise: the rows that its payer spends are not counted here.

Premises that are bound and not spent. The first antecedent (the promise `onQ`) stands because the
spender's premise has it. Of "near" only this is used: the digits' array is the segment's own, the
layout has it, its message is there, and that message is still ahead.

Limits. No state is shown at which the premises hold together. At `OnBytes.secondHashFunction` alone. The full
size alone. Nothing on soundness.


-/
import Johnson.HB.LLHARD.Q38J.TiesAtDraw
import Johnson.HB.LLHARD.Q38J.LawfulAtHead
import Johnson.HB.LLHARD.Q38J.ZzBuilt
import Johnson.HB.LLHARD.Q38J.AheadArms
import Johnson.HB.LLHARD.Q38A.SegAtBehindDraw
import Johnson.HB.LLHARD.Q38A.DigAtLink
import Johnson.HB.LLHARD.Q38A.MatrixOkAhead
import Johnson.HB.LLHARD.Q38C.AheadOfSeats
import Johnson.HB.LLHARD.Q38C.AheadSeatsAtHead
import Johnson.P1K8R.FoldAtDraw
import Johnson.Desc.First.K8.TieRides

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
/-- **The side of the state, behind the draw.** -/
theorem digState_behind_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps)
    (hnear : aheadPlanSizeB (P1K8T.n0At Zp l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l)
      Xl.arrayOf G.first.layout Zp.first.shape l Xl.tl.ix.ZZ = true)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hx : VerifiableInference.Desc.First.Look.digAt (P5J.At.X Zp) l = some (x, tl)) :
    ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs =
        .ok b.1) →
      ∃ p, VerifiableInference.Desc.K9.segAt? b.1 = some p ∧
        FrameIs h.𝔇.sent x.link p.L.check.frame ∧
        p.L.check.rows.layout = h.𝔇.sent.layout ∧
        p.L.arrayOf = h.𝔇.sent.arrayOf.getD x.link #[] ∧
        p.d.st.codes = h.𝔇.sent.codes ∧
        ∀ (z' : Seat) (u c : ℕ), seatOf h.𝔇.sent x.link (.cell tl.ix.ZZ u c) = some z' →
          (∀ bn h', (h.𝔇.sent.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn →
            aheadIn (h.𝔇.N.sent l) (h.𝔇.N.group l) p bn = some h' →
            (∀ hk : z'.msg < (digList x h.𝔇.sent h.𝔇.l3.rad).length,
              h'.seat = (fun j : Fin (digList x h.𝔇.sent h.𝔇.l3.rad).length =>
                h.𝔇.l3.seat x.link true j.1) ⟨z'.msg, hk⟩) ∧
              laidMatrixOk h'.A (rowBitsOf h'.shape .main)
                (placeBitsOf h.𝔇.sent.codes h'.shape .main) = true) ∧
          (∀ bn a', (h.𝔇.sent.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn →
            aheadIn (h.𝔇.N.sent l) (h.𝔇.N.group l) p bn = none →
            reqArray h.𝔇.sent.layout bn.1 bn.2 = some a' →
            ∃ o, SeatOk h.𝔇.sent.codes (digList x h.𝔇.sent h.𝔇.l3.rad)
                (fun j => h.𝔇.l3.seat x.link true j.1) p.L.check.frame 0 (h.𝔇.N.group l) p.d.st
                p.d.book z' o ∧
              laidMatrixOk a' (p.d.st.rowBits o .main) (p.d.st.placeBits o .main) = true) := by
  intro z a b _ hr hm hd
  obtain ⟨rs, gs, hd⟩ := hd
  have hu : a.1.failed = none := Classical.not_not.1 hm
  obtain ⟨L, Gr, pre, hL, -, -, -, e1, e2, e5, e6, e4⟩ :=
    P1K8T.k08_fold_at h hG hl e3 ((z, a.1), a.2) (hRch _ _ hr)
  have hL' : a.1.link? = some L := hL
  obtain ⟨p, hp, pL, pst⟩ := segAt_behind_draw (drawn_of_yes _ _ _ rs gs hd) hL'
  have exl : x.link = l := digAt_link hx
  have ezz : tl.ix.ZZ = Xl.tl.ix.ZZ := j_zz_built h hG hl e3 hx
  obtain ⟨bn, A, sh, M, f1, -, f3, f4, f5, f6⟩ :=
    ahead_of_seats (P1K8T.n0At Zp l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) p
      Xl.arrayOf G.first.layout Zp.first.shape (P5J.At.seat3At Zp l true) l Xl.tl.ix.ZZ
      (by rw [pL]; exact e1) (by rw [pL]; exact e2) (by rw [pL]; exact e6) (by rw [pL]; exact e4)
      (by rw [pL]; exact e5) hnear (aheadSeats_at_head h.toAtMg hl)
  have f3' : reqArray (P5J.At.layout Zp) l bn.2 = some A := by
    rw [← P1K8T.layout_at hG]
    exact f3
  have hmat : laidMatrixOk A (rowBitsOf M.shape .main) (placeBitsOf (P5J.At.cs Zp) M.shape .main) =
      true := matrixOk_ahead (lawful_at_head h) f3' f4 f5
  have hbn : ((P5J.At.sentAt Zp).arrayOf.getD l #[])[tl.ix.ZZ]? = some bn := by
    rw [← arr_at hG e3, ezz]
    exact f1
  subst exl
  refine ⟨p, hp, ?_, ?_, ?_, ?_, fun z' u c hz => ?_⟩
  · rw [pL]
    exact frameIs_at_draw FF hr hu hL' hl
  · rw [pL]
    exact e2.trans (P1K8T.layout_at hG)
  · rw [pL]
    exact e1.trans (arr_at hG e3)
  · rw [pst]
    exact codes_at_draw FF hr hu
  · exact ahead_arms x tl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.N x.link p
      (P5J.At.seat3At Zp x.link true) (fun _ => rfl) hbn f3' f6 hmat hz

end Q38

#print axioms Q38.digState_behind_draw
