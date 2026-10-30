-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/DigAheadAtReach.lean: THE SMALLNESS TEST: THE LOOKUPS' `DigAheadOk`
(Johnson/Desc/First/Look/K3DigitsAhead.lean) BEHIND A DRAW's YES, AT EACH OF THE 25 SEGMENTS AND AT
EVERY WITNESS: FROM THE LIBRARY's HEAD, "REACHED" IN FRONT, "NO MARK" AND THE YES ALONE. One
theorem; no definition; none of the library's goals.

  **`digAhead_at_reach`**   (h : `P5J.AtMgA`) · the blank ground G · l ≤ 24 · the built segment Xl ·
                   `digAt` answers (x, tl) at l · `RchAt` at the draw's border at (z, s) · s bears
                   no mark · the draw's decision says yes from s to t ⊢ DigAheadOk … l t w, at
                   every w
WRITTEN A FURTHER TIME, WITH ONE PREMISE FEWER. The library has this end in `Q38.digAhead_of_fold`
(Johnson/HB/LLHARD/Q38J/DigAhead.lean) over `Q38.digState_behind_draw` (Q38J/DigState.lean). Both
take the table's promise in front of the draw at the library's own meaning and a frame's strings
(`onQ`); neither proof spends it. A stand of the honest thread has that promise at the honest
letters alone, so it cannot call them. Here their lines stand without it; and their premises
`FoldFacts` and "near" are drawn from the head, as Johnson/P1K8R/KindOfOwnSizes.lean draws them
(`P5J.atMgR_of_head`, Johnson/P5J/StartAtHead.lean: general in "reached" · `IM.k08_near_at`,
Johnson/IMR/NearAtDraw.lean).
TWO OPTIONS ARE RAISED (maxHeartbeats, for the file; maxRecDepth, at the theorem) AND ONE INSTANCE
IS TAKEN AWAY (attribute [-instance] Inst.Model.Scl.ref), as in the two files whose lines these are.
NO TACTIC THAT SEARCHES.
Limits. That any state is reached is not said. At OnBytes.secondHashFunction alone. THE FULL SIZE ALONE.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.HB.LLHARD.Q38J.DigAhead
import Johnson.P5J.StartAtHead
import Johnson.IMR.NearAtDraw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest

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
open Q38

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 40000 in
/-- **`DigAheadOk` behind the draw, from "reached", "no mark" and the yes.** -/
theorem digAhead_at_reach (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    (hx : VerifiableInference.Desc.First.Look.digAt (P5J.At.X Zp) l = some (x, tl))
    (z : ProofFile.InstPub) (s t : S)
    (hr : RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (drawAt l) ((z, s), ()))
    (hu : s.failed = none)
    (hd : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide s rs gs = .ok t)
    (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) :
    VerifiableInference.OnPublicFiles.DigAheadOk x tl h.𝔇.sent h.𝔇.l3.rad
      (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.l3.arr h.𝔇.ms h.𝔇.N l t w := by
  obtain ⟨L₀, A₀⟩ := P5J.atMgR_of_head h (Str := Unit)
    (fun k a => RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a) (fun _ _ u => u)
  have FF := A₀.fold
  have hnear := IM.k08_near_at h hG hl e3
  obtain ⟨rs, gs, hd⟩ := hd
  obtain ⟨L, Gr, pre, hL, -, -, -, e1, e2, e5, e6, e4⟩ :=
    P1K8T.k08_fold_at h hG hl e3 ((z, s), ()) hr
  have hL' : s.link? = some L := hL
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
  refine ⟨p, hp, ?_, ?_, ?_, ?_, fun μ hμ u hu' i hi bb hb => ?_⟩
  · rw [pL]
    exact frameIs_at_draw FF (a := ((z, s), ())) hr hu hL' hl
  · rw [pL]
    exact e2.trans (P1K8T.layout_at hG)
  · rw [pL]
    exact e1.trans (arr_at hG e3)
  · rw [pst]
    exact codes_at_draw FF (a := ((z, s), ())) hr hu
  · obtain ⟨zz, c1, c2, c3, c6⟩ := e_digClosed_at_head h hl hx w μ hμ u hu' i hi bb hb
    obtain ⟨c4, c5⟩ := ahead_arms x tl h.𝔇.sent h.𝔇.l3.rad
      (fun j => h.𝔇.l3.seat x.link true j.1) h.𝔇.N x.link p (P5J.At.seat3At Zp x.link true)
      (fun _ => rfl) hbn f3' f6 hmat c1
    exact ⟨zz, c1, c2, c3, c4, c5, c6⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.digAhead_at_reach
