-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K8R/ShareAtDraw.lean: THE SMALLNESS TEST: THE STATE'S SHARE OF THE FIRST HALF OF
"alike" (the premise A of alike_of_rows, Johnson/P1K8R/AlikeOfRows.lean), AT EVERY REACHED STATE IN
FRONT OF LINK l's DRAW ON WHICH NO CHECK HAS FAILED, l ≤ 24: from the head, the facts on every
reached state (FoldFacts at the head's closed term) and ONE TEST WITH CODE ON THE PUBLIC PART.

  k8NumsOf d lay Xl l   the plan's term for the numbers of the state's list: over the arrays that
                    the drawn matrix multiplies (Named.arrays Xl.tl): the built link's table of
                    arrays, the layout's array, and the plan's term whereD for "under which number
                    the statement has the message now", with two moments sent
  msgs_in_nums      at such a state every number of Named.msgs tl L is one of these: by
                    array_of_msgNow (First/K8/LawBlockIn.lean), whereIs_reached
                    (First/Link/Law/PartFitsReached.lean), k08_fold_at
                    (Johnson/P1K8R/FoldAtDraw.lean), draw_place_full
                    (Johnson/P1K8R/SmallAtHead.lean), k8LaidOwn and planAt_built
  share_at_draw     THE SHARE, in the letters of the field alike of K8LeftT
                    (Johnson/P1K8R/TightAt.lean); the table's promise is not spent
  alike_first_at    with alike_of_rows: THE FIRST HALF OF THE FIELD alike, at
                    rad := At.rad3At Zp Z.lay

PREMISES THAT STAY: FF (FoldFacts: Johnson/P5J/FoldJ3Whole.lean has it from the head and tests on
the public part); hT (k8NumsB at link l: a test with code on the public part); for alike_first_at
also alike_of_rows' three: hrows, h1, hSh.
Limits. None of these is shown here. A member of the head is proved at storedPublicFiles and zGap alone (at
secondHashFunction; side library AtFullSide/Top/). The second half of the field
(CellsIn) is not treated. At the second hash function. No soundness statement.

-/
import Johnson.P1K8R.SmallAtHead
import Johnson.P1K8R.ShareOfNums
import Johnson.P1K8R.AlikeOfRows
import Johnson.Desc.First.K8.LawBlockIn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S FoldData FoldFacts flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (seven lay7 lay7_of_test)
open VerifiableInference.Desc.LinkJoin (whereD whereIs_reached)
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA)

/-- **The plan's term for the numbers of the state's list, in front of link l's draw.** -/
def k8NumsOf (d : FoldData) (lay : OnBytes.Params.ReqLayout) (Xl : LinkH) (l : ℕ) : List ℕ :=
  (Named.arrays Xl.tl).filterMap fun t =>
    (Xl.arrayOf[t]?).bind fun x =>
      (OnBytes.reqArray lay x.1 x.2).bind fun a => whereD d l 2 x.1 a.message

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **At a reached state in front of the draw the numbers of the state's list are the plan's.** -/
theorem msgs_in_nums (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Ld : Laid} {Fr : Frame}
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF Ld) P5J.At.reqW P5J.At.links P5J.At.ps)
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl24 : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) (a : (ProofFile.InstPub × S) × Fr.E.Str) {tl : HTailF2}
    {L : LinkCtx} (hr : Rch (drawAt l) a) (hm : a.1.2.failed = none) (ht : a.1.2.tl? = some tl)
    (hL : a.1.2.link? = some L) :
    ∀ o ∈ Named.msgs tl L, o ∈ k8NumsOf (P5J.At.foldD Zp cF Ld) (P5J.At.layout Zp) Xl l := by
  intro o ho
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hr0 := hRch _ _ hr
  have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) a := by
    rw [← drawAt_place]
    exact hr0
  -- the smallness test's part is the built link's, in the seven fields
  obtain ⟨tlP, hv, h7, -⟩ := P1K8S.k8LaidOwn h.scope h.reads O hx a hr'
  have eP : tlP = Xl.tl := P1K8S.planAt_built h.scope h.reads O e3 hv
  have e7 : seven tl = seven Xl.tl := by
    have e := lay7_of_test h7
    unfold lay7 at e
    rw [ht] at e
    rw [← eP]
    exact Option.some.inj e
  have eA : Named.arrays tl = Named.arrays Xl.tl := by
    unfold Named.arrays
    rw [show tl.gtTree = Xl.tl.gtTree from congrArg (·.1) e7,
      show tl.ix = Xl.tl.ix from congrArg (·.2.1) e7]
  -- the open link's table of arrays and layout are the plan's
  obtain ⟨L', -, -, hL', -, -, -, e1, e2, -, -, -⟩ := k08_fold_at h hG hl24 e3 a hr0
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  obtain ⟨p, hp, hlk, hpc, hmo⟩ := draw_place_full l hl24
  obtain ⟨t, htm, hto⟩ := Named.mem_msgs.1 ho
  obtain ⟨x, ar, hx1, hx2, hx3⟩ := array_of_msgNow hto
  have hmo' : VerifiableInference.Desc.First.momentAt
      (VerifiableInference.Desc.First.shiftAt P5J.At.links l) p.piece = 2 := hmo
  rw [whereIs_reached FF hr hm hp hlk hpc hL x.1 ar.message, hmo'] at hx3
  rw [e1] at hx1
  rw [e2, layout_at hG] at hx2
  unfold k8NumsOf
  refine List.mem_filterMap.2 ⟨t, eA ▸ htm, ?_⟩
  rw [hx1]
  show ((OnBytes.reqArray (P5J.At.layout Zp) x.1 x.2).bind fun a =>
    whereD (P5J.At.foldD Zp cF Ld) l 2 x.1 a.message) = some o
  rw [hx2]
  exact hx3

/-- **THE STATE'S SHARE, AT EVERY REACHED STATE IN FRONT OF THE DRAW.** -/
theorem share_at_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (rad : OracleShape → ℕ)
    {Ld : Laid} {Fr : Frame} {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF Ld) P5J.At.reqW P5J.At.links P5J.At.ps)
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl24 : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    (hT : k8NumsB (P5J.At.pseats Zp) Ld (P5J.At.foldD Zp cF Ld).M
      (k8NumsOf (P5J.At.foldD Zp cF Ld) (P5J.At.layout Zp) Xl l) = true) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx),
      Rch (drawAt l) ((z, a.1), a.2) → a.1.failed = none → a.1.tl? = some tl →
      a.1.link? = some L →
      ∀ i : Fin (lA rad a.1 tl L).length, ∃ q ∈ P5J.At.pseats Zp, q.smpd = true ∧
        q.shape = ((lA rad a.1 tl L).get i).1 ∧ q.seat = sA rad a.1 tl L i :=
  fun z a tl L hr hm ht hL => share_of_nums rad a.1 tl L
    (msgs_in_nums h FF hRch hG hl24 e3 ((z, a.1), a.2) hr hm ht hL)
    (FF.msgShapes (drawAt l) ((z, a.1), a.2) hr hm)
    (FF.seatsCarried (drawAt l) ((z, a.1), a.2) hr hm) hT

/-- **THE FIRST HALF OF THE FIELD "alike".** -/
theorem alike_first_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {Ld : Laid} {Fr : Frame} {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF Ld) P5J.At.reqW P5J.At.links P5J.At.ps)
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl24 : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    (hT : k8NumsB (P5J.At.pseats Zp) Ld (P5J.At.foldD Zp cF Ld).M
      (k8NumsOf (P5J.At.foldD Zp cF Ld) (P5J.At.layout Zp) Xl l) = true)
    {rows : List Johnson.G.SendRow} (hrows : P5T.rowsAt? Zp.pol Z.lay Zp.KL = some rows)
    (h1 : P5T.radOneB ((P5T.firstRows rows).flatMap (·.sampled)) = true)
    (hSh : P1Opts.RowsShaped rows (P5J.At.pseats Zp)) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx),
      Rch (drawAt l) ((z, a.1), a.2) → a.1.failed = none → a.1.tl? = some tl →
      a.1.link? = some L →
      ∀ i, ∃ y ∈ P5J.At.ms Zp Z.lay, Alike y
        ⟨⟨lA (P5J.At.rad3At Zp Z.lay) a.1 tl L, sA (P5J.At.rad3At Zp Z.lay) a.1 tl L⟩, i⟩ :=
  fun z a tl L hr hm ht hL => alike_of_rows Zp Z.lay hrows h1 hSh a.1 tl L
    (share_at_draw h _ FF hRch hG hl24 e3 hT z a tl L hr hm ht hL)

end P1K8T

#print axioms P1K8T.msgs_in_nums
#print axioms P1K8T.share_at_draw
#print axioms P1K8T.alike_first_at
