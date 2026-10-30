-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K8R/ConstAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
KIND'S SHARE OF THE CHAIN OF PROMISES AT THE COMPOSED MEANING'S CLOSED CONSTANT. NO SOUNDNESS.

`k08_top` (TopAt.lean) ends at letters: a meaning Mg, the numbers N, the codes, the arrays'
numbers, a reader of OOD samples, the plan's members, the readers of runs. These are written as
ONE closed term: `P5J.mgAtAll h` (Johnson/P5J/MgAtAll.lean), under
one head `P5J.AtMgA`: the goals' scope, "the verifier's own value is laid", the named tests on the
plan. Here `K8Left` is met at that term's own letters, as far as payers lie:
  by the make of the term (rfl): `pin`, "no collision", the item "tie";
  the row's three lists: `row_at_draw_full` (Johnson/Desc/First/K8/RowAtDraw.lean);
  `forms`: `small_at9` (Johnson/Desc/First/K8/FormsAt9.lean);
  the readers at the run "K8.equations": `reader_small` (Johnson/Desc/Sound/MgAt/SmallRun.lean);
  the reader of OOD samples hangs on entry and seat alone, and is blind to the draw:
    `smpNamed_bySeat`, `smpNamed_stays` (Johnson/Desc/Sound/SmpNamed.lean);
  the fence: `k08_fence` (Johnson/P1K8R/FenceAt.lean);
  `SeatsOwn`: `seatsOwn_of_onQ` (Johnson/Desc/First/K8/SeatsOwnPromise.lean);
  128 combinations: `IM.k8_tau_128` (Johnson/K8Q14R/TauAt.lean): the scope fixes them;
  the segment's sort and its run's name: `smallRun_links` (Johnson/K8Q21R/SmallRunAtLinks.lean);
  as many numbers of symbol arrays as matrices: `gtSizes_of_B`
    (Johnson/Second/K08/GtSizesAt.lean), under its test `gtSizesAllB` on the public parameters.
What is left:
  `K8LeftC`: the piece as one equation; `DrawBlind`; the segment's link is there; the tie gives the
    part "small"; the digits; and, at a reached statement inside the promise (`atFold`): the frame's
    two lists are members of the group that it names, which is the segment's listed group; every
    member of the state's list has an alike member in the plan's; `CellsIn` at the early arrays;
    `smallSizesB` at the link's own planned value; the array of digits is near.
  `k08_at_const`: **UNDER THE HEAD `AtMgA` AT `OnBytes.secondHashFunction`, THE TESTS `namesDoorB`,
    `planFitsAllB` AND `gtSizesAllB`, AND `K8LeftC` AT EACH OF THE 25 PLACES: `KindTiedR` … K8 AT
    `mgAtAll h`.**
THE CONDITION BESIDE THE PROMISE IS A LETTER Rch THAT GIVES `RchAt`: `K8LeftC` is asked ALONG Rch
ALONE, and the end stands at Rch: so the law can be called at the join's own narrower "reached" with
no more owed than holds there.
THE RADIUS OF A MEMBER OF THE STATE's LIST IS THE CONSTANT's OWN, BY THE SHAPE (`P5J.At.rad3At Zp
Z.lay`): no free letter in `k08_at_const`. That the seats of the state's list fit the description
follows from "alike" and from "the plan's own members fit" (a premise on the plan alone, `hFit`), by
`P5T.fits_of_some` (Johnson/P5J/Rad3Seat3At.lean).
THE LETTERS OF THE LOT (G) UNDER WHICH `K8LeftC` IS ASKED ARE THE BLANK LETTERS OF THE PUBLIC PART
ITSELF (`ProofFile.blankBy ProofFile.pureRoad.links Zp = some G`: a function of Zp). Asked
at every G with G.W = Zp.p.X, which ties the built links to nothing, that premise
cannot be met.
Limits. `K8LeftC` is shown nowhere (Where this and
lean/THEOREM.md differ, the page holds.): NOT TO BE TOLD AS "TIED". A member of the head is proved
at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). AT `OnBytes.secondHashFunction` ALONE.
Nothing on soundness.

-/
import Johnson.P1K8R.TopAt
import Johnson.P1K8R.FenceAt
import Johnson.P1K8R.KindTiedRIs
import Johnson.P5J.MgAtAll
import Johnson.P5J.Rad3Seat3At
import Johnson.Desc.First.K8.FormsAt9
import Johnson.Desc.First.K8.RowAtDraw
import Johnson.Desc.First.K8.SeatsOwnPromise
import Johnson.Desc.Sound.CellsAtName
import Johnson.Desc.Sound.SmpNamed
import Johnson.K8Q14R.TauAt
import Johnson.K8Q21R.SmallRunAtLinks
import Johnson.Second.K08.GtSizesAt

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail (early)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf runsOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (planFitsAllB)
open VerifiableInference.Desc.K9 (Readers formsInA smallSizesB nearA)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- 1 at the head's link, 0 elsewhere. -/
def oOf (l : ℕ) : ℕ := if l = 24 then 1 else 0

theorem pieceAt_eq (l : ℕ) : VerifiableInference.Desc.First.K8.pieceAt l = 5 + oOf l := by
  unfold VerifiableInference.Desc.First.K8.pieceAt oOf
  split <;> rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (rad : OracleShape → ℕ)
  {Fr : Frame} (Wp : Verify.Public) (l : ℕ)
  (q : Piece (Run.ckP .two) Fr (ProofFile.InstPub × S) Claim
    (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)) (p : ParW)
  (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)

/-- **WHAT IS LEFT AT ONE PLACE, AT THE CONSTANT.** -/
structure K8LeftC : Prop where
  piece : ∀ B' : Block S Claim,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (Run.ckP .two) Fr S Claim (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)) =
    ⟨below B', q.base, [rdt p.toPar], [], fun _ _ w => w,
      Err.cap 128 (uLT (Run.ckP .two) [rdt p.toPar])⟩
  blind : DrawBlind (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
    (drawAt l) q.base (oSAt (P5J.At.N Zp cF) (h.𝔇.Rd l) (4 + oOf l) l)
  link : ∃ Lk, h.𝔇.lk l = some Lk
  small : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) w,
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none →
    TieAt (cellsAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
      (z, a.1)) a.1 w →
    (mgAtAll h).constr l .small (z, a.1) (strsOf Fr a.2) w
  digits : ∀ (z : ProofFile.InstPub) (a b : S × Fr.E.Str) w,
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none →
    (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS p.toPar).decide a.1 rs gs = .ok b.1) →
    (mgAtAll h).constr l .lookDigits (z, b.1) (strsOf Fr b.2) w →
    DigitsAt (cellsAhead (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
      (z, b.1)) b.1 w
  atFold : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx)
    (u : VerifiableInference.Desc.K9.Part),
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) →
    a.1.failed = none → a.1.tl? = some tl → a.1.link? = some L →
    VerifiableInference.Desc.K9.segAt? a.1 = some u →
    FrameJoined a.1.st L.check.frame ∧ L.check.frame.group = (P5J.At.N Zp cF).groupAt l ∧
      (∀ i, ∃ y ∈ P5J.At.ms Zp Z.lay, Alike y ⟨⟨lA rad a.1 tl L, sA rad a.1 tl L⟩, i⟩) ∧
      (∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        CellsIn (P5J.At.cs Zp) (lA rad a.1 tl L) (sA rad a.1 tl L) (P5J.At.ms Zp Z.lay)
          (P5J.At.N Zp cF) l a.1 t o) ∧
      (∀ tlP, P1K8S.PlanAt Wp l tlP →
        smallSizesB u.L.arrayOf u.L.check.rows.layout tlP p.toPar = true) ∧
      nearA ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) u tl.ix.ZZ = true

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The constant's reader of OOD samples is blind to the draw. -/
theorem smp_stays (z : ProofFile.InstPub) (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat) :
    P5J.At.smp Zp (z, s.putTl { tl with cfF := mm, cfFirst := f }) = P5J.At.smp Zp (z, s) := by
  funext u i
  have e := (putTl_rest s { tl with cfF := mm, cfFirst := f }).1
  exact smpNamed_stays (P5J.At.cs Zp) (P5J.At.seats Zp) (z, s)
    (z, s.putTl { tl with cfF := mm, cfFirst := f }) u i (by rw [e]) (by rw [e])

unseal lA sA in
/-- The fence, in this file's spelling. -/
theorem fence_sA {rad : OracleShape → ℕ} {s : S} {tl : HTailF2} {L : LinkCtx} {b₀ : ℕ}
    (h : ∀ i, (Named.seatFn rad s.st s.book tl L i).1 < b₀) : ∀ i, (sA rad s tl L i).1 < b₀ := h

/-- **`K8LeftC` gives `K8Left` at the constant's own letters.** -/
theorem k08_left_const {pp : ScalesAndPolicy} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (rad : OracleShape → ℕ)
    (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) Zp Bs
      base cF (seatZ Zp Np) (secondAt Zp Np))
    {D : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    {T : ThreeAt (Run.ckP .two) D all (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) X₁ X₂
      (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)}
    (hT : OfDesc _ T) (hf : Three.Fits T) (file : String)
    (hD : (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF).data file = .ok D)
    (hP : (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF).planOk = true)
    (hDoor : namesDoorB (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true)
    (hGt : Second.K08.gtSizesAllB Bs.G₀.W = true)
    (hFit : ∀ y ∈ P5J.At.ms Zp Z.lay,
      SeatFits (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (P5J.At.cs Zp) y.1.l y.1.seat)
    {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    {q : Piece (Run.ckP .two) (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Claim
      (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)}
    (hq : (T.p₁ :: T.l₁)[ixOf l]? = some q)
    {Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    (H : K8LeftC h rad Bs.G₀.W l q (ProofFile.k8ParW Zp Bs.G₀ Xl l) Rch) :
    K8Left Zp (seatZ Zp Np) (secondAt Zp Np) cF (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp)
      (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) (mgAtAll h) rad Bs.G₀.W (h.𝔇.Rd l)
      (4 + oOf l) (5 + oOf l) l q (ProofFile.k8ParW Zp Bs.G₀ Xl l) Rch := by
  obtain ⟨rI, rO, rC⟩ := row_at_draw_full l hl
  rw [pieceAt_eq] at rO
  obtain ⟨sub, hsub, hruns⟩ := P5J.At.smallRun_links l hl
  obtain ⟨Lk, hLk⟩ := H.link
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hq' : (T.p₁ :: T.l₁)[14 * l + (if l = 24 then 5 else 4) + 2]? = some q := by
    rw [← drawAt_place]
    exact hq
  refine
    { piece := H.piece, tau := IM.k8_tau_128 hS hR O hl e3, ins := rI, outs := rO, ctx := rC
      blind := H.blind
      pin := fun _ _ _ _ _ hp => hp
      smpStay := fun z s tl mm f _ => smp_stays z s tl mm f
      closes := fun z a w ha hr hm hT' => ⟨H.small z a w ha hr hm hT', hT'⟩
      forms := fun z s y w tl ht hfu hfm =>
        small_at9 (𝔇 := h.𝔇) (Mg := mgBase) l (oOf l) sub hsub hruns Lk hLk z s y w ht hfu hfm
      digits := H.digits
      here := ?_, makes := ?_ }
  · refine ⟨fun _ _ _ _ hn => hn, smpNamed_bySeat _ _, fun z a tl L ha hr hm ht hL => ?_⟩
    obtain ⟨F', hF⟩ := fork_of_onQ _ _ (fun s => (z, s)) l hl a ha hm
    obtain ⟨u, hu, -, -, -⟩ := VerifiableInference.Desc.K9.segAt_of a.1 L F' tl hL hF ht
    obtain ⟨hJ, hg, hsome, hC, -, -⟩ := H.atFold z a tl L u ha hr hm ht hL hu
    have hfits := P5T.fits_of_some _ _ _ _ _ hFit hsome
    have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
        (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
      rw [← drawAt_place]
      exact hRch _ _ hr
    obtain ⟨tl', L', ht', hL', hN⟩ :=
      P1K8S.namedB_of_reach hS hR O hP hDoor hx e3 ((z, a.1), a.2) hr'
    obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
    obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
    exact ⟨hJ, hg, hsome, hfits,
      fence_sA (P1K8S.k08_fence hS hR O hT hf file hD hP hx e3 hq' rad a.1.st a.1.book tl L hN),
      hC⟩
  · refine ⟨fun t => reader_small (𝔇 := h.𝔇) l Lk hLk (4 + oOf l) t,
      fun tlP hv => Second.K08.gtSizes_of_B hGt tlP (P1K8S.planVal_of_at hv),
      fun z a u tl ha hr hm hu ht => ?_⟩
    obtain ⟨L, hL⟩ : ∃ L, a.1.link? = some L :=
      ⟨u.L, link_of_segAt a.1 u hu⟩
    obtain ⟨hJ, hg, -, -, hsz, hnear⟩ := H.atFold z a tl L u ha hr hm ht hL hu
    refine ⟨hsz, seatsOwn_of_onQ _ _ (fun s => (z, s)) l hl a ha hm (fun L' hL' => ?_) _, hnear⟩
    obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
    exact ⟨hJ, hg⟩

/-- **THE KIND K8's SHARE OF THE CHAIN OF PROMISES, AT THE CLOSED CONSTANT.** -/
theorem k08_at_const (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (hDoor : namesDoorB (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true)
    (hW : planFitsAllB Zp.p.X = true) (hGt : Second.K08.gtSizesAllB Zp.p.X = true)
    (hFit : ∀ y ∈ P5J.At.ms Zp Z.lay,
      SeatFits (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (P5J.At.cs Zp) y.1.l y.1.seat)
    {D : WholeD} (hD : (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF).data "proof file" = .ok D)
    {all : List LeftT} {X₁ X₂ : Type}
    {T : ThreeAt (Run.ckP .two) D all (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) X₁ X₂
      (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)}
    (hT : OfDesc _ T) (hf : Three.Fits T)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
      Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hE : ∀ l, l ≤ 24 → ∀ a b w, E (ixOf l) a b w = w)
    (Rch : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    (H : ∀ (G : ProofFile.Ground) l Xl q, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
      G.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      K8LeftC h (P5J.At.rad3At Zp Z.lay) G.W l q (ProofFile.k8ParW Zp G Xl l) Rch) :
    KindTiedR (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true) Rch E
      (T.p₁ :: T.l₁) KindName.K8 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW' : planFitsAllB Bs.G₀.W = true := by
    rw [O.W]
    exact hW
  have hGt' : Second.K08.gtSizesAllB Bs.G₀.W = true := by
    rw [O.W]
    exact hGt
  exact k08_top h.scope h.reads O h.laid.planOk hDoor hW' hT (P5J.At.N Zp cF) (mgAtAll h) E hE
    (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.smp Zp) (P5J.At.ms Zp Z.lay) (P5J.At.rad3At Zp Z.lay)
    (fun l => h.𝔇.Rd l) (fun l => 4 + oOf l) (fun l => 5 + oOf l) Rch hRch
    fun l Xl q hl e3 hq =>
      k08_left_const h (P5J.At.rad3At Zp Z.lay) h.scope h.reads O hT hf "proof file" hD
        h.laid.planOk hDoor hGt' hFit hl e3 hq hRch (H Bs.G₀ l Xl q O.blank hl e3 hq)

end

end P1K8T

#print axioms P1K8T.k08_at_const
#print axioms P1K8T.smp_stays
#print axioms P1K8T.k08_left_const
