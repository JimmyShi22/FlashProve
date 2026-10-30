-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/TightAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
KIND'S LAW AT THE CLOSED CONSTANT FROM THE TIGHT LIST OF FACTS ALONG THE FOLD THAT IT SPENDS. NO
SOUNDNESS.

`K8LeftC.atFold` (ConstAt.lean) asks seven things of a reached statement in front of the draw.
Four of them follow from NINE PLAIN EQUATIONS ON THE OPEN LINK AND THE STATEMENT OF ORACLES, each of
which is proved in Johnson/IMR/ along the fold from the first state (names in square brackets below;
in another build; not imported), and from two tests with code on the plan:
  `K8FoldAt Z G l Xl n₀ t`: THE TIGHT LIST, at a state t: there are the open link L, a group Gr and
    a list pre with: L is t's link; its frame names group l; group l of t's statement of oracles is
    Gr; Gr's members are pre, then the frame's kept copies, then its own messages [members_at |
    members_head]; L's list of arrays is the built link's and its rows' layout
    the plan's [arrays_open]; the frame has n₀ own messages, the plan's shape and the link's
    number [own_size_draw | own_size_head].
  `frameJoined_of_members`: these give `FrameJoined`.
  `K8LeftT`: WHAT IS LEFT: the piece; `DrawBlind`; the link is there; the tie gives the part
    "small"; the digits; the constant's numbers list group l at segment l; the test `aheadPlanSizeB`
    at the built link's values; `fold`: `K8FoldAt` at every reached statement inside the promise;
    "alike member"; `CellsIn` at the early arrays.
  `k08_leftC_of_tight`: **`K8LeftT` gives `K8LeftC`**, in the goals' scope, under the test
    `ProofFile.smallSizesOwnB` (each built link at its own planned value): by
    `smallSizes_at_state`, `near_of_plan_size`, and `k8LaidOwn`,
    `planAt_built`.
  `k08_at_const_tight`: **THE KIND's SHARE AT THE CLOSED CONSTANT, FROM `K8LeftT`.**
Limits. `K8LeftT` is shown nowhere (Where this and
lean/THEOREM.md differ, the page holds.): NOT TO BE TOLD AS "TIED". n₀ is a letter. AT
`OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.ConstAt
import Johnson.Desc.ProofFile.Lot.K8SmallSizes
import Johnson.Desc.First.Batch.SmallNearSize

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
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (planFitsAllB seven lay7 lay7_of_test)
open VerifiableInference.Desc.K9 (aheadPlanSizeB near_of_plan_size)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- **THE TIGHT LIST OF FACTS ALONG THE FOLD, at the border in front of the draw at link l.** -/
def K8FoldAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (Xl : LinkH) (n₀ : ℕ) (t : S) : Prop :=
  ∃ (L : LinkCtx) (Gr : Group) (pre : Array Nat), t.link? = some L ∧ L.check.frame.group = l ∧
    t.st.groups[l]? = some Gr ∧
    Gr.members = pre ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
    L.arrayOf = Xl.arrayOf ∧ L.check.rows.layout = G.first.layout ∧
    L.check.frame.own.size = n₀ ∧ L.check.frame.shape = Z.first.shape ∧ L.check.frame.link = l

/-- The frame's two lists are members of the group that it names. -/
theorem frameJoined_of_members {St : Statement} {f : ReqFrame} {l : ℕ} {Gr : Group}
    {pre : Array Nat} (hg : f.group = l) (hG : St.groups[l]? = some Gr)
    (hm : Gr.members = pre ++ f.keptBefore ++ f.own) : FrameJoined St f := by
  intro o ho
  refine ⟨Gr, by rw [hg]; exact hG, ?_⟩
  rw [hm]
  rcases ho with ho | ho
  · simp only [Array.toList_append, List.mem_append]
    exact Or.inr ho
  · simp only [Array.toList_append, List.mem_append]
    exact Or.inl (Or.inr ho)

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (rad : OracleShape → ℕ)
  {Fr : Frame} (G : ProofFile.Ground) (l : ℕ) (Xl : LinkH) (n₀ : ℕ)
  (q : Piece (Run.ckP .two) Fr (ProofFile.InstPub × S) Claim
    (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT))
  (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)

/-- **WHAT IS LEFT AT ONE PLACE, WITH THE FACTS ALONG THE FOLD AS A TIGHT LIST.** -/
structure K8LeftT : Prop where
  piece : ∀ B' : Block S Claim,
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (Run.ckP .two) Fr S Claim (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)) =
    ⟨below B', q.base, [rdt (ProofFile.k8ParW Zp G Xl l).toPar], [], fun _ _ w => w,
      Err.cap 128 (uLT (Run.ckP .two) [rdt (ProofFile.k8ParW Zp G Xl l).toPar])⟩
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
    (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs = .ok b.1) →
    (mgAtAll h).constr l .lookDigits (z, b.1) (strsOf Fr b.2) w →
    DigitsAt (cellsAhead (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
      (z, b.1)) b.1 w
  groupAt : (P5J.At.N Zp cF).groupAt l = l
  near : aheadPlanSizeB n₀ ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) Xl.arrayOf
    G.first.layout Zp.first.shape l Xl.tl.ix.ZZ = true
  fold : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str),
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) →
    a.1.failed = none → K8FoldAt Zp G l Xl n₀ a.1
  alike : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx),
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) →
    a.1.failed = none → a.1.tl? = some tl → a.1.link? = some L →
    (∀ i, ∃ y ∈ P5J.At.ms Zp Z.lay, Alike y ⟨⟨lA rad a.1 tl L, sA rad a.1 tl L⟩, i⟩) ∧
      ∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        CellsIn (P5J.At.cs Zp) (lA rad a.1 tl L) (sA rad a.1 tl L) (P5J.At.ms Zp Z.lay)
          (P5J.At.N Zp cF) l a.1 t o

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **`K8LeftT` gives `K8LeftC`.** -/
theorem k08_leftC_of_tight {pp : ScalesAndPolicy} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) (rad : OracleShape → ℕ)
    (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) Zp Bs
      base cF (seatZ Zp Np) (secondAt Zp Np))
    (hOwn : ProofFile.smallSizesOwnB Zp Bs.G₀ = true) {Fr : Frame} {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : Bs.G₀.built[l]? = some Xl) {n₀ : ℕ}
    {q : Piece (Run.ckP .two) Fr (ProofFile.InstPub × S) Claim
      (Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)}
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    (H : K8LeftT h rad Bs.G₀ l Xl n₀ q Rch) :
    K8LeftC h rad Bs.G₀.W l q (ProofFile.k8ParW Zp Bs.G₀ Xl l) Rch := by
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  refine
    { piece := H.piece, blind := H.blind, link := H.link, small := H.small, digits := H.digits
      atFold := fun z a tl L u ha hr hm ht hL hu => ?_ }
  obtain ⟨L', Gr, pre, hL', hg, hGr, hmem, e1, e2, e5, e6, e4⟩ := H.fold z a ha hr hm
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  obtain ⟨hA, hC⟩ := H.alike z a tl L ha hr hm ht hL
  have eu : u.L = L := Option.some.inj ((link_of_segAt a.1 u hu).symm.trans hL)
  have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
    rw [← drawAt_place]
    exact hRch _ _ hr
  obtain ⟨tlP, hv, h7, -⟩ := P1K8S.k8LaidOwn hS hR O hx ((z, a.1), a.2) hr'
  have eP : tlP = Xl.tl := P1K8S.planAt_built hS hR O e3 hv
  have e7 : seven tl = seven Xl.tl := by
    have e := lay7_of_test h7
    unfold lay7 at e
    rw [ht] at e
    rw [← eP]
    exact Option.some.inj e
  have eZ : tl.ix.ZZ = Xl.tl.ix.ZZ := congrArg (·.2.1.ZZ) e7
  refine ⟨frameJoined_of_members hg hGr hmem, hg.trans H.groupAt.symm, hA, hC,
    fun tlQ hq => ?_, ?_⟩
  · rw [eu]
    exact ProofFile.smallSizes_at_state Zp Bs.G₀ hOwn l Xl e3 L tlQ e1 e2
      (by rw [P1K8S.planAt_built hS hR O e3 hq])
  · rw [eZ]
    exact near_of_plan_size n₀ _ _ u Xl.arrayOf Bs.G₀.first.layout Zp.first.shape l _
      (by rw [eu]; exact e1) (by rw [eu]; exact e2) (by rw [eu]; exact e6) (by rw [eu]; exact e4)
      (by rw [eu]; exact e5) H.near

/-- **THE KIND K8's SHARE AT THE CLOSED CONSTANT, FROM THE TIGHT LIST.** -/
theorem k08_at_const_tight (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (hDoor : namesDoorB (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true)
    (hW : planFitsAllB Zp.p.X = true) (hGt : Second.K08.gtSizesAllB Zp.p.X = true)
    (hOwn : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true)
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
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a) (n₀ : ℕ → ℕ)
    (H : ∀ (G : ProofFile.Ground) l Xl q, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
      G.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      K8LeftT h (P5J.At.rad3At Zp Z.lay) G l Xl (n₀ l) q Rch) :
    KindTiedR (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true) Rch E
      (T.p₁ :: T.l₁) KindName.K8 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine k08_at_const h hDoor hW hGt hFit hD hT hf E hE Rch hRch fun G l Xl q hG hl e3 hq => ?_
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  exact k08_leftC_of_tight h _ h.scope h.reads O (hOwn _ hG) hl e3 hRch (H _ l Xl q hG hl e3 hq)

end

end P1K8T

#print axioms P1K8T.k08_at_const_tight
#print axioms P1K8T.frameJoined_of_members
#print axioms P1K8T.k08_leftC_of_tight
