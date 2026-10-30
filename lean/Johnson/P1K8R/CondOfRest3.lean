-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/CondOfRest3.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: "REST
GIVES CONDITION", A THIRD STEP: SEVEN OF `K8Rest2`'s CLOSED FIELDS ARE
THEOREMS UNDER THE HEAD AND ARE CALLED. NO SOUNDNESS.

  planFits, gtSizes: `planFitsAllB_of_public`, `gtSizesAllB_of_public`
    (Johnson/Desc/Sound/K8Tests/): at everything that the planner's reader of the public files
    returns;
  ground: the head's opening, and `IM.ground_tails`: the 25 built links are there;
  laid, start: `P5J.atMgR_of_head` (Johnson/P5J/StartAtHead.lean);
  sends: `P5J.sendsB_of_madeRow` at `P5J.madeRow_at_head`;
  fence: `k8Fence_at_head` (Johnson/P1K8R/BlindFromHead.lean).
  THE LAST FOUR ARE "FROM THE HEAD (WITH THE FOURTEEN ENTRY TESTS)": they spend the head's field on
  the entry tests' accept, among whose fourteen rows are the two pins on the made plan and the cut.
  `K8Rest3`: WHAT IS LEFT: (a) seven closed fields on public data: `door`, `ownSizes`, `link`,
    `small`, `near`, `nums`, `rows`; (b) the two that read states and witnesses: `ahead`, `cells`.
  `k08_rest2_of_rest3`: **`K8Rest3 h` gives `K8Rest2 h`**; `k08_cond_of_rest3`, `k08_kind_of_rest3`:
    so it gives `h.K8Cond 𝔏` and `h.Kind 𝔏 K8`.
Limits. `K8Rest3` is shown nowhere here. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.CondOfRest2
import Johnson.P1K8R.BlindFromHead
import Johnson.P5J.StartAtHead
import Johnson.Desc.Sound.K8Tests.GtSizesOfPublic

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
open VerifiableInference.Desc.K9 (aheadPlanSizeB)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT OF THE KIND's NAMED CONDITION, THIRD STEP.** -/
structure K8Rest3 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : Prop where
  door : namesDoorB (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true
  ownSizes : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true
  link : ∀ l, l ≤ 24 → k8LinkB Zp l = true
  small : ∀ (G : ProofFile.Ground) l Xl L₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl → P5J.At.laid? Zp = some L₀ → smallPlanB Zp cF L₀ l Xl = true
  near : ∀ (G : ProofFile.Ground) l Xl, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl →
    aheadPlanSizeB (n0At Zp l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) Xl.arrayOf
      G.first.layout Zp.first.shape l Xl.tl.ix.ZZ = true
  nums : ∀ (G : ProofFile.Ground) l Xl L₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl → P5J.At.laid? Zp = some L₀ →
    k8NumsB (P5J.At.pseats Zp) L₀ (P5J.At.foldD Zp cF L₀).M
      (k8NumsOf (P5J.At.foldD Zp cF L₀) (P5J.At.layout Zp) Xl l) = true
  rows : ∃ rows, P5T.rowsAt? Zp.pol Z.lay Zp.KL = some rows ∧
    P5T.radOneB ((P5T.firstRows rows).flatMap (·.sampled)) = true ∧
    rowsShapedB rows (P5J.At.pseats Zp) Zp.made.proof.1.sends.length = true
  ahead : ∀ (G : ProofFile.Ground) l Xl, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl →
    ∀ (xd : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2),
    VerifiableInference.Desc.First.Look.digAt (P5J.At.X Zp) l = some (xd, tl) →
    ∀ (z : ProofFile.InstPub) (a b : S × (FrK D).E.Str)
    (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT),
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    h.rchU (drawAt l) ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none →
    (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs = .ok b.1) →
    VerifiableInference.OnPublicFiles.DigAheadOk xd tl h.𝔇.sent h.𝔇.l3.rad
      (fun j => h.𝔇.l3.seat xd.link true j.1) h.𝔇.l3.arr h.𝔇.ms h.𝔇.N l b.1 w
  cells : ∀ l, l ≤ 24 → ∀ (z : ProofFile.InstPub) (a : S × (FrK D).E.Str) (tl : HTailF2)
      (L : LinkCtx),
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    h.rchU (drawAt l) ((z, a.1), a.2) →
    a.1.failed = none → a.1.tl? = some tl → a.1.link? = some L →
    ∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
      CellsIn (P5J.At.cs Zp) (lA (P5J.At.rad3At Zp Z.lay) a.1 tl L)
        (sA (P5J.At.rad3At Zp Z.lay) a.1 tl L) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l a.1 t o

/-- Under the head the blank ground is made and has its 25 built links. -/
theorem ground_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G ∧
      ∀ l, l ≤ 24 → ∃ Xl, G.built[l]? = some Xl := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨tails, l24, e24, -⟩ := IM.ground_tails h.scope h.reads O.pub O.blank
  refine ⟨Bs.G₀, O.blank, fun l hl => ?_⟩
  by_cases h24 : l = 24
  · subst h24
    exact ⟨l24, e24⟩
  · obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    obtain ⟨-, -, y, y', -, -, ey, -, -, -, -, -, ey', -⟩ := tails g (by omega)
    rcases hg with rfl | rfl
    · exact ⟨y, ey⟩
    · exact ⟨y', ey'⟩

/-- **THE THIRD REST GIVES THE SECOND.** -/
theorem k08_rest2_of_rest3 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (R : K8Rest3 h) :
    K8Rest2 h := by
  obtain ⟨L₀, A⟩ := P5J.atMgR_of_head h h.rchU (fun _ _ u => u.1.1)
  exact
    { door := R.door
      planFits := LT28.K8Tests.planFitsAllB_of_public h.pubOne
      gtSizes := LT28.K8Tests.gtSizesAllB_of_public h.pubOne
      ownSizes := R.ownSizes
      laid := ⟨L₀, A.listed⟩
      start := A.start
      sends := P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg)
      fence := fun _ hl => k8Fence_at_head h hl
      link := R.link, small := R.small, near := R.near
      ground := ground_at_head h
      nums := R.nums, rows := R.rows, ahead := R.ahead, cells := R.cells }

/-- So it gives the frozen named condition. -/
theorem k08_cond_of_rest3 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (R : K8Rest3 h) : h.K8Cond 𝔏 :=
  k08_cond_of_rest2 h 𝔏 q₁ q₂ q₃ (k08_rest2_of_rest3 h R)

/-- And the kind's field of the table. -/
theorem k08_kind_of_rest3 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (R : K8Rest3 h) : h.Kind 𝔏 KindName.K8 :=
  k08_kind_of_rest2 h 𝔏 q₁ q₂ q₃ (k08_rest2_of_rest3 h R)

end P1K8T

#print axioms P1K8T.ground_at_head
#print axioms P1K8T.k08_rest2_of_rest3
#print axioms P1K8T.k08_cond_of_rest3
#print axioms P1K8T.k08_kind_of_rest3
