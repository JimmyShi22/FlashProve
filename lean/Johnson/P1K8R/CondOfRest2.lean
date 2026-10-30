-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/CondOfRest2.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: "REST
GIVES CONDITION", A SECOND STEP: OF THE TWO FIELDS OF `K8Rest` THAT READ
STATES AND WITNESSES, `digits` IS CUT DOWN TO `DigAheadOk` BEHIND THE DRAW, AND THE
FIRST HALF OF `alike` TO CLOSED TESTS. NO SOUNDNESS.

  digits: `k08_digits_from_ahead` (Johnson/P1K8R/DigitsFromAhead.lean): the head and `DigAheadOk`;
  alike, first half: `alike_first_at` (Johnson/P1K8R/ShareAtDraw.lean): the head, the facts along
    "reached" (here called: `P5J.foldFacts_at_head'`), the test `k8NumsB`, "the rows can be read",
    the tests `radOneB` and `rowsShapedB` (`rowsShaped_at`, Johnson/P1K8R/RowsShapedTest.lean).
  `K8Rest2`: WHAT IS LEFT: (a) closed, on public data: `K8Rest`'s eleven, and these four; (b) TWO
    SENTENCES THAT READ STATES AND WITNESSES: `ahead` (`DigAheadOk` at the state behind a yes of the
    draw) and `cells` (`CellsIn` at the early arrays: the second half of `alike`, to the letter).
  `k08_rest_of_rest2`: **`K8Rest2 h` gives `K8Rest h`**; `k08_cond_of_rest2`, `k08_kind_of_rest2`:
    so it gives `h.K8Cond 𝔏` and `h.Kind 𝔏 K8`.
Limits. `K8Rest2` is shown nowhere here. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.CondOfRest
import Johnson.P1K8R.DigitsFromAhead
import Johnson.P1K8R.ShareAtDraw
import Johnson.P1K8R.RowsShapedTest

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
open VerifiableInference.Desc.First.K8.Ready (planFitsAllB)
open VerifiableInference.Desc.K9 (aheadPlanSizeB)
open VerifiableInference.PlanWritten (cutOf)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT OF THE KIND's NAMED CONDITION, SECOND STEP.** -/
structure K8Rest2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : Prop where
  door : namesDoorB (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true
  planFits : planFitsAllB Zp.p.X = true
  gtSizes : Second.K08.gtSizesAllB Zp.p.X = true
  ownSizes : ∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true
  laid : ∃ L₀, P5J.At.laid? Zp = some L₀
  start : VerifiableInference.Desc.First.FillP1.startB Zp
    (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1)
    (P5J.At.N Zp cF).indexNo = true
  sends : P5J.SendsB Zp
  fence : ∀ l, l ≤ 24 → k8FenceB (P5J.At.N Zp cF) (cutOf cF.blocksInOrder) l = true
  link : ∀ l, l ≤ 24 → k8LinkB Zp l = true
  small : ∀ (G : ProofFile.Ground) l Xl L₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl → P5J.At.laid? Zp = some L₀ → smallPlanB Zp cF L₀ l Xl = true
  near : ∀ (G : ProofFile.Ground) l Xl, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl →
    aheadPlanSizeB (n0At Zp l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) Xl.arrayOf
      G.first.layout Zp.first.shape l Xl.tl.ix.ZZ = true
  ground : ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G ∧
    ∀ l, l ≤ 24 → ∃ Xl, G.built[l]? = some Xl
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

/-- **THE SECOND REST GIVES THE FIRST.** -/
theorem k08_rest_of_rest2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (R : K8Rest2 h) :
    K8Rest h := by
  obtain ⟨L₀, hL₀⟩ := R.laid
  obtain ⟨G, hG, hX⟩ := R.ground
  obtain ⟨rows, hrows, h1, hSh⟩ := R.rows
  have hU : ∀ k a, h.rchU k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a :=
    fun _ _ u => u.1.1
  have FF := P5J.foldFacts_at_head' h.toAtMg h.rchU hU hL₀ R.start R.sends
  exact
    { door := R.door, planFits := R.planFits, gtSizes := R.gtSizes, ownSizes := R.ownSizes
      laid := R.laid, start := R.start, sends := R.sends, fence := R.fence, link := R.link
      small := R.small, near := R.near
      digits := fun G' l Xl hG' hl e3 =>
        k08_digits_from_ahead h hG' hl e3 hU (R.ahead G' l Xl hG' hl e3)
      alike := fun l hl z a tl L ha hr hm ht hL => by
        obtain ⟨Xl, e3⟩ := hX l hl
        exact ⟨alike_first_at h FF hU hG hl e3 (R.nums G l Xl L₀ hG hl e3 hL₀) hrows h1
          (rowsShaped_at Zp hSh) z a tl L hr hm ht hL, R.cells l hl z a tl L ha hr hm ht hL⟩ }

/-- So it gives the frozen named condition. -/
theorem k08_cond_of_rest2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (R : K8Rest2 h) : h.K8Cond 𝔏 :=
  k08_cond_of_rest h 𝔏 q₁ q₂ q₃ (k08_rest_of_rest2 h R)

/-- And the kind's field of the table. -/
theorem k08_kind_of_rest2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (R : K8Rest2 h) : h.Kind 𝔏 KindName.K8 :=
  k08_kind_of_rest h 𝔏 q₁ q₂ q₃ (k08_rest_of_rest2 h R)

end P1K8T

#print axioms P1K8T.k08_rest_of_rest2
#print axioms P1K8T.k08_cond_of_rest2
#print axioms P1K8T.k08_kind_of_rest2
