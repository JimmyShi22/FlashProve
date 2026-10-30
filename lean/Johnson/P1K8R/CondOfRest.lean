-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/CondOfRest.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: "REST
GIVES CONDITION": THE KIND'S FROZEN NAMED CONDITION `P5J.AtMgA.K8Cond` FROM WHAT IS LEFT OF IT.
NO SOUNDNESS.

`K8Cond h 𝔏` (Johnson/Goal/Skeleton/Kinds/K8Bridge.lean) is four closed tests and, at each of the 25
links, `K8LeftT`'s nine fields. Of the nine, six are had here by calls:
  piece: `k08_piece_at_row` (from the head); fold: `k08_fold_field` (from the head), at n₀ := `n0At
    Zp`; groupAt: by the make;
  blind: `blind_of_test` (the head and the test `k8FenceB`);
  link: `k8Link_tie` (the test `k8LinkB`);
  small: `small_closed` (the head, three closed premises, the test
    `smallPlanB`).
  `K8Rest`: WHAT IS LEFT: (a) closed, on public data: the condition's own four tests; "the plan's
    list of seats can be laid", `startB`, `SendsB`; at each link `k8FenceB`, `k8LinkB`, `smallPlanB`
    and the field `near` at `n0At Zp l`; (b) THE TWO FIELDS THAT STILL READ STATES AND WITNESSES:
    `digits` and `alike`, to the letter.
  `k08_cond_of_rest`: **`K8Rest h 𝔏` gives `h.K8Cond 𝔏`.**
  `k08_kind_of_rest`: so it gives `h.Kind 𝔏 K8` (`P5J.k08_kind_all`).
Limits. `K8Rest` is shown nowhere here. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.SmallClosed
import Johnson.P1K8R.BlindOfTest
import Johnson.Goal.Skeleton.Kinds.K8Bridge

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

/-- The first chain's frame at the seated row. -/
abbrev FrK (D : WholeD) : Frame :=
  frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **WHAT IS LEFT OF THE KIND's NAMED CONDITION.** -/
structure K8Rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : Prop where
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
  digits : ∀ (G : ProofFile.Ground) l Xl, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl → ∀ (z : ProofFile.InstPub) (a b : S × (FrK D).E.Str) w,
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    h.rchU (drawAt l) ((z, a.1), a.2) →
    ¬ a.1.failed ≠ none →
    (∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide a.1 rs gs = .ok b.1) →
    (mgAtAll h).constr l .lookDigits (z, b.1) (strsOf (FrK D) b.2) w →
    DigitsAt (cellsAhead (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
      (z, b.1)) b.1 w
  alike : ∀ l, l ≤ 24 → ∀ (z : ProofFile.InstPub) (a : S × (FrK D).E.Str) (tl : HTailF2)
      (L : LinkCtx),
    onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a →
    h.rchU (drawAt l) ((z, a.1), a.2) →
    a.1.failed = none → a.1.tl? = some tl → a.1.link? = some L →
    (∀ i, ∃ y ∈ P5J.At.ms Zp Z.lay,
      Alike y ⟨⟨lA (P5J.At.rad3At Zp Z.lay) a.1 tl L, sA (P5J.At.rad3At Zp Z.lay) a.1 tl L⟩, i⟩) ∧
      ∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        CellsIn (P5J.At.cs Zp) (lA (P5J.At.rad3At Zp Z.lay) a.1 tl L)
          (sA (P5J.At.rad3At Zp Z.lay) a.1 tl L) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l a.1 t o

/-- **REST GIVES CONDITION.** -/
theorem k08_cond_of_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (R : K8Rest h) : h.K8Cond 𝔏 := by
  obtain ⟨L₀, hL₀⟩ := R.laid
  refine ⟨R.door, R.planFits, R.gtSizes, R.ownSizes, n0At Zp, fun G l Xl q hG hl e3 hq => ?_⟩
  exact
    { piece := k08_piece_at_row h 𝔏 q₁ q₂ q₃ hG hl e3 hq
      blind := blind_of_test h 𝔏 q₁ q₂ q₃ hl (R.fence l hl) hq
      link := k8Link_tie h (R.link l hl)
      small := small_closed h hG hl e3 (fun _ _ u => u.1.1) hL₀ R.start R.sends
        (R.small G l Xl L₀ hG hl e3 hL₀)
      digits := R.digits G l Xl hG hl e3
      groupAt := rfl
      near := R.near G l Xl hG hl e3
      fold := k08_fold_field h hG hl e3 (fun _ _ u => u.1.1)
      alike := R.alike l hl }

/-- So it gives the kind's field of the table. -/
theorem k08_kind_of_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (R : K8Rest h) : h.Kind 𝔏 KindName.K8 :=
  P5J.k08_kind_all h 𝔏 q₁ q₂ q₃ (k08_cond_of_rest h 𝔏 q₁ q₂ q₃ R)

end P1K8T

#print axioms P1K8T.k08_cond_of_rest
#print axioms P1K8T.k08_kind_of_rest
