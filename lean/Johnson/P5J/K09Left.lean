-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09Left.lean: THE ONE LIST OF WHAT IS LEFT OF THE BATCHING KIND's CONDITION AT THE
CLOSED CONSTANT, BENEATH `AtMgA.K9Sorts` (K09Sorts.lean), when the payers that lie at the constant
are laid in: the shutting's side whole (`k9_shut_at`, K09Shut.lean), twelve fields of the core
(`coreRest2_at`, K09Core.lean) the head's spots (`headSpots_at`,
Johnson/LPFE1R/HeadSpotsConst.lean) and THE FACTS ALONG THE FOLD, WHOLE (
`atMgR_rch_of_head`, StartAtHead.lean: all 26 sentences on every reached state, from the head, which
stands with fourteen entry tests). A definition and theorems.

What is said.
  `AtMgA.K9Left h 𝔏`: at the laid list Ld that `At.laid? Zp` lists, at every link m < 25 there are
    letters that sit there, with p the plan's own, and: ONE CLOSED SENTENCE ON PUBLIC DATA: the
    link's plan fits (`linkPlanB`: a test with code); and, at the row's piece at the batching's
    number and at what `digAt` answers at the link: the link's sort is one of the three, and there
    are that sort's letters (N laid at the number of the fold's messages), and at every public part
    `LayersLeft`, `AttLeft` or `HeadLeft` (Johnson/Desc/First/Link/Law/SortLeft.lean): the sort's
    own fields (`LayersOwes`, `AttOwes`, `HeadOwes`, LinkRestAtSort4.lean) and what is
    left of the core (`CoreLeft`: 10 fields). `k9Sorts_of_left`: **`h.K9Sorts 𝔏` from it**, under
    the tower's own three equations on the flat lists' heads. `k09_kind_of_left`: **so `h.Kind 𝔏
    .K9`.**

Limits. BOOK-KEEPING. `K9Left` IS THE DEBT. NOTHING OF THE SHUTTING's PIECE IS LEFT IN IT. IN IT
STILL STAND: in `CoreLeft`: Anumbers, Aready, hitems, hAt, hLeft, hruns, inSeg, inRun, inTot, hmem;
each sort's own premises (its ties, the clauses on the lookup's entries, on which the kinds' laws on
their runs hang). WHETHER IT CAN BE MET IS NOT SAID: no member is known; Aready owes the sort's
named Ok AND the free sentence Kx; the closed sentence has no theorem that is joined here. The count
of fields is no measure. AT THE SECOND HASH FUNCTION ALONE. Nothing on soundness.

-/
import Johnson.P5J.K09Sorts
import Johnson.P5J.K09Core
import Johnson.P5J.K09Shut
import Johnson.LPFE1R.HeadSpotsConst
import Johnson.P5J.StartAtHead
import Johnson.P5J.K09FoldIs
import Johnson.Desc.First.Link.Law.SortLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Link claimsInBy)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf FoldFacts)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS Where)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.LinkJoin (batchAt atRec linkPlanB LayersLeft AttLeft
  HeadLeft layersRest3_of_left attRest3_of_left headRest3_of_left)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps
set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **WHAT IS LEFT.** -/
def AtMgA.K9Left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : Prop :=
  ∀ Ld, At.laid? Zp = some Ld →
  ∀ m < 25, ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ ∧ IM.k9At Zp m = some p ∧
    (∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true) ∧
    ∀ qb, (h.toAtMg.row 𝔏)[kAt m]? = some qb → ∀ xx tlD,
      VerifiableInference.Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD) →
      (subAt m = .layers ∧ ∃ (β : Type) (p4 : _) (Kx : _) (t3 : _) (l3 : _) (u : _) (ψ : S → β)
        (nU : _) (d : ℕ) (items : _) (run : _), ∀ z,
        LayersLeft (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m p4 Kx t3 l3 L u ψ nU p
          d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB)) items run xx tlD
          (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
          (At.foldD Zp cF Ld)) ∨
      (subAt m = .attention ∧ ∃ (β : Type) (rd : _) (c : _) (Kx : _) (t3 : _) (l3 : _) (u : _)
        (ψ : S → β) (nU : _) (d : ℕ) (items : _) (run : _), ∀ z,
        AttLeft (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m rd c Kx t3 l3 L u ψ nU
          p d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB)) items run xx tlD
          (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
          (At.foldD Zp cF Ld)) ∨
      (subAt m = .head ∧ ∃ (β : Type) (hS : _) (iU3 l' piece : ℕ) (p6 : _) (kap : _) (Kx : _)
        (t3 : _) (l3 : _) (u : _) (ψ : S → β) (nU : _) (d : ℕ) (items : _) (run : _), ∀ z,
        HeadLeft (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m hS iU3 l' piece p6 kap
          Kx t3 l3 L u ψ nU p d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB)) items
          run xx tlD
          (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
          (At.foldD Zp cF Ld))

/-- **THE SORTS' LISTS FROM WHAT IS LEFT.** -/
theorem k9Sorts_of_left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9Left 𝔏) : h.K9Sorts 𝔏 := by
  obtain ⟨Ld, R⟩ := atMgR_rch_of_head h
  have Fo := k9_fold_of_atMgR h Ld R
  refine ⟨Ld, Fo, fun m hm => ?_⟩
  obtain ⟨L, p, Q, b₃, b₅, St, kp, hP, G⟩ := H Ld R.listed m hm
  obtain ⟨xx, tlD, hdig, _⟩ := h.k9_dig m hm h.𝔇.l3.rad
  refine ⟨L, p, Q, b₃, b₅, St, kp, hP, headSpots_at h, fun qb qq qe hb _ _ => ?_,
    k9_shut_at h 𝔏 q₁ q₂ q₃ (kAt m + 4) b₅⟩
  rcases G qb hb xx tlD hdig with ⟨hs, β, p4, Kx, t3, l3, u, ψ, nU, d, items, run, K⟩ |
    ⟨hs, β, rd, c, Kx, t3, l3, u, ψ, nU, d, items, run, K⟩ |
    ⟨hs, β, hS, iU3, l', piece, p6, kap, Kx, t3, l3, u, ψ, nU, d, items, run, K⟩
  · exact Or.inl ⟨hs, β, p4, Kx, t3, l3, u, ψ, nU, d, _, items, run, xx, tlD, _, _, fun z =>
      layersRest3_of_left h.𝔇 fullLinks At.ps z _ (kAt m) m p4 Kx t3 l3 L u ψ nU p d _ _ items run
        xx tlD _ _ _ _
        (fun sh => coreRest2_at h 𝔏 q₁ q₂ q₃ Ld Fo m hm St kp sh qb hb xx tlD hdig _ u ψ _ nU _ _
          d items _ run z) (K z)⟩
  · exact Or.inr (Or.inl ⟨hs, β, rd, c, Kx, t3, l3, u, ψ, nU, d, _, items, run, xx, tlD, _, _,
      fun z => attRest3_of_left h.𝔇 fullLinks At.ps z _ (kAt m) m rd c Kx t3 l3 L u ψ nU p d _ _
        items run xx tlD _ _ _ _
        (fun sh => coreRest2_at h 𝔏 q₁ q₂ q₃ Ld Fo m hm St kp sh qb hb xx tlD hdig _ u ψ _ nU _ _
          d items _ run z) (K z)⟩)
  · exact Or.inr (Or.inr ⟨hs, β, hS, iU3, l', piece, p6, kap, Kx, t3, l3, u, ψ, nU, d, _, items,
      run, xx, tlD, _, _, fun z => headRest3_of_left h.𝔇 fullLinks At.ps z _ (kAt m) m hS iU3 l'
        piece p6 kap Kx t3 l3 L u ψ nU p d _ _ items run xx tlD _ _ _ _
        (fun sh => coreRest2_at h 𝔏 q₁ q₂ q₃ Ld Fo m hm St kp sh qb hb xx tlD hdig _ u ψ _ nU _ _
          d items _ run z) (K z)⟩)

/-- **SO THE FIELD.** -/
theorem k09_kind_of_left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9Left 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind_of_sorts h 𝔏 q₁ q₂ q₃ (k9Sorts_of_left h 𝔏 q₁ q₂ q₃ H)

end P5J

#print axioms P5J.k9Sorts_of_left
#print axioms P5J.k09_kind_of_left
