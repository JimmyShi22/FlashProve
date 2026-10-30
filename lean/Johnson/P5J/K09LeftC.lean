-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09LeftC.lean: ON THE SECOND ROAD: THE ONE LIST OF WHAT IS LEFT OF THE BATCHING KIND's
CONDITION AT THE CLOSED CONSTANT, BENEATH `AtMgA.K9SortsC` (K09SortsC.lean): THE SISTER OF
`AtMgA.K9Left` (K09Left.lean, which does not turn), when the payers that lie at the constant are
laid in: the shutting's side whole (`k9_shut_at`, K09Shut.lean); fifteen fields of the core
(`coreRest2C_at`, K09CoreC.lean); the head's spots (`headSpots_at`,
Johnson/LPFE1R/HeadSpotsConst.lean); the facts along the fold, whole (`atMgR_rch_of_head`,
StartAtHead.lean); a run at the smallness test's equations (`hAt_layers_mg` and its like,
Johnson/LPFK9R/SortRunAtMg.lean). Where a payer is «from the head»: from all the fields of
`AtMgA`, not from the entry tests alone. A definition and theorems.

What is said.
  `AtMgA.K9LeftC h 𝔏`: at the laid list Ld that `At.laid? Zp` lists, at every link m < 25 there are
    letters that sit there, with p the plan's own, and: ONE CLOSED SENTENCE ON PUBLIC DATA: the
    link's plan fits (`linkPlanB`: a test with code); and, at the row's piece at the batching's
    number and at what `digAt` answers at the link: the link's sort is one of the three, and AT
    EVERY RUN THAT STANDS AT THE SMALLNESS TEST's EQUATIONS there are that sort's letters (N, items,
    set, pp are laid), and at every public part `LayersLeftC`, `AttLeftC` or `HeadLeftC`
    (Johnson/Desc/First/Link/Law/SortLeftC.lean): the sort's own fields
    (`LayersOwesC`, `AttOwesC`, `HeadOwesC`) and what is left of the core (`CoreLeftC`: 7 fields).
    `k9SortsC_of_left`: **`h.K9SortsC 𝔏` from it**, under the tower's own three equations on the
    flat lists' heads. `k09_kind_of_leftC`: **so `h.Kind 𝔏 .K9`.**

Limits. BOOK-KEEPING. `K9LeftC` IS THE DEBT. IN IT STILL STAND: in `CoreLeftC`: Anumbers, AreadyS,
hitems, hLeft, inSeg, inRun, inTot; each sort's own premises (its ties, the clauses on the lookup's
entries at the bare promise, that the lookup's runs keep the map). «The runs' claims are at most the
plan's number» IS NOWHERE IN IT: on this road it is drawn from the batching piece's own yes. WHETHER
IT CAN BE MET IS NOT SAID: no member is known; AreadyS owes the sort's named Ok AND the free
sentence Kx; the closed sentence has no theorem that is joined here. The count of fields is no
measure. AT THE SECOND HASH FUNCTION ALONE. Nothing on soundness.

-/
import Johnson.P5J.K09SortsC
import Johnson.P5J.K09CoreC
import Johnson.LPFK9R.SortRunAtMg
import Johnson.P5J.K09Shut
import Johnson.LPFE1R.HeadSpotsConst
import Johnson.P5J.StartAtHead
import Johnson.P5J.K09FoldIs
import Johnson.Desc.First.Link.Law.SortLeftC

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
open VerifiableInference.Desc.LinkJoin (batchAt atRec linkPlanB sortItems LayersLeftC AttLeftC
  HeadLeftC layersRest3C_of_left attRest3C_of_left headRest3C_of_left)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps
set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **WHAT IS LEFT.** -/
def AtMgA.K9LeftC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : Prop :=
  ∀ Ld, At.laid? Zp = some Ld →
  ∀ m < 25, ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ ∧ IM.k9At Zp m = some p ∧
    (∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true) ∧
    ∀ qb, (h.toAtMg.row 𝔏)[kAt m]? = some qb → ∀ xx tlD,
      VerifiableInference.Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD) →
      (subAt m = .layers ∧ ∀ run, VerifiableInference.Desc.LinkJoin.At L (4, "K8.equations") run →
        ∃ (β : Type) (p4 : _) (Kx : _) (t3 : _) (l3 : _) (u : _) (ψ : S → β) (nU : _) (d : ℕ), ∀ z,
        LayersLeftC (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m p4 Kx t3 l3 L u ψ nU p
          d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB)) (sortItems .layers) run xx tlD
          (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
          (At.foldD Zp cF Ld)) ∨
      (subAt m = .attention ∧
        ∀ run, VerifiableInference.Desc.LinkJoin.At L (4, "K8.equations") run →
        ∃ (β : Type) (rd : _) (c : _) (Kx : _) (t3 : _) (l3 : _) (u : _) (ψ : S → β) (nU : _)
        (d : ℕ), ∀ z,
        AttLeftC (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m rd c Kx t3 l3 L u ψ nU
          p d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB)) (sortItems .attention) run
          xx tlD
          (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
          (At.foldD Zp cF Ld)) ∨
      (subAt m = .head ∧ ∀ run, VerifiableInference.Desc.LinkJoin.At L (5, "K8.equations") run →
        ∃ (β : Type) (hS : _) (iU3 l' piece : ℕ) (p6 : _) (kap : _) (Kx : _) (t3 : _) (l3 : _)
        (u : _) (ψ : S → β) (nU : _) (d : ℕ), ∀ z,
        HeadLeftC (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m hS iU3 l' piece p6 kap
          Kx t3 l3 L u ψ nU p d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB))
          (sortItems .head) run xx tlD
          (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
          (At.foldD Zp cF Ld))

/-- **THE SORTS' LISTS FROM WHAT IS LEFT.** -/
theorem k9SortsC_of_left (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9LeftC 𝔏) : h.K9SortsC 𝔏 := by
  obtain ⟨Ld, R⟩ := atMgR_rch_of_head h
  have Fo := k9_fold_of_atMgR h Ld R
  refine ⟨Ld, Fo, fun m hm => ?_⟩
  obtain ⟨L, p, Q, b₃, b₅, St, kp, hP, G⟩ := H Ld R.listed m hm
  obtain ⟨xx, tlD, hdig, _⟩ := h.k9_dig m hm h.𝔇.l3.rad
  refine ⟨L, p, Q, b₃, b₅, St, kp, hP, headSpots_at h, fun qb qq qe hb _ _ => ?_,
    k9_shut_at h 𝔏 q₁ q₂ q₃ (kAt m + 4) b₅⟩
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  rcases G qb hb xx tlD hdig with ⟨hs, G1⟩ | ⟨hs, G1⟩ | ⟨hs, G1⟩
  · obtain ⟨run, hAt⟩ := LPFK9.hAt_layers_mg h O m hm hs L St.lk
    obtain ⟨β, p4, Kx, t3, l3, u, ψ, nU, d, K⟩ := G1 run hAt
    exact Or.inl ⟨hs, β, p4, Kx, t3, l3, u, ψ, nU, d, _, _, run, xx, tlD, _, _, fun z =>
      layersRest3C_of_left h.𝔇 fullLinks At.ps z _ (kAt m) m p4 Kx t3 l3 L u ψ nU p d _ _ _ run xx
        tlD _ _ _ _
        (fun sh => coreRest2C_at h 𝔏 q₁ q₂ q₃ Ld R.listed Fo m hm St kp sh qb hb xx tlD hdig _
          (hs ▸ St.sort) u ψ _ nU _ _ d _ run hAt z) (K z)⟩
  · obtain ⟨run, hAt⟩ := LPFK9.hAt_att_mg h O m hm hs L St.lk
    obtain ⟨β, rd, c, Kx, t3, l3, u, ψ, nU, d, K⟩ := G1 run hAt
    exact Or.inr (Or.inl ⟨hs, β, rd, c, Kx, t3, l3, u, ψ, nU, d, _, _, run, xx, tlD, _, _, fun z =>
      attRest3C_of_left h.𝔇 fullLinks At.ps z _ (kAt m) m rd c Kx t3 l3 L u ψ nU p d _ _ _ run xx
        tlD _ _ _ _
        (fun sh => coreRest2C_at h 𝔏 q₁ q₂ q₃ Ld R.listed Fo m hm St kp sh qb hb xx tlD hdig _
          (hs ▸ St.sort) u ψ _ nU _ _ d _ run hAt z) (K z)⟩)
  · obtain ⟨run, hAt⟩ := LPFK9.hAt_head_mg h O m hm hs L St.lk
    obtain ⟨β, hS, iU3, l', piece, p6, kap, Kx, t3, l3, u, ψ, nU, d, K⟩ := G1 run hAt
    exact Or.inr (Or.inr ⟨hs, β, hS, iU3, l', piece, p6, kap, Kx, t3, l3, u, ψ, nU, d, _, _, run,
      xx, tlD, _, _, fun z => headRest3C_of_left h.𝔇 fullLinks At.ps z _ (kAt m) m hS iU3 l' piece
        p6 kap Kx t3 l3 L u ψ nU p d _ _ _ run xx tlD _ _ _ _
        (fun sh => coreRest2C_at h 𝔏 q₁ q₂ q₃ Ld R.listed Fo m hm St kp sh qb hb xx tlD hdig _
          (hs ▸ St.sort) u ψ _ nU _ _ d _ run hAt z) (K z)⟩)

/-- **SO THE FIELD.** -/
theorem k09_kind_of_leftC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9LeftC 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind_of_sortsC h 𝔏 q₁ q₂ q₃ (k9SortsC_of_left h 𝔏 q₁ q₂ q₃ H)

end P5J

#print axioms P5J.k9SortsC_of_left
#print axioms P5J.k09_kind_of_leftC
