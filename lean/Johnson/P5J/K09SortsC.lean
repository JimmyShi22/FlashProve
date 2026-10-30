-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09SortsC.lean: ON THE SECOND ROAD: BENEATH `AtMgA.K9RestC` (K09RestC.lean): THE SISTER
OF `AtMgA.K9Sorts` (K09Sorts.lean, which does not turn): the law's letters chosen by the link's
sort: at a link's three pieces `LinkRestC` gives way to `LayersRest3C`, `AttRest3C` or
`HeadRest3C` (Johnson/Desc/First/Link/Law/LinkRestAtSort3C.lean). The elder file's text with the
names turned. A definition and theorems.

What is said.
  `AtMgA.K9SortsC h 𝔏`: as `K9Sorts`, with these. Among the letters: Kx, a free sentence on the
    snapshot: the law's Ok is «the sort's named Ok AND Kx». `k9RestC_of_sorts`: **`h.K9RestC 𝔏`
    from it.** `k09_kind_of_sortsC`: **so `h.Kind 𝔏 .K9`**, under the tower's own three equations
    on the flat lists' heads.

Limits. BOOK-KEEPING. `K9SortsC` IS THE DEBT; no member is known. On this road the runs' debts stand
once, at the bare promise «the sort's named Ok and Kx»; «the runs' claims are at most the plan's
number» is no part of Kx. The count of fields is no measure. AT THE SECOND HASH FUNCTION ALONE.
Nothing on soundness.

-/
import Johnson.P5J.K09RestC
import Johnson.Desc.First.Link.Law.LinkRestAtSort3C

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
open VerifiableInference.Desc.LinkJoin (batchAt atRec ShutRest linkPlanB HeadSpots LayersRest3C
  AttRest3C HeadRest3C linkRestC_layers3 linkRestC_att3 linkRestC_head3)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps
set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **WHAT IS LEFT, THE LETTERS CHOSEN BY THE LINK's SORT.** -/
def AtMgA.K9SortsC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : Prop :=
  ∃ Ld, FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps ∧
  ∀ m < 25, ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ ∧ IM.k9At Zp m = some p ∧
    (∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true) ∧ (∃ nH, HeadSpots Zp nH) ∧
    (∀ qb qq qe, (h.toAtMg.row 𝔏)[kAt m]? = some qb →
      (h.toAtMg.row 𝔏)[kAt m + 1]? = some qq → (h.toAtMg.row 𝔏)[kAt m + 1 + 1]? = some qe →
      (subAt m = .layers ∧ ∃ (β : Type) (p4 : _) (Kx : _) (t3 : _) (l3 : _) (u : _) (ψ : S → β)
        (nU : _) (d N : ℕ) (items : _) (run : _) (xx : _) (tlD : _) (set : _) (pp : ℕ), ∀ z,
        LayersRest3C (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m p4 Kx t3 l3 L u ψ nU p
          d N (atRec qb (below L.batchB)) items run xx tlD set pp
          (fun j => h.𝔇.l3.seat xx.link true j.1) (At.foldD Zp cF Ld)) ∨
      (subAt m = .attention ∧ ∃ (β : Type) (rd : _) (c : _) (Kx : _) (t3 : _) (l3 : _) (u : _)
        (ψ : S → β) (nU : _) (d N : ℕ) (items : _) (run : _) (xx : _) (tlD : _) (set : _)
        (pp : ℕ), ∀ z,
        AttRest3C (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m rd c Kx t3 l3 L u ψ nU
          p d N (atRec qb (below L.batchB)) items run xx tlD set pp
          (fun j => h.𝔇.l3.seat xx.link true j.1) (At.foldD Zp cF Ld)) ∨
      (subAt m = .head ∧ ∃ (β : Type) (hS : _) (iU3 l' piece : ℕ) (p6 : _) (kap : _) (Kx : _)
        (t3 : _) (l3 : _) (u : _) (ψ : S → β) (nU : _) (d N : ℕ) (items : _) (run : _) (xx : _)
        (tlD : _) (set : _) (pp : ℕ), ∀ z,
        HeadRest3C (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m hS iU3 l' piece p6 kap
          Kx t3 l3 L u ψ nU p d N (atRec qb (below L.batchB)) items run xx tlD set pp
          (fun j => h.𝔇.l3.seat xx.link true j.1) (At.foldD Zp cF Ld))) ∧
    ∀ qs, (h.toAtMg.row 𝔏)[kAt m + 4]? = some qs → ∃ Zc layF Dw,
      (∃ o pol lay KL, ProofFile.pureRoad.pub o pol lay KL = .ok Zc) ∧
      (ProofFile.pAtK2 Zc 24).stands ≠ .head ∧
      ShutRest (F := FrK) h.𝔇 (atRec qs (below b₅)) Zc layF Dw

/-- **THE REST FROM THE SORTS.** -/
theorem k9RestC_of_sorts (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (H : h.K9SortsC 𝔏) : h.K9RestC 𝔏 := by
  obtain ⟨Ld, Fo, H⟩ := H
  refine ⟨Ld, Fo, fun m hm => ?_⟩
  obtain ⟨L, p, Q, b₃, b₅, St, kp, hP, hH, G, G5⟩ := H m hm
  refine ⟨L, p, Q, b₃, b₅, St, kp, hP, hH, fun qb qq qe hb hq he => ?_, G5⟩
  rcases G qb qq qe hb hq he with ⟨hs, β, p4, Kx, t3, l3, u, ψ, nU, d, N, items, run, xx, tlD, set,
      pp, K⟩ | ⟨hs, β, rd, c, Kx, t3, l3, u, ψ, nU, d, N, items, run, xx, tlD, set, pp, K⟩ |
    ⟨hs, β, hS, iU3, l', piece, p6, kap, Kx, t3, l3, u, ψ, nU, d, N, items, run, xx, tlD, set, pp,
      K⟩
  · rw [hs]
    exact ⟨_, _, _, _, _, _, d, N, items, u, _, _, run, xx, tlD, set, pp, fun z =>
      linkRestC_layers3 h.𝔇 fullLinks At.ps z _ (kAt m) m p4 Kx t3 l3 L u ψ nU p d N _ items run xx
        tlD set pp _ _ p b₃ _ _ 0 _ _ _ (K z)⟩
  · rw [hs]
    exact ⟨_, _, _, _, _, _, d, N, items, u, _, _, run, xx, tlD, set, pp, fun z =>
      linkRestC_att3 h.𝔇 fullLinks At.ps z _ (kAt m) m rd c Kx t3 l3 L u ψ nU p d N _ items run xx
        tlD set pp _ _ p b₃ _ _ 0 _ _ _ (K z)⟩
  · rw [hs]
    exact ⟨_, _, _, _, _, _, d, N, items, u, _, _, run, xx, tlD, set, pp, fun z =>
      linkRestC_head3 h.𝔇 fullLinks At.ps z _ (kAt m) m hS iU3 l' piece p6 kap Kx t3 l3 L u ψ nU p
        d N _ items run xx tlD set pp _ _ p b₃ _ _ 0 _ _ _ (K z)⟩

/-- **SO THE FIELD.** -/
theorem k09_kind_of_sortsC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9SortsC 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind_of_restC h 𝔏 q₁ q₂ q₃ (k9RestC_of_sorts h 𝔏 H)

end P5J

#print axioms P5J.k9RestC_of_sorts
#print axioms P5J.k09_kind_of_sortsC
