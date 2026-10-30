-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3Fenced.lean: the kind "lookup" (K3): EVERY SAMPLED TENANT OF A PIN THAT IS
OPEN IN FRONT OF A LOOKUP SITS BELOW ITS PIECE's BASE: at the pieces that the proof file's rule
takes, at all fifty places.

Main name:
  `k03_fenced`: at each of the fifty pieces q of the first chain's row: every tenant x of a pin
    that is open in front of it, with an OOD sample, sits in a tree below the piece's first:
    x.1 < q.base.

What it pays: the premise hseat of the kind's four laws ("(seatT i).1 < q.base") and the premise
"t.1 < p.base" of Johnson/Desc/Sound/MgAt/K3Sig.lean, wherever the seat is among the sampled tenants
at that border (the fields seats | hSeat; Johnson/Desc/Sound/MgAt/K3Pins.lean brings N.sent there).

A joining: `fenced_at` (Johnson/Desc/Sound/PieceFence.lean) at `seated_more`
(Johnson/Desc/Sound/PieceSeated.lean), with "the lookup's sub-protocol is not the flat list's last"
(`hear_not_last`) and "the place stands in the written list" (`k03_at_full`).

Limits: three tests are premises: the sub-protocols' declared roots fit what they tell (blocksOk);
the table's numbers fit the told trees (bookFit); the fence (fenceFit). By a register of
the composed meaning's letters, a text of this project that is not in this repository (its line on
N), the last two have run true at both sizes: those runs were not seen for this file; none is a
theorem here. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3PiecesSeated
import Johnson.Desc.Sound.PieceFence

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers bookFit fenceFit sampledIn openSets start flatPlacesOf)

/-- **The fence at the kind's fifty pieces.** -/
theorem k03_fenced {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Desc.Block Desc.First.S ProofFile.Cl)} {c : Desc.Chain Desc.First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B)
    {Cells Tok : Type} (file : String) (D : WholeD)
    (hD : (pureDesc Z A B c).data file = .ok D) (hs : (pureDesc Z A B c).sealLast = true)
    (b₁ : Desc.Block (pureDesc Z A B c).S₁ (pureDesc Z A B c).Cl)
    (l₁ : List (Desc.Block (pureDesc Z A B c).S₁ (pureDesc Z A B c).Cl))
    (b₂ : Desc.Block (pureDesc Z A B c).S₂ (pureDesc Z A B c).Cl)
    (l₂ : List (Desc.Block (pureDesc Z A B c).S₂ (pureDesc Z A B c).Cl))
    (b₃ : Desc.Block (pureDesc Z A B c).S₃ (pureDesc Z A B c).Cl)
    (l₃ : List (Desc.Block (pureDesc Z A B c).S₃ (pureDesc Z A B c).Cl))
    (q₁ : (pureDesc Z A B c).first.blocksInOrder = b₁ :: l₁)
    (q₂ : (pureDesc Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (pureDesc Z A B c).second.blocksInOrder = b₃ :: l₃)
    (e₁ : (i : ℕ) → (ds : List RDT) →
      ((pureDesc Z A B c).XiPub × (pureDesc Z A B c).S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → Desc.Wit Cells Tok MsgT → Desc.Wit Cells Tok MsgT)
    (e₂ : (i : ℕ) → (ds : List RDT) →
      (((pureDesc Z A B c).XiPub × (pureDesc Z A B c).S₁) × (pureDesc Z A B c).S₂) ×
        (frameAt D (allOf D) D.key₂ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → Desc.Wit Cells Tok MsgT → Desc.Wit Cells Tok MsgT)
    (e₃ : (i : ℕ) → (ds : List RDT) →
      (((pureDesc Z A B c).XiPub × (pureDesc Z A B c).S₁ × (pureDesc Z A B c).S₂) ×
        (pureDesc Z A B c).S₃) ×
        (frameAt D (allOf D) D.key₃ (pureDesc Z A B c).lastChainFirstTreeNumber).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → Desc.Wit Cells Tok MsgT → Desc.Wit Cells Tok MsgT)
    (d wEnd : Desc.Wit Cells Tok MsgT) (N : Numbers)
    (hb : Desc.blocksOk ((pureDesc Z A B c).first.blocksInOrder.map
      (held (P := (pureDesc Z A B c).XiPub))) = true)
    (hf : bookFit N (flatPlacesOf linksFull true)
      (toldOf ((pureDesc Z A B c).first.blocksInOrder.map (held (P := (pureDesc Z A B c).XiPub)))) = true)
    (hg : fenceFit N linksFull (flatPlacesOf linksFull true) = true) :
    ∀ l, l < 25 → ∀ (dd : Bool) q,
      ((piecesAt (ckP .two) (pureDesc Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂)
          (restCap e₃) d wEnd).p₁ ::
        (piecesAt (ckP .two) (pureDesc Z A B c) D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂)
          (restCap e₃) d wEnd).l₁)[14 * l + IM.k3Ix l dd + 2]? = some q →
      ∀ x ∈ sampledIn N ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[14 * l + IM.k3Ix l dd + 2]?.getD []), x.1 < q.base := by
  intro l hl dd q hq
  obtain ⟨Lk, b, b', h1, h2, -, -⟩ := IM.k3_of hS hR O l hl dd
  have hn := hear_not_last h1 h2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix l dd)] at hn
  have x := (seated_more (pureDesc Z A B c) file D hD hs (ckP .two) b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃ e₁
    e₂ e₃ d wEnd).1 _ q hq hn
  exact fenced_at x.1 hb N linksFull _ hf hg
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 (K3Lot.k03_at_full l hl dd)).1)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k03_fenced
