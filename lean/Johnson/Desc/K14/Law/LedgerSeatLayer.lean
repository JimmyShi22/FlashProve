-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSeatLayer.lean: THE SEAT's LAYER: at the value that the field
RowsTiedR.shared_joint_count names as its list of pieces, T := atDesc F (piecesAt C F D c₁ k₁ c₂ k₂
c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd), SIX OF THE PREMISES "OF THE MAKE" OF THE
LEDGER's TOP AT
THE MAKER's CUT (Johnson/Desc/K14/Law/LedgerByMakeTop.lean: g₁ · g₂ · g₃ · hcut · hcp · hrow) ARE
FACTS, at
every description F. No kind's law, no chance.
  seat_layer   F.first.blocksInOrder = c₁ :: k₁ · F.shared.blocksInOrder = c₂ :: k₂ · F.second.blocksInOrder = c₃ :: k₃ ⊢
               (g₁ g₂ g₃) the held blocks declare F's rounds · (hcut) T is the maker's cut at the
               held
               blocks, at restCap e₁ | e₂ | e₃ and the sealing round · (hcp) AtCap (restCap e₂) ·
               (hrow) the held blocks of the shared row are F.shared.blocksInOrder, below and lifted
OBJECT   the field's own list of pieces
USER     the ledger's top at the field (not called here)
What is not claimed. That F.shared is the seated chain: at the seated description it is so by its
text. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerRowOfCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared

theorem seat_layer {Xi W : Type} (F : FileDescription Xi) (D : WholeD) (C : CK) (c₁ : Block F.S₁ F.Cl)
    (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl) (k₂ : List (Block F.S₂ F.Cl))
    (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl)) (h₁ : F.first.blocksInOrder = c₁ :: k₁)
    (h₂ : F.shared.blocksInOrder = c₂ :: k₂) (h₃ : F.second.blocksInOrder = c₃ :: k₃)
    (e₁ : (i : ℕ) → (ds : List RDT) → (F.XiPub × F.S₁) × (frameAt D (allOf D) D.key₁ 0).E.Str →
      Iop.Tr (uLT C ds) → W → W)
    (e₂ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁) × F.S₂) ×
      (frameAt D (allOf D) D.key₂ 0).E.Str → Iop.Tr (uLT C ds) → W → W)
    (e₃ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) ×
      (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber).E.Str → Iop.Tr (uLT C ds) → W → W)
    (dW wEnd : W) :
    ((held c₁ :: k₁.map held : List (Block (F.XiPub × F.S₁) F.Cl)).map (·.rounds) =
        F.first.blocksInOrder.map (·.rounds)) ∧
      ((held c₂ :: k₂.map held : List (Block ((F.XiPub × F.S₁) × F.S₂) F.Cl)).map (·.rounds) =
        F.shared.blocksInOrder.map (·.rounds)) ∧
      ((held c₃ :: k₃.map held : List (Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl)).map
        (·.rounds) = F.second.blocksInOrder.map (·.rounds)) ∧
      (atDesc F (piecesAt C F D c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW
          wEnd)).IsCut
        (held c₁) (k₁.map held) (held c₂) (k₂.map held) (held c₃) (k₃.map held) (restCap e₁)
        (restCap e₂) (restCap e₃) sealRound ∧
      AtCap (restCap e₂) ∧
      (held c₂ :: k₂.map held : List (Block ((F.XiPub × F.S₁) × F.S₂) F.Cl)) =
        (F.shared.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) := by
  refine ⟨?_, ?_, ?_, ⟨rfl, rfl, rfl⟩, atCap_restCap e₂, ?_⟩
  · rw [h₁]; exact held_map_rounds (c₁ :: k₁)
  · rw [h₂]; exact held_map_rounds (c₂ :: k₂)
  · rw [h₃]; exact held_map_rounds (c₃ :: k₃)
  · rw [h₂, ← held_map]
    rfl

end Desc.K14.Law
