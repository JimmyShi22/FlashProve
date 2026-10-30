-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PieceLaid.lean: THE PIECE's FOUR FACTS AT WHAT THE VERIFIER's VALUE FOR THE PROOF FILE LAYS (proofDataAndDecisionOfPublicFiles, Johnson/Desc/Laid/ProofFull.lean): THERE THE PREMISES OF Johnson/Desc/Sound/PieceSeated.lean ON THE DESCRIPTION ARE PAID BY THE VALUE's OWN TESTS. Three theorems.

  planOk_parts: the tests on the plan hold: the three chains' blocks are in order (blocksOk), and the first chain ends in a seal.
  laid_premises: **proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r) → there is F with: onlineDescription o pol lay KL = .ok F · r = (F.pull instanceAsPlainRecord).run · F.data "proof file" = .ok D · F.sealLast · blocksOk of the three flat lists**: by laidPOf_ok (Johnson/Desc/Laid/ProofFullLaw.lean) and planOk_parts.
  laid_pieces: **SO AT THAT F AND D, at piecesAt … (restCap e₁) (restCap e₂) (restCap e₃) … at its three flat lists: PieceMore and the cap at every place of the first chain but the last and at every place of the two later chains; and each such piece's base is base₀ + the oracles that F's own blocks in front tell.** NO PREMISE ON THE
    DESCRIPTION IS LEFT (but the three lists' heads b :: l, which are free by the make of a chain's flat list).
WHAT IS LEFT FOR THE LAWS' "every tenant's tree lies below q.base": the two tests on the table's numbers (bookFit | fenceFit: seated_fenced): they are asked by no test of the value.

Limits. The full size's value. Nothing where the value refuses. No law of a block. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PieceSeated
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err)

/-- What the tests on the plan hold of the three chains' blocks and of the seal. -/
theorem planOk_parts {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    blocksOk F.first.blocksInOrder = true ∧ blocksOk F.shared.blocksInOrder = true ∧ blocksOk F.second.blocksInOrder = true ∧
      F.sealLast = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  tauto

/-- **What the value's yes pays of the pieces' premises.** -/
theorem laid_premises {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r}
    (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F, ProofFile.onlineDescription o pol lay KL = .ok F ∧ r = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      F.data "proof file" = .ok D ∧ F.sealLast = true ∧ blocksOk F.first.blocksInOrder = true ∧
      blocksOk F.shared.blocksInOrder = true ∧ blocksOk F.second.blocksInOrder = true := by
  obtain ⟨F, hF, hp, hD, _, hr⟩ := LPFD.Full.laidPOf_ok h
  obtain ⟨b₁, b₂, b₃, hs⟩ := planOk_parts F hp
  exact ⟨F, hF, hr, hD, hs, b₁, b₂, b₃⟩

/-- **The four facts at what the value lays: no premise on the description is left.** -/
theorem laid_pieces {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD} {r}
    (h : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F, ProofFile.onlineDescription o pol lay KL = .ok F ∧ r = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      ∀ (W : Type) (C : CK) (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
        (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl)),
        F.first.blocksInOrder = b₁ :: l₁ → F.shared.blocksInOrder = b₂ :: l₂ → F.second.blocksInOrder = b₃ :: l₃ →
        ∀ e₁ e₂ e₃ (d wEnd : W),
          (∀ k q, ((piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₁ ::
              (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₁)[k]? =
                some q → k + 1 < F.first.blocksInOrder.length →
            PieceMore (numAt D.t₁ D.t₂ 0) 0 (F.first.blocksInOrder.map held) k q ∧
              q.err = Err.cap 128 (uLT C q.ds) ∧ q.base = 0 + (oraclesOf (F.first.blocksInOrder.take k)).length) ∧
          (∀ k q, ((piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₂ ::
              (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₂)[k]? =
                some q →
            PieceMore (numAt D.t₁ D.t₂ 1) D.t₁ (F.shared.blocksInOrder.map held) k q ∧
              q.err = Err.cap 128 (uLT C q.ds) ∧
              q.base = D.t₁ + (oraclesOf (F.shared.blocksInOrder.take k)).length) ∧
          ∀ k q, ((piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).p₃ ::
              (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ (restCap e₁) (restCap e₂) (restCap e₃) d wEnd).l₃)[k]? =
                some q →
            PieceMore (numAt D.t₁ D.t₂ 2) (D.t₁ + D.t₂) (F.second.blocksInOrder.map held) k q ∧
              q.err = Err.cap 128 (uLT C q.ds) ∧
              q.base = D.t₁ + D.t₂ + (oraclesOf (F.second.blocksInOrder.take k)).length := by
  obtain ⟨F, hF, hr, hD, hs, k₁, k₂, k₃⟩ := laid_premises h
  refine ⟨F, hF, hr, fun W C b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃ e₁ e₂ e₃ d wEnd => ?_⟩
  obtain ⟨m₁, m₂, m₃⟩ := seated_more F "proof file" D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ q₁ q₂ q₃ e₁ e₂ e₃ d wEnd
  exact ⟨fun k q hq hk => ⟨(m₁ k q hq hk).1, (m₁ k q hq hk).2, seated_base (m₁ k q hq hk).1 k₁⟩,
    fun k q hq => ⟨(m₂ k q hq).1, (m₂ k q hq).2, seated_base (m₂ k q hq).1 k₂⟩,
    fun k q hq => ⟨(m₃ k q hq).1, (m₃ k q hq).2, seated_base (m₃ k q hq).1 k₃⟩⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.planOk_parts
#print axioms VerifiableInference.Desc.Sound.laid_premises
#print axioms VerifiableInference.Desc.Sound.laid_pieces
