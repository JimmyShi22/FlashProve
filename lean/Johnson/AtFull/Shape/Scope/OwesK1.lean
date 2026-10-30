-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesK1.lean: THE KIND K1's FIELD OF FirstOwed (OwesByKind.lean). A joining.

  k1_paid        KindPaid at K1: playsS_k1_base and k1_exchange_at_base, with tie_baseMaker, hWrow_first
                 and k13_pileOneS_at_356 for their three shares

Limits. hA, h, hQ, hSaid are those laws' own. No run on shapes is asked: the step's acceptance is not
said here. At the base maker alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesKinds
import AtFullSide.K1.FiveAtBaseMakerPaid
import AtFullSide.K1.ExchangeAtBase
import AtFullSide.K1.PlaysAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (KindName)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker matrixInput)
open ProofFile.Honest.K1 (firstScriptAt LocB tie_baseMaker hWrow_first pile_open_honest playsS_k1_base
  k1_number_of_kind k1_exchange_at_base othersApart_first)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- **THE KIND K1's FIELD**, at the base maker's return, at the Script firstScriptAt. The sender plays
and the row's items hold behind the step at each of the 52 numbers; no run on shapes is asked. -/
theorem k1_paid {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    KindPaid (firstLetters h parts w) Said KindName.K1 := by
  have hTie := tie_baseMaker hA h parts hQ w Said hSaid
  have hWrow := hWrow_first hA h parts hQ w pile_open_honest Said
  obtain ⟨script, numbers⟩ := parts
  dsimp only at hQ
  subst hQ
  have hPile := ProofFile.Honest.K13.k13_pileOneS_at_356 h.head A.H
    (firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain)
    (fallsAfterBatching (firstFalls A numbers) h.firstChain)
    (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁
    h.description.t₂ 339 (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w Said
  have hPl := playsS_k1_base h.head hA
    (fallsAfterBatching (firstFalls A numbers) h.firstChain)
    (VerifiableInference.Desc.K2.Honest.carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁
    h.description.t₂ 339 (ReadyInput h.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses h)) w Said
  intro b p hp hk
  refine ⟨fun _ => ?_, fun _ j hj ho => ?_⟩
  · rcases k1_number_of_kind hp hk with rfl | ⟨l, hl, d, rfl⟩ | rfl
    · exact hPl.1
    · exact hPl.2.1 l hl d
    · exact hPl.2.2
  · exact k1_exchange_at_base h.head hA _ _ _ (othersApart_first h.head hA) _ _ _ _ _ _ _ _ _ w Said
      hSaid hTie hPile hWrow b p hp hk j hj ho

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.k1_paid
