-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesK9.lean: THE KIND K9's FIELD OF FirstOwed (OwesByKind.lean): four_at_k9_first
(Honest/K9/FourAtFirst.lean) CALLED. One theorem.

Limits. hA (the maker's return at the wider filling), h (the head at it) and hSaid are those of
four_at_k9_first. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesKinds
import Johnson.Desc.ProofFile.Honest.K9.FourAtFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (KindName)
open ProofFile.Honest ProofFile.Honest.FirstThread

/-- **THE KIND K9's FIELD.** -/
theorem k9_paid {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument)
    (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {o' : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (Said : ℕ → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    KindPaid (firstLetters h parts w) Said KindName.K9 :=
  kindPaid_of_exchange fun _ _ hp hk =>
    have f := ProofFile.Honest.K9.four_at_k9_first I o Sz O hA h parts w Said hSaid hp hk
    ⟨f.1, f.2.2.1⟩

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.k9_paid
