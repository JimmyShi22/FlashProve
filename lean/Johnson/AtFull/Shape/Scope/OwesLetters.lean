-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesLetters.lean: owes₁ AT THE NAMES OF AtFullSide/Honest/TheLettersFirst.lean: thread₁,
said₁, at first and numbers there. One theorem; a joining; nothing is evaluated.

Limits. RestOwed (what of the kinds is still owed) stays a premise by name, and live, a public test.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesGather
import AtFullSide.Honest.TheLettersFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Johnson.AtFull.Shape.Scope
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker)
open AtFullSide.Honest.TheLetters (numbers first thread₁ said₁)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **owes₁ AT THE LETTERS.** -/
theorem owes_at_letters (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (Rd : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (R : RestOwed h (numbers h) Rd.own (said₁ h Rd) Bs) :
    OwesS (thread₁ h Rd) (said₁ h Rd) :=
  owes_one_base made h (numbers h) Rd live hB R

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.owes_at_letters
