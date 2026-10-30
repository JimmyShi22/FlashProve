-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/OpenSharedFilled.lean: a value of the object's letter open₂.

  open₂_filled         OpenShared A, its one field rest at zeros

Why a constant serves. The laws at the shared chain are general in rest: five_term_laid, five_letters_nine,
five_letters_ten, owes₂_filled, yes₂_filled hold at every value of it. So this value says nothing of what
the prover knows: a law that reads the witness behind K14's messages needs another value, and none here
stands for it.

Limits. A value of a letter: nothing is shown of it. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.Honest.TheLettersShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread

/-- **The letter open₂, at zeros.** -/
def open₂_filled (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) : TheLetters.OpenShared A :=
  ⟨fun _ _ _ => (⟨fun _ _ => 0, 0, fun _ _ _ _ => 0, fun _ _ _ _ _ => 0⟩, fun _ _ _ => 0)⟩

end AtFullSide.Honest

#print axioms AtFullSide.Honest.open₂_filled
