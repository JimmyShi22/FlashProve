-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/DoorFormAtTheTerm.lean: THE FORM AT THE SECOND CHAIN's FIRST BORDER, PAID OFF THE TWO
EARLIER THREADS. The two tests that door_form_at_term (DoorAtTheTerm.lean of this folder) asks are
said by first_door_saidS (AtFullSide/K14/FirstDoorAtEnd.lean) and shared_door_at_end
(AtFullSide/K14/SharedDoorAtEnd.lean).

  door_form_paid   the form, from what the letter ends names

What this is. A conditional lemma. It is none of the library's goals. It says nothing of soundness,
completeness or hiding.
-/
import AtFullSide.Honest.DoorAtTheTerm
import AtFullSide.K14.FirstDoorAtEnd
import AtFullSide.K14.SharedDoorAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  {Wt : Type} (shared : SharedThreadParts A Wt) (last : LastThreadParts A)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
  (x : ProofFile.Inst) (k : Coins A.B)

/-- **The form at the second chain's first border.** -/
theorem door_form_paid
    (hends : ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      last.ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((x.pub, e₁), e₂)) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      h.description.start₃ x.pub e₁ e₂ = .ok s₃ →
      (threadThree h first reads last R).Form 0 k s₃ (R.start₃ A.H m₁ m₂) :=
  door_form_at_term h first reads shared last R x k hends
    (fun e₁ m₁ E₁ e₂ _ _ s₃ u₁ _ hs =>
      AtFullSide.K14.first_door_saidS h.head A.H first.script _ _ _ _ _ _ _ _ _ _ _ k x.pub e₁ m₁ E₁
        e₂ s₃ u₁ hs)
    (fun _ _ _ _ _ _ _ _ u₂ _ =>
      AtFullSide.K14.shared_door_ordered A.Z h.places h.firstChain A.H _ _ _ _ _ _ _ _ _ _ _ _ _ _
        h.head (fun _ q => q) u₂.1)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.door_form_paid
