-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/DoorYesAtTheTerm.lean: THE FIELD doorYes OF ThreadDebts AT THE THREE THREADS OF ONE
RUN: the second chain's start says yes, where the first chain's state has the run's shape.

  door_yes_at_term   doorYes_at_head (Johnson/AtFull/Shape/Scope/DoorStart.lean) at firstThread and
    sharedThread

What this is. A conditional lemma. It is none of the library's goals. It says nothing of soundness,
completeness or hiding.

Limits. hB, hX₀, hc, hcl are doorYes_at_head's: a base, the public data at the stored files, the run
on shapes to the first chain's last border and its test.
-/
import AtFullSide.Honest.DoorAtTheTerm
import Johnson.AtFull.Shape.Scope.DoorStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (h : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ IndexCommitterCoins)
  {Wt : Type} (shared : SharedThreadParts A Wt)
  (R : Ready W₀ IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
  (x : ProofFile.Inst) (k : Coins A.B)

/-- **The second chain's start says yes.** -/
theorem door_yes_at_term {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    {X₀ : OnBytes.Model.Verify.Public}
    (hX₀ : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {c : ShA} (hc : (shapeL (LWn X₀)).run 358 startShA = .ok c)
    (hcl : endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape c = true) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (threadOne h first R) (saidOne h first R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (threadTwo h reads shared R) (saidTwo h reads shared R)
        h.description.shared.blocksInOrder.length k e₂ m₂ E₂ →
      shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA
        h.description.first.blocksInOrder.length e₁ →
      ∃ s₃, h.description.start₃ (h.description.pub x) e₁ e₂ = .ok s₃ :=
  doorYes_at_head h.head hB hX₀ hc hcl A.H first.script _ _ _ _ _ _ _ _ _ _ x k rfl rfl
    (begun_at_term h reads shared R)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.door_yes_at_term
