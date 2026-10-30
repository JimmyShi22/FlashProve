-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesK4.lean: THE KIND K4's DEBT OF owesS_firstThread AT THE BASE PROVER's FIRST THREAD, BY KIND: kindFour_five_at_every_member_honest_at_the_threads_falls.

Limits. Every premise named here stays a premise. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesByKind
import Johnson.AtFull.Shape.Scope.OwesPlaces
import AtFullSide.K4.AllFiveAtTheBaseProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (KindName)
open ProofFile.Honest (OnlineProverWithDescription Coins Mid Local IndexCommitterCoins Cells)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers firstThread firstLetters)
open ProofFile.Honest.K1 (firstScriptAt)
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes.HonestTrace (Sz)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **K4_paid.** Conditional on the head and the base filling's return. -/
theorem K4_paid (head : HeadAtReturn files A)
    (made : ProofFile.Honest.onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (ProofFile.Honest.onlineProverPartsInUse matrixInput OnBytes.secondHashFunction Sz.ref ProofFile.Honest.openHonest) = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    KindPaid
      (firstLetters head
        ⟨firstScriptAt matrixInput Sz.ref ProofFile.Honest.openHonest A head.firstChain, numbers⟩ input)
      Said KindName.K4 := by
  intro b p hp hk
  obtain ⟨blk, hb, rfl⟩ := member_of_ps head.head hp
  exact paidAt_of_five (L := firstLetters head _ input) (AtFullSide.K4.kindFour_five_at_every_member_honest_at_the_threads_falls head
    made numbers input Said hb hk)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.K4_paid
