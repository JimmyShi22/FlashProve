-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesK5.lean: THE KIND K5's DEBT OF owesS_firstThread AT THE FIRST THREAD OF THE BASE MAKER, BY KIND: kindFive_five_at_every_member_honest, at every number of that kind in the written list.

Limits. Every premise named here stays a premise. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesByKind
import Johnson.AtFull.Shape.Scope.OwesPlaces
import Johnson.Desc.ProofFile.Honest.K5.Law.FiveAtFirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (KindName)
open ProofFile.Honest (OnlineProverWithDescription Coins Mid Local IndexCommitterCoins Cells)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers firstThread firstLetters)
open ProofFile.Honest.Term (baseMaker matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes.HonestTrace (Sz)
open P5J (TS)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **K5_paid.** Conditional on the head and the maker's return. -/
theorem K5_paid (head : HeadAtReturn files A) (made : baseMaker files = .ok A)
    (numbers : FallNumbers) (input : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) :
    KindPaid
      (firstLetters head
        ⟨ProofFile.Honest.K1.firstScriptAt matrixInput Sz.ref ProofFile.Honest.openHonest A head.firstChain,
          numbers⟩ input)
      Said KindName.K5 := by
  intro b p hp hk
  obtain ⟨blk, hb, rfl⟩ := member_of_ps head.head hp
  exact paidAt_of_five (L := firstLetters head _ input) (ProofFile.Honest.K5.kindFive_five_at_every_member_honest head made numbers input
    Said (fun _ _ _ => none) hb hk)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.K5_paid
