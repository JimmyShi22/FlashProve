-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesK13.lean: THE KIND K13's FIELD OF FirstOwed (OwesByKind.lean):
k13_five_at_baseMaker (AtFullSide/K13/FiveAt355AtBaseMaker.lean) CALLED at its one number. One theorem.

Limits. At the base maker's return, at the Script firstScriptAt (hQ). No other premise. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesKinds
import AtFullSide.K13.FiveAt355AtBaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (KindName)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker matrixInput)
open ProofFile.Honest.K1 (firstScriptAt LocB)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- **THE KIND K13's FIELD**, at the base maker's return. -/
theorem k13_paid_base {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A) (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop) :
    KindPaid (firstLetters h parts w) Said KindName.K13 := by
  obtain ⟨sc, numbers⟩ := parts
  obtain rfl : sc = _ := hQ
  exact k13_paid (AtFullSide.K13.k13_five_at_baseMaker hA h numbers w Said (fun _ _ _ => none))

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.k13_paid_base
