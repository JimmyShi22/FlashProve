-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesK7.lean: KindPaid at the kind K7, at the first thread of the maker's return at the base filling:
k7_five_at_base's plays and exchange through k7_paid.

  `k7_paid_base`    KindPaid, under that law's premises, htok among them
  `k7_paid_first`   the same at the Script firstScriptAt: htok is paid: the Script's token is the element's first coordinate

Limits. At the base filling, at Sz.ref, under the head; one kind of thirteen. Nothing on any property.
-/
import Johnson.AtFull.Shape.Scope.OwesHeadKinds
import AtFullSide.Honest.K7FiveAtBase
import AtFullSide.K1.FirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput)
open VerifiableInference.Desc (KindName)

variable {files : VerifierAndGoals.PublicFiles}

/-- **K7's place is paid.** -/
theorem k7_paid_base {pp : Inst.Model.ScalesAndPolicy} {R : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (hret : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok R)
    (head : HeadAtReturn files R) (parts : FirstThreadParts R) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins R.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf R.Z (ProofFile.pureSeat OnBytes.secondHashFunction R.Z) = .ok Bs)
    (htok : ∀ v : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells, (firstThread head parts w).valid v →
      parts.script.tok v = v.x.asked.c0.toNat) :
    KindPaid (firstLetters head parts w) Said KindName.K7 :=
  have F := ProofFile.Honest.Term.k7_five_at_base hS hR live hret head parts w Said hB htok (fun _ _ => True)
    (fun _ a => .ok a) (fun _ _ _ => none)
  k7_paid F.plays F.exchange

/-- **K7's place is paid, at the Script firstScriptAt.** -/
theorem k7_paid_first {pp : Inst.Model.ScalesAndPolicy} {R : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (hret : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok R)
    (head : HeadAtReturn files R) (parts : FirstThreadParts R)
    (hQ : parts.script =
      ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest R head.firstChain)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins R.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf R.Z (ProofFile.pureSeat OnBytes.secondHashFunction R.Z) = .ok Bs) :
    KindPaid (firstLetters head parts w) Said KindName.K7 :=
  k7_paid_base hS hR live hret head parts w Said hB fun v _ => by
    rw [hQ]
    rfl

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.k7_paid_base
#print axioms Johnson.AtFull.Shape.Scope.k7_paid_first
