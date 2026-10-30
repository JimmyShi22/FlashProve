-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/K7FiveAtBase.lean: `K7Five` at the first thread of the maker's return at the base filling,
before it is read through.

  `k7_five_at_base`   from scope, the gate, the return, its head, the base, and the script's token

This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import AtFullSide.Honest.K7AtTerm
import Johnson.Desc.ProofFile.Honest.K7.AtFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape
open P5J (TS)

variable {files : VerifierAndGoals.PublicFiles}

/-- **The member's four and its test on values at the base prover.** -/
theorem k7_five_at_base {pp : Inst.Model.ScalesAndPolicy} {R : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hS : VerifierAndGoals.InScope files = true) (hR : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (hret : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok R)
    (head : HeadAtReturn files R) (parts : FirstThreadParts R) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins R.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf R.Z (ProofFile.pureSeat OnBytes.secondHashFunction R.Z) = .ok Bs)
    (htok : ∀ v : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells, (firstThread head parts w).valid v →
      parts.script.tok v = v.x.asked.c0.toNat)
    (J : Nat → TS → Prop) (g : Nat → ShA → Except String ShA)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    K7Five (firstThread head parts w) Said J (firstZA g (Tab.vals R.Z Bs.G₀)) fall := by
  have hc := reply_closing_at_base hS hR hret live
  unfold ReplyClosed at hc
  exact k7_five_of_token head parts w Said hB hc.1 htok J g fall

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.k7_five_at_base
