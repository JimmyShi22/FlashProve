-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/InstanceEight.lean: the members 1 to 8 of the shared chain at laterBase: the hash
build's five_at_sharedParts with its layings paid.

  five_border_eight       FiveAtBorder at a member 1 to 8, at the committer's made input.

late stays a premise: every rider begins at 10 or later. The witness's first component and the
keeps away from 9, 10 stay letters.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head). The
ground: each of the five starts from ThrS, a premise on the letters left (rest, Kp₁, Said, w), which
may read the coins; no lemma here shows it at every value of the coins: there the bar is flat.
The input is the made term xiAt at a letter sd beside the coins. Nothing on completeness, on
soundness or on what is hidden.
-/
import AtFullSide.K12.InstanceLater
import AtFullSide.K14.AtLaterThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)
open ProofFile.Honest.K14 (randNow)
open ProofFile.Honest.FirstThread

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **FiveAtBorder at a member 1 to 8, at laterBase.** -/
theorem five_border_eight (h : HeadAtReturn files A)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (bs : List (Block St Unit)) (pO : P12)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (riders : List (RiderCl (Common FullSizeMatrix IndexCommitterCoins TableKey) St)) (Kp₁ : Place → St → St → Prop)
    (late : ∀ c ∈ riders, 10 ≤ c.lo) (w₀ : FullSizeMatrix) (rc : IndexCommitterCoins)
    (sd : Bind.ForProver.Seed (Bind.ForProver.shapeOf A.Z) × ℕ) (bytes : ByteArray × ByteArray)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) (b : ℕ) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (sharedThread h (readsBase h) (sharedParts h (laterBase h bs pO rest riders Kp₁))
      ⟨w₀, rc, A.H.key (Bind.ForProver.xiAt (Bind.ForProver.shapeOf A.Z) A.Z
        ⟨matrixInput.weights A.Z w₀, rc, sd⟩ bytes)⟩) Said fall b :=
  AtFullSide.K14.five_at_sharedParts matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest
    base h (laterBase h bs pO rest riders Kp₁) w₀ rc sd bytes rfl
    AtFullSide.K14.fixedShared_low.1 AtFullSide.K14.fixedShared_low.2 late Said fall
    b hb1 hb8

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.five_border_eight
