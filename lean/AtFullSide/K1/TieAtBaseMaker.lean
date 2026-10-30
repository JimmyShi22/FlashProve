-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/TieAtBaseMaker.lean: hTie OF k1_fiveJ_baseMaker (AtFullSide/K1/AtBaseMaker.lean), TO THE LETTER: tie_first (TieAtFirst.lean) at the matrix input, hI paid by trace_at_matrix.

  tie_baseMaker   the item tie l at the reads of each of the 25 segments, at the base maker's return, at the first thread: under hSaid alone

OF COMPLETENESS's KIND: NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean).
NO PROPERTY IS CLAIMED.
-/
import AtFullSide.K1.TieAtFirst
import AtFullSide.K1.TraceAtMatrix
import AtFullSide.K1.AtBaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker matrixInput)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge

/-- **hTie at the base maker's return.** -/
theorem tie_baseMaker {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A) (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) :
    ∀ l, l < 25 → ExchangeAtS (firstThread h parts w) Said (K1.noL l false) (.tie l) :=
  tie_first hA h parts hQ w Said hSaid (trace_at_matrix A.Z)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tie_baseMaker
