-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/AtBaseMaker.lean: the shared sending (kind K1): the five statements at every place of the kind in the
first chain, at the return of the named base maker (ProofFile.Honest.Term.baseMaker, E2E/BaseMaker.lean): the maker at
the filling that the honest online prover's filling reads through.

  1  k1_fiveJ_baseMaker   k1_fiveJ_first (FiveByKind.lean) at I := matrixInput, S := Sz.ref, Op := openHonest

One call: baseMaker files unfolds to onlineProverFromPublicFiles at onlineProverPartsInUse matrixInput secondHashFunction Sz.ref openHonest.

Limits. Those of FiveByKind.lean, word for word: hyes, hTie and hWrow are debts; hSaid, the head h and hQ are
hypotheses; each field stands under the thread's invariant. This file proves nothing about completeness,
soundness or hiding.
-/
import AtFullSide.K1.FiveByKind
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (KindName)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker matrixInput)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open Johnson.AtFull.Shape

/-- **The five statements at every place of the kind K1 in the first chain, at the base maker's return.** -/
theorem k1_fiveJ_baseMaker {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 =
      true)
    (hTie : ∀ l, l < 25 → ExchangeAtS (firstThread h parts w) Said (K1.noL l false) (.tie l))
    (hWrow : ExchangeAtS (firstThread h parts w) Said 356 .wrow) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      FiveAtBorderJ (firstThread h parts w) Said
        (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
        b :=
  k1_fiveJ_first hA h parts hQ w Said hSaid fall hyes hTie hWrow

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_fiveJ_baseMaker
