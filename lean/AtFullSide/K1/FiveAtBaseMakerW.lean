-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FiveAtBaseMakerW.lean: the shared sending (kind K1): the five statements at every place of the kind in
the first chain, at the return of the named base maker (ProofFile.Honest.Term.baseMaker), with the share at the item
wrow at number 356 paid.

  1  pile_open_honest        openHonest.pile is pileAnyK3
  2  k1_fiveJ_baseMaker_w    k1_fiveJ_baseMaker (AtBaseMaker.lean) without its hypothesis hWrow

By hWrow_first (WrowAtFirst.lean), which rests on the kind K13's k13_items_at_356_at_firstThread.

Limits. Those of FiveByKind.lean, but for hWrow. hyes (the run on shapes returns) and hTie (the share at tie l at
the 25 members "reads") are debts; hSaid, the head h and hQ are hypotheses; each field stands under the thread's
invariant. This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.AtBaseMaker
import AtFullSide.K1.WrowAtFirst

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
open ProofFile.Honest.K13 (pileAnyK3)

/-- The pile that the honest prover's open functions lay. -/
theorem pile_open_honest : openHonest.pile = pileAnyK3 := rfl

/-- **The five statements at every place of the kind K1 in the first chain, at the base maker's return; the share
at wrow paid.** -/
theorem k1_fiveJ_baseMaker_w {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 =
      true)
    (hTie : ∀ l, l < 25 → ExchangeAtS (firstThread h parts w) Said (K1.noL l false) (.tie l)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      FiveAtBorderJ (firstThread h parts w) Said
        (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
        b :=
  k1_fiveJ_baseMaker hA h parts hQ w Said hSaid fall hyes hTie
    (hWrow_first hA h parts hQ w pile_open_honest Said)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.pile_open_honest
#print axioms ProofFile.Honest.K1.k1_fiveJ_baseMaker_w
