-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FiveAtBaseMakerPaid.lean: the shared sending (kind K1): the five statements, in the form FiveAtBorderJ, at
every place of the kind in the first chain of the online proof, at the return of the named base maker
(ProofFile.Honest.Term.baseMaker), at the first thread (Honest/Thread/TheFirstThread.lean) with the Script firstScriptAt.
The shares of the exchange at the items tie l and wrow are paid.

  1  k1_fiveJ_paid       FiveAtBorderJ at every b whose place in P5J.At.ps has the kind K1
  2  k1_fiveJ_in_scope   at public files in scope and live: the base maker returns, the head stands at its return, and
                         the same holds at the parts firstParts, at every input, under hyes and hSaid alone

From k1_fiveJ_baseMaker_w (FiveAtBaseMakerW.lean) and tie_baseMaker (TieAtBaseMaker.lean). There are 52 such b: 2,
K1.noL l d with l below 25, and 356 (k1_places_52, k1_kind_at: ExchangeAtBase.lean; k1_number_of_kind:
Honest/K1/Law/NumbersOfKind.lean).

What it rests on that is of other kinds' authors: the code switch's handed_at_book, closing_at_head,
publicOk_of_reads; readsLight_of_att; att_returns_at_open; the kind K13's k13_items_at_356_at_firstThread; the table
of steps and its laws (Johnson/AtFull/Shape).

Limits.
  * ONE HYPOTHESIS IS A DEBT: hyes: the run on shapes returns over the 358 members, from startShA. It is proved at no
    public files here. The fields accepted and next rest on it.
  * hSaid: the condition Said gives SaidOk. hA: the base maker returns A. h: the head at that return. hQ: the thread's
    Script is firstScriptAt at the honest prover's parameters.
  * The fields accepted and next are asked with J in hand. That J begins at the chain's start, and that it is carried,
    which needs NextJ at every member in front, of every kind, is not shown here. At a fall that always speaks they
    are idle.
  * Each field stands under the thread's invariant in front of the member. That the invariant holds there at a run
    needs the five statements at every member in front, of every kind. At an input that does not meet the thread's
    valid (ReadyInput) all six fields are idle.
  * At the base maker. The crossing to the honest online prover, which reads this filling through, is not here.
  * The first chain of the online proof alone.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.FiveAtBaseMakerW
import AtFullSide.K1.TieAtBaseMaker
import AtFullSide.K1.HeadAtBaseMaker
import AtFullSide.K1.FirstScriptIsSenders

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

/-- **The five statements at every place of the kind K1 in the first chain, at the base maker's return: one debt left,
hyes.** -/
theorem k1_fiveJ_paid {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 =
      true) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      FiveAtBorderJ (firstThread h parts w) Said
        (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
        b :=
  k1_fiveJ_baseMaker_w hA h parts hQ w Said hSaid fall hyes
    (tie_baseMaker hA h parts hQ w Said hSaid)

/-- **At public files in scope and live**: the base maker returns; the head stands at its return; and at the first
thread with the Script firstScriptAt the five statements hold at every place of the kind K1, at every input, every
list of the falls' stated numbers, every fall and every Said that gives SaidOk, where the run on shapes returns. -/
theorem k1_fiveJ_in_scope (files : VerifierAndGoals.PublicFiles) (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (h : HeadAtReturn files A), baseMaker files = .ok A ∧
      ((firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 = true →
        ∀ (numbers : FallNumbers) (w : LocB FullSizeMatrix)
          (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop),
          (∀ b k m, Said b k m → SaidOk b k m) →
          ∀ (fall : Nat → TS → List Fmt.Drawn → Option String) b p,
            P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
            FiveAtBorderJ
              (firstThread h (firstParts matrixInput OnBytes.HonestTrace.Sz.ref openHonest A
                h.firstChain numbers) w) Said
              (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA)
              fall b) := by
  obtain ⟨A, hA⟩ := baseMaker_returns files scope live
  obtain ⟨h, -⟩ := headAtReturn_baseMaker files scope live hA
  exact ⟨A, h, hA, fun hyes numbers w Said hSaid fall =>
    k1_fiveJ_paid hA h _ rfl w Said hSaid fall hyes⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_fiveJ_paid
#print axioms ProofFile.Honest.K1.k1_fiveJ_in_scope
