-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FiveOfWholeRun.lean: the shared sending (kind K1): the five statements, in the form FiveAtBorderJ, at every
place of the kind in the first chain of the online proof, at the return of the named base maker, with the hypothesis
hyes of FiveAtBaseMakerPaid.lean drawn from one closed statement on the written table of steps.

  1  k1_fiveJ_of_run            k1_fiveJ_paid without hyes, from hW
  2  k1_fiveJ_in_scope_of_run   k1_fiveJ_in_scope without hyes, from hW

hW : RunsAll 0 358 startShA c says that at the stored full-size public files the table's steps on shapes, started from
startShA, return at all 358 members of the first chain, with the value c, at every record that publicOfO returns at
these files; it does not say that a record is there (RunsAll, Johnson/AtFull/Shape/JoinAll.lean). It names no public
files of the theorem, no prover and no input. yes_of_whole (Johnson/AtFull/Shape/Scope/YesOfWhole.lean) carries it to every public files under
the head. hW is the statement of runOnShapes_toEnd in the side library ShapeLines (ShapeLines/FirstChainRuns.lean), which
this library does not import; runOnShapes_atARecord there says that a record is there. Over that library the two laws
close by one line each.

Limits.
  * hW is a hypothesis here.
  * hSaid: the condition Said gives SaidOk. In 1: hA, the head h and hQ are hypotheses.
  * The fields accepted and next are asked with J in hand. That J begins at the chain's start, and that it is carried,
    which needs NextJ at every member in front, of every kind, is not shown here. At a fall that always speaks they
    are idle. The run on shapes shows no member's accept: shapes alone, no value.
  * Each field stands under the thread's invariant in front of the member. That the invariant holds there at a run
    needs the five statements at every member in front, of every kind. At an input that does not meet the thread's
    valid (ReadyInput) all six fields are idle.
  * At the base maker. The crossing to the honest online prover, which reads this filling through, is not here.
  * The first chain of the online proof alone.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.FiveAtBaseMakerPaid
import Johnson.AtFull.Shape.Scope.YesOfWhole

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

/-- The run on shapes returns at the base maker's return, at the thread's own ground. -/
theorem hyes_of_run {files : VerifierAndGoals.PublicFiles} {W₀ Rc Tr X₀ X : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) {c : ShA} (hW : RunsAll 0 358 startShA c) :
    (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 = true := by
  obtain ⟨Bs, _, _, _, _, _, hB, -⟩ := reads_head_at h.head
  rw [seatGround_of_base hB]
  exact Scope.yes_of_whole h.head hB hW

/-- **The five statements at every place of the kind K1 in the first chain, at the base maker's return, from the whole
run on shapes.** -/
theorem k1_fiveJ_of_run {c : ShA} (hW : RunsAll 0 358 startShA c) {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (hA : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      FiveAtBorderJ (firstThread h parts w) Said
        (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
        b :=
  k1_fiveJ_paid hA h parts hQ w Said hSaid fall (hyes_of_run h hW)

/-- **At public files in scope and live, from the whole run on shapes.** -/
theorem k1_fiveJ_in_scope_of_run {c : ShA} (hW : RunsAll 0 358 startShA c) (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (h : HeadAtReturn files A), baseMaker files = .ok A ∧
      ∀ (numbers : FallNumbers) (w : LocB FullSizeMatrix)
        (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop),
        (∀ b k m, Said b k m → SaidOk b k m) →
        ∀ (fall : Nat → TS → List Fmt.Drawn → Option String) b p,
          P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
          FiveAtBorderJ
            (firstThread h (firstParts matrixInput OnBytes.HonestTrace.Sz.ref openHonest A
              h.firstChain numbers) w) Said
            (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA)
            fall b := by
  obtain ⟨A, h, hA, H⟩ := k1_fiveJ_in_scope files scope live
  exact ⟨A, h, hA, H (hyes_of_run h hW)⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.hyes_of_run
#print axioms ProofFile.Honest.K1.k1_fiveJ_of_run
#print axioms ProofFile.Honest.K1.k1_fiveJ_in_scope_of_run
