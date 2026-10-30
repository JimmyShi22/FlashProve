-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/PlanOkForFree.lean: at the full size, at the frame with the entry file's three
letters: whoever owes the key file's or the proof file's hypothesis on soundness at a description's
own run may take the description's tests on the plan as given. Theorems.

Why. `FileDescription.run` refuses first of all where `F.planOk` says no (Johnson/Desc/Block.lean:
`runCore` throws `planWord`). So at such a description the decision never says yes, and the two
hypotheses hold there for nothing (`keySoundOfFullD_of_never`, `proofSoundOfFullD_of_never`,
Johnson/Flat/Dec/FailsClosed.lean). The tests are in the verifier's own text already: no list of
what is owed need name one of them, and no gate need ask one again. `planOk` holds, among others:
`sealLast` (the first chain's last block has a round); the blocks' rounds in a row are the plan's
declared rounds, whole; `labelsOk`; `placesOk`; `beforeOk`; `treeSharingOk`; `readsOk`; every block's own
test on the plan.

Main names.
  `run_false_of_planOk_false`: where the tests on the plan say no, the decision says no at all
    views.
  `sealLast_of_planOk`: the tests' second half.
  `keySoundOfFullD_of_planOk`, `proofSoundOfFullD_of_planOk`: the hypothesis, from the hypothesis
    under `F.planOk = true`; the decision is a letter with an equation (`gatedFileDecision b F.run`), b any.
  `proofSoundOfFullD_of_sealLast`: the case that the lists above ask by name.

Limits. Tools: a case split. Nothing is proved here but that a premise which is a test of the
verifier's own may be taken as given. At a description whose tests on the plan say no the hypotheses
are true and empty. Nothing on whether any description's tests say yes. The full size alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.ClosedAll
import Johnson.Desc.Sound.DescRunsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

/-- **Where the tests on the plan say no, the decision says no at all views.** -/
theorem run_false_of_planOk_false {Xi : Type} (F : FileDescription Xi) (h : F.planOk = false) (x : Xi)
    (v₁ v₂ v₃ : Fmt.View) : F.run x v₁ v₂ v₃ = false := by
  unfold FileDescription.run
  cases hr : F.runEnd x v₁ v₂ v₃ with
  | error m => rfl
  | ok t =>
    obtain ⟨e₁, e₂, e₃⟩ := t
    have hp := ((runEndIs Xi F x v₁ v₂ v₃ e₁ e₂ e₃).1 hr).1
    rw [h] at hp
    cases hp

/-- `sealLast` is one of the tests on the plan. -/
theorem sealLast_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    F.sealLast = true := by
  unfold FileDescription.planOk at h
  exact (Bool.and_eq_true_iff.1 h).2

end VerifiableInference.Desc.Sound

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.Desc VerifiableInference.Desc.Sound

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}

/-- **The key file's hypothesis may take the description's tests on the plan as given.** -/
theorem keySoundOfFullD_of_planOk (F : FileDescription RecFull) (b : Bool) (er : runK = gatedFileDecision b F.run)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (h : F.planOk = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T)) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T) := by
  cases hp : F.planOk with
  | true => exact h hp
  | false =>
    refine keySoundOfFullD_of_never (fun r v₁ v₂ v₃ => ?_) T
    rw [er]
    show (b && F.run r v₁ v₂ v₃) = false
    rw [run_false_of_planOk_false F hp, Bool.and_false]

/-- **The proof file's hypothesis may take the description's tests on the plan as given.** -/
theorem proofSoundOfFullD_of_planOk (F : FileDescription (X × RecFull)) (b : Bool)
    (er : runP = gatedFileDecision b F.run)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (h : F.planOk = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T)) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T) := by
  cases hp : F.planOk with
  | true => exact h hp
  | false =>
    refine proofSoundOfFullD_of_never (fun x v₁ v₂ v₃ => ?_) T
    rw [er]
    show (b && F.run x v₁ v₂ v₃) = false
    rw [run_false_of_planOk_false F hp, Bool.and_false]

/-- The case that the lists of what is left ask by name: "the first chain's last block has a
round". -/
theorem proofSoundOfFullD_of_sealLast (F : FileDescription (X × RecFull)) (b : Bool)
    (er : runP = gatedFileDecision b F.run)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (h : F.sealLast = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T)) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T) :=
  proofSoundOfFullD_of_planOk F b er T fun hp => h (sealLast_of_planOk F hp)

end VerifiableInference.OnPublicFiles

end

#print axioms VerifiableInference.Desc.Sound.run_false_of_planOk_false
#print axioms VerifiableInference.OnPublicFiles.keySoundOfFullD_of_planOk
#print axioms VerifiableInference.OnPublicFiles.proofSoundOfFullD_of_planOk
#print axioms VerifiableInference.OnPublicFiles.proofSoundOfFullD_of_sealLast
