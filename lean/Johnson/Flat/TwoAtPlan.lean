-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TwoAtPlan.lean: the theorems of Johnson/Flat/TwoSizes.lean and
Johnson/Flat/TwoLink.lean at the chains and the depth of a value of the planner's type of answers.

Statements and their proofs, each one application. In Johnson/Flat/TwoSizes.lean the record G
(`FilesParameters`, OnBytes/Flat/FilesAt.lean) is a letter: the theorems are asked of every G. Here `G := bigAt
p block rec₀ z₀ early` (OnBytes/Flat/BigAt.lean): the key file's chains, the proof file's chains and
the depth of the tree that binds a batch are those of a value p of the type of answers of the
planner of this library's port of the verifier program (`Model.Verify.Planned`; the planner:
`Model.Verify.planned`). The statements are INSTANCES at that value: no premise on p is added or
dropped. As there, the theorems on the wires and on the entry's arm take all of T, so also a coding
(its type holds laws: `OracleCoding`, Rom/Family.lean) and an extractor that they never read: where no such
T is they say nothing.

Main names:
  `innerCompiledVerifierSoundFromDryRunAtFullSize_at`, `innerCompiledVerifierSoundFromDryRunAtSmallSize_at`: the theorem on innerCompiledVerifier there.
  `wiresFromDryRunAtFullSize_at`, `wiresFromDryRunAtSmallSize_at`: the laws of the wires there.
  `slotsFull_at`, `slotsSmall_at`: the number of slots is 2 ^ (the plan's depth), by unfolding.
  `linkPrFull_at`, `linkPrSmall_at`: the entry's arm there.

Limits: those of Johnson/Flat/TwoSizes.lean and Johnson/Flat/TwoLink.lean. `Model.Verify.planned` is
a Lean definition: that it plans as the shipped program does is a fact about the programs, which is
not shown here. p IS A LETTER: any value of the type of the planner's answers: that it is the answer
at any files (`planOf Z = .ok p`) is not asked here (`atPlan_bigAt`, `atPlan_port`,
OnBytes/Flat/BigAt.lean, tie a p with that law to the program's checks). What the instance ties is
one thing: the depth of a batch's tree is the field `logLeaves` of the same p's proof chains. No
number of p is evaluated: what the depth is, and whether p's sizes are those of the entry file and
the decoder of this size, is not said. The other four fields (the first chain's block, the two
sample values, what of an instance comes early) are letters. The four hypotheses are as unproved
here as there; that the makers' guards pass at this G is not shown.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TwoLink
import OnBytes.Flat.BigAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The full-size files -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A}
  (p : Model.Verify.Planned) (block : X → Blk Proof.FirstEnd) (rec₀ : RecFull) (z₀ : X × RecFull)
  (early : X → X)
  {P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).Provers}

/-- Under the four named hypotheses and the theorem on codes (hypotheses of the theorem: Lean's list
of axioms does not show them): the theorem on innerCompiledVerifier at this size, where the key file's and the
proof file's chains and the depth of a batch's tree are those of a value p of the planner's type of
answers. An instance of `innerCompiledVerifierSoundFromDryRunAtFullSize`. -/
theorem innerCompiledVerifierSoundFromDryRunAtFullSize_at (hA : BCHKS46At GF GE)
    {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E (bigAt p block rec₀ z₀ early) P} (h : RemainingSoundnessConditionsFromDryRunAtFullSize T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize T))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize T)) :=
  innerCompiledVerifierSoundFromDryRunAtFullSize hA h

/-- The laws of the wires there: at the written wiring, a wiring of our own choice. An instance of
`wiresFromDryRunAtFullSize`. -/
theorem wiresFromDryRunAtFullSize_at (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E (bigAt p block rec₀ z₀ early) P) :
    CompilerSoundnessConditionStatements.wires (r := innerCompilerInputFromDryRunAtFullSize T) :=
  wiresFromDryRunAtFullSize T

/-- The number of slots there is 2 to the depth that the plan lays for a batch's tree. -/
theorem slotsFull_at :
    (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).N =
      2 ^ p.chains.proof.first.binding.logLeaves := rfl

set_option maxRecDepth 20000 in
/-- Under the theorem on codes: the entry's arm of the compiled verifier there is sound against
every maker. An instance of `linkPrFull`. -/
theorem linkPrFull_at (hA : BCHKS46At GF GE)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E (bigAt p block rec₀ z₀ early) P) (q : Params)
    (M : TypedOracleComputation 256 T.W.K
      (typedOracleCarrier ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).withProvers P) T.Bd
        (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).annT
        (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).annL)
      (OutLA 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).withProvers P)
        (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).annL))
    (t : ℕ) (hq : M.QueryBound t) :
    Rom.Pr (joinedLA T.W T.letters.Sd T.letters.cA q M).withTrace
        (fun _ => {o | o.1.2 = true ∧
          ¬ LinkHolds T.W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1}) ≤
      (((t + tVL T.W) * (1 + 4) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        2 * (((t + tVL T.W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  linkPrFull hA T q M t hq

end

/-! ## The small files -/

section
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A}
  (p : Model.Verify.Planned) (block : X → Blk Proof.FirstEnd) (rec₀ : RecSmall) (z₀ : X × RecSmall)
  (early : X → X)
  {P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).Provers}

/-- Under the four named hypotheses and the theorem on codes (hypotheses of the theorem: Lean's list
of axioms does not show them): the theorem on innerCompiledVerifier at this size, where the key file's and the
proof file's chains and the depth of a batch's tree are those of a value p of the planner's type of
answers. An instance of `innerCompiledVerifierSoundFromDryRunAtSmallSize`. -/
theorem innerCompiledVerifierSoundFromDryRunAtSmallSize_at (hA : BCHKS46At GF GE)
    {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E (bigAt p block rec₀ z₀ early) P} (h : RemainingSoundnessConditionsFromDryRunAtSmallSize T) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtSmallSize T))
      (innerSystem (innerCompilerInputFromDryRunAtSmallSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtSmallSize T)) :=
  innerCompiledVerifierSoundFromDryRunAtSmallSize hA h

/-- The laws of the wires there: at the written wiring, a wiring of our own choice. An instance of
`wiresFromDryRunAtSmallSize`. -/
theorem wiresFromDryRunAtSmallSize_at (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E (bigAt p block rec₀ z₀ early) P) :
    CompilerSoundnessConditionStatements.wires (r := innerCompilerInputFromDryRunAtSmallSize T) :=
  wiresFromDryRunAtSmallSize T

/-- The number of slots there is 2 to the depth that the plan lays for a batch's tree. -/
theorem slotsSmall_at :
    (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).N =
      2 ^ p.chains.proof.first.binding.logLeaves := rfl

set_option maxRecDepth 20000 in
/-- Under the theorem on codes: the entry's arm of the compiled verifier there is sound against
every maker. An instance of `linkPrSmall`. -/
theorem linkPrSmall_at (hA : BCHKS46At GF GE)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E (bigAt p block rec₀ z₀ early) P) (q : Params)
    (M : TypedOracleComputation 256 T.W.K
      (typedOracleCarrier ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).withProvers P) T.Bd
        (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).annT
        (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).annL)
      (OutLA 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).withProvers P)
        (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) (bigAt p block rec₀ z₀ early)).annL))
    (t : ℕ) (hq : M.QueryBound t) :
    Rom.Pr (joinedLA T.W T.letters.Sd T.letters.cA q M).withTrace
        (fun _ => {o | o.1.2 = true ∧
          ¬ LinkHolds T.W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1}) ≤
      (((t + tVL T.W) * (1 + 4) : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        2 * (((t + tVL T.W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  linkPrSmall hA T q M t hq

end

end VerifiableInference.OnPublicFiles
