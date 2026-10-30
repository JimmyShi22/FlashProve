-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/ToldThin.lean: at letters R, T : LayoutsByPublicReading R, b : SoundnessAnalysisData R: the hypotheses of
  `innerCompiledVerifier_sound` that read neither seedQueries, answerCode, oracleCoding nor keyCode are one proposition at R's own names b and
  at `T.beside b.Wn b.Rno b.x₀ b.εs d`, at every d: by unfolding.

So the fifteen at every d come from eleven at b, the seed's law and the answers' two laws at every
  d, and "code". A sister of `T.core_of` (Johnson/Top/InnerCompiledVerifierByPublicReading.lean), which starts from the
  fifteen at one d₀. Why at letters: at a written T Lean first compares the two inputs field by
  field, the codings among them, and does not come back; at letters that comparison fails at once
  and the definitions are unfolded.
Limits: nothing on soundness.

-/
import Johnson.Top.InnerCompiledVerifierByPublicReading

set_option autoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b : SoundnessAnalysisData R)

/-- **The fifteen at every d.** -/
theorem LayoutsByPublicReading.core_from (code : ZKCP.CodeIsOneToOne T.encT)
    (noneColl : CompilerSoundnessConditionStatements.noneColl (r := R)) (keySound : CompilerSoundnessConditionStatements.keySound b)
    (entrySound : CompilerSoundnessConditionStatements.entrySound b) (proofSound : CompilerSoundnessConditionStatements.proofSound b)
    (keyLocal : CompilerSoundnessConditionStatements.keyLocal (r := R)) (entryLocal : CompilerSoundnessConditionStatements.entryLocal (r := R))
    (proofLocal : CompilerSoundnessConditionStatements.proofLocal (r := R)) (keyCoherent : CompilerSoundnessConditionStatements.keyCoherent (r := R))
    (entryCoherent : CompilerSoundnessConditionStatements.entryCoherent (r := R)) (proofCoherent : CompilerSoundnessConditionStatements.proofCoherent (r :=
                                                                  R))
    (wires : CompilerSoundnessConditionStatements.wires (r := R)) (seed : ∀ d, (T.Sd d).Law b.εs)
    (ansCode : ∀ d, CompilerSoundnessConditionStatements.answersCode (r := T.at d))
    (ansLength : ∀ d, CompilerSoundnessConditionStatements.answersLength (r := T.at d)) (d : T.D) :
    CompilerSoundnessConditions (T.beside b.Wn b.Rno b.x₀ b.εs d) where
  noneColl := noneColl
  keySound := keySound
  entrySound := entrySound
  proofSound := proofSound
  keyLocal := keyLocal
  entryLocal := entryLocal
  proofLocal := proofLocal
  keyCoherent := keyCoherent
  entryCoherent := entryCoherent
  proofCoherent := proofCoherent
  seedLaw := seed d
  wires := wires
  answersCode := ansCode d
  answersLength := ansLength d
  commitment := T.commitment_of_code code b.Wn b.Rno b.x₀ b.εs d

/-- **The meaning at every d.** -/
theorem LayoutsByPublicReading.sound_from (h : CompilerSoundnessConditionStatements.sound b) (d : T.D) :
    CompilerSoundnessConditionStatements.sound (T.beside b.Wn b.Rno b.x₀ b.εs d) := h

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.core_from
#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.sound_from
