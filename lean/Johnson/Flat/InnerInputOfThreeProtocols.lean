-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/InnerInputOfThreeProtocols.lean: an input of the top over the compiled verifier that hashes a file as three
chains (`InnerCompilerInput`, `SoundnessAnalysisData`, Johnson/Top/InnerCompiledVerifier.lean), whose object is made of three
protocols, one for each file of the prover, laid as they are.

Definitions, one structure of hypotheses, three theorems. The object is `F.withProvers P`
(OnBytes/Flat/Object.lean); the key file's and the entry file's marks are `F.annT`, `F.annL`; which
part of an instance is named early and which late are `F.early`, `F.late`.

Main names:
  `InnerCompilerInputFieldsOverThreeProtocols F P`: the fields of an input beside the object and the marks, typed over `F.withProvers P`.
    `innerInputOfThreeProtocols F P T : InnerCompilerInput`. `soundnessAnalysisDataOfThreeProtocols F P T U : SoundnessAnalysisData (innerInputOfThreeProtocols F P T)`: witnesses
    and relation are the configuration's cells and relaxed relation.
  `CompilerSoundnessConditionsOverThreeProtocols F P T U`: the named hypotheses in the terms of F: fifteen. `CompilerSoundnessConditionsOverThreeProtocols.holes : CompilerSoundnessConditionsOverThreeProtocols F P T
    U → CompilerSoundnessConditionsWithMeaning (soundnessAnalysisDataOfThreeProtocols F P T U)`. Of the sixteen fields of `CompilerSoundnessConditionsWithMeaning` one holds by the way the
    object is made and says nothing of a protocol: `noneColl` (by the definition of the decoder
    `ConfigurationWithOutOfDomainSample.D`).
  `innerCompiledVerifier_sound_overThreeProtocols`, `innerCompiledVerifier_soundFor_overThreeProtocols`.

Limits: no F, P, T, U is given here, and none is shown to have `CompilerSoundnessConditionsOverThreeProtocols`. Laws that stand in the
types of `T.m` and `T.W` are not counted among the fields.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.InnerCompiledVerifier
import OnBytes.Flat.Object

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop OnBytes.Flat
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The fields of an input beside the object and the marks. -/
structure InnerCompilerInputFieldsOverThreeProtocols {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) where
  Bd : Type
  W : QueryLayout 256 (typedOracleCarrier (F.withProvers P) Bd F.annT F.annL)
  Sd : OutOfDomainSampleQueryLayout 256 W.K (F.withProvers P) Bd F.annT F.annL
  /-- how a record's answers are written as a list of digests -/
  cA : C.Ans → List (Dig 256)
  /-- a fixed record -/
  r₀ : C.Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier (F.withProvers P) Bd F.annT F.annL)) 256
  enc : KeyRoot 256 (F.withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option C.X
  nextToken : C.I → List Token → Option Token
  ISK : Type
  commit : C.I → Rom.OComp (typedOracleFamily 256 W.K (typedOracleCarrier (F.withProvers P) Bd F.annT F.annL))
    (KeyRoot 256 (F.withProvers P) × ISK)
  prove : ISK → (b : List (C.X × Unit)) →
    Rom.OComp (typedOracleFamily 256 W.K (typedOracleCarrier (F.withProvers P) Bd F.annT F.annL))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 (F.withProvers P) F.annT F.annL) b)
  bound : ℕ
  π₀ : KeyRoot 256 (F.withProvers P) × OfflineLinkOnlineProof 256 (F.withProvers P) F.annT F.annL

/-- The input whose object is made of the three protocols. -/
def innerInputOfThreeProtocols {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) (T : InnerCompilerInputFieldsOverThreeProtocols F P) : InnerCompilerInput where
  Index := C.I
  Instance := C.X
  protocol := F.withProvers P
  LeafBody := T.Bd
  offlineRoundSplits := F.annT
  linkRoundSplits := F.annL
  queryLayout := T.W
  seedQueries := T.Sd
  answerCode := T.cA
  fixedSample := T.r₀
  compilerParameters := T.p
  oracleCoding := T.m
  keyCode := T.enc
  buildInstance := T.build
  nextToken := T.nextToken
  ProverKey := T.ISK
  commit := T.commit
  prove := T.prove
  coinBound := T.bound
  fallbackProof := T.π₀

/-- What the hypotheses name beside: the extractor behind the commitment, its cost, an instance, the
stated bound on a round's error. -/
structure SoundnessAnalysisFieldsOverThreeProtocols {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) where
  ext : ZKCP.Extractor 256 C.I C.X Unit (ZKCP.Digest 256)
    (KeyRoot 256 (F.withProvers P) × OfflineLinkOnlineProof 256 (F.withProvers P) F.annT F.annL)
  εId : ℕ → ℝ≥0∞
  x₀ : C.X
  εs : ℝ≥0∞

/-- Witnesses and relation are the configuration's. -/
def soundnessAnalysisDataOfThreeProtocols {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) (T : InnerCompilerInputFieldsOverThreeProtocols F P) (U : SoundnessAnalysisFieldsOverThreeProtocols F P) :
    SoundnessAnalysisData (innerInputOfThreeProtocols F P T) where
  Wn := C.Cells
  Rno := C.Rno
  ext := U.ext
  εId := U.εId
  x₀ := U.x₀
  εs := U.εs

variable {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) (T : InnerCompilerInputFieldsOverThreeProtocols F P) (U : SoundnessAnalysisFieldsOverThreeProtocols F P)

/-- The compiler is handed the three protocols, their marks and the instance's two parts as they
are. -/
example : (innerInputOfThreeProtocols F P T).protocol.offline = F.key := rfl
example : (innerInputOfThreeProtocols F P T).protocol.link = F.entry := rfl
example : (innerInputOfThreeProtocols F P T).protocol.onlineBatch = ⟨F.proof, F.ann⟩ := rfl
example : (innerInputOfThreeProtocols F P T).offlineRoundSplits = F.annT := rfl
example : (innerInputOfThreeProtocols F P T).protocol.early = F.early ∧ (innerInputOfThreeProtocols F P T).protocol.late = F.late := ⟨rfl, rfl⟩

/-- The named hypotheses, in the terms of the three protocols. -/
structure CompilerSoundnessConditionsOverThreeProtocols : Prop where
  /-- KEY FILE: its protocol is round-by-round sound for "the word has a collision at the record's
  seed, or decodes with the record to an index"; every round's error, a shared round's counted once
  for each leaf of the call's request tree, is at most εs -/
  keySound      : ∃ ε, Err.Below (Err.timesShared (2 ^ T.W.depthReqT) F.annT ε) U.εs ∧
    F.key.Sound (fun rec y => C.coll y rec.1 ∨ C.D y rec ≠ none) ε
  /-- ENTRY FILE: the same for "the first word gives no index, or the further word has a collision,
  or both give the same index" -/
  entrySound    : ∃ ε, Err.Below (Err.timesShared (2 ^ T.W.depthReqL) F.annL ε) U.εs ∧
    F.entry.Sound
      (fun rr y => C.D y.1 rr.1 = none ∨ C.coll y.2 rr.2.1 ∨ C.D y.2 rr.2 = C.D y.1 rr.1) ε
  /-- PROOF FILE: in the form for batches, with the instance's early and late parts, for the relaxed
  relation at the decoded index -/
  proofSound    : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols F P T U)
  keyLocal      : F.key.IsLocal
  entryLocal    : F.entry.IsLocal
  proofLocal    : F.proof.IsLocal
  keyCoherent   : F.annT.Coherent
  entryCoherent : F.annL.Coherent
  proofCoherent : F.ann.Coherent
  seedLaw       : CompilerSoundnessConditionStatements.seedLaw (soundnessAnalysisDataOfThreeProtocols F P T U)
  wires         : CompilerSoundnessConditionStatements.wires (r := innerInputOfThreeProtocols F P T)
  answersCode   : CompilerSoundnessConditionStatements.answersCode (r := innerInputOfThreeProtocols F P T)
  answersLength : CompilerSoundnessConditionStatements.answersLength (r := innerInputOfThreeProtocols F P T)
  commitment    : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataOfThreeProtocols F P T U)
  sound         : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataOfThreeProtocols F P T U)

variable {F P T U}

/-- The sixteen, from the fifteen. -/
theorem CompilerSoundnessConditionsOverThreeProtocols.holes (h : CompilerSoundnessConditionsOverThreeProtocols F P T U) : CompilerSoundnessConditionsWithMeaning (soundnessAnalysisDataOfThreeProtocols F P T U) where
  noneColl := F.obj_noneColl P
  keySound := h.keySound
  entrySound := h.entrySound
  proofSound := h.proofSound
  keyLocal := h.keyLocal
  entryLocal := h.entryLocal
  proofLocal := h.proofLocal
  keyCoherent := h.keyCoherent
  entryCoherent := h.entryCoherent
  proofCoherent := h.proofCoherent
  seedLaw := h.seedLaw
  wires := h.wires
  answersCode := h.answersCode
  answersLength := h.answersLength
  commitment := h.commitment
  sound := h.sound

/-- Under the fifteen named hypotheses `CompilerSoundnessConditionsOverThreeProtocols F P T U` (hypotheses of the theorem: Lean's list of
axioms does not show them): the theorem on innerCompiledVerifier at an input made of three protocols. -/
theorem innerCompiledVerifier_sound_overThreeProtocols (h : CompilerSoundnessConditionsOverThreeProtocols F P T U) :
    SoundForWith (innerSystem (innerInputOfThreeProtocols F P T)) (compiledIndexExtractor (soundnessAnalysisDataOfThreeProtocols F P T U))
      (innerSystem (innerInputOfThreeProtocols F P T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataOfThreeProtocols F P T U)) :=
  innerCompiledVerifier_sound _ h.holes

/-- Under the fifteen named hypotheses `CompilerSoundnessConditionsOverThreeProtocols F P T U`, of which the last, `sound`, is not used,
and under `CompilerSoundnessConditionStatements.soundFor` at the claim (hypotheses of the theorem: Lean's list of axioms does not
show them): the same for any claim. -/
theorem innerCompiledVerifier_soundFor_overThreeProtocols (claim : C.I → List Token → List Token → Prop) (h : CompilerSoundnessConditionsOverThreeProtocols F P T U)
    (hs : CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataOfThreeProtocols F P T U) claim) :
    SoundForWith (innerSystem (innerInputOfThreeProtocols F P T)) (compiledIndexExtractor (soundnessAnalysisDataOfThreeProtocols F P T U)) claim
      (compiledSoundnessError (soundnessAnalysisDataOfThreeProtocols F P T U)) :=
  innerCompiledVerifier_soundFor _ claim h.holes.toCompilerSoundnessConditions hs

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.CompilerSoundnessConditionsOverThreeProtocols.holes
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound_overThreeProtocols
