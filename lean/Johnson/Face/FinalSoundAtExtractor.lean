-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalSoundAtExtractor.lean: SOUNDNESS OF compile
flashProveAtFiles AT THE NAMED EXTRACTOR: the first clause of SoundAndBinding, in the form in which it can be
joined with the second.

Why. Sound and SoundAndBinding (VerifiableInference/Statements.lean) begin "there is one extractor".
finalSound (FinalSoundProof.lean) ends in Sound, which hides its extractor: it cannot be laid beside a
theorem on binding, for nothing says that the two extractors are one. SoundForWith
(VerifiableInference/MoreStatements.lean) is Sound's body with the extractor as an argument.

  `compile_soundForWith_iff`, `flashProve_soundForWith_iff`: soundness at an extractor reads no honest
    part: of compile at a description it is that of VerifierAndGoals's system, whatever its prover. By definition.
  `finalSoundAtExtractor_within`: at files that the verifier takes (in scope, read, exact match), at
    every honest part: SoundForWith of compile flashProveAtFiles at finalExtractor, for "the output tokens are
    the model's", at the error soundnessErrorInQueries t n, for every n ≥ 1.
  **`finalSoundAtExtractor`**: that at n = 1: at finalSoundnessError.
  `bits_mono`, `finalSoundnessError_le_finalBindingError`: the first top line's error is within the
    fourth's.

Limits. Soundness alone: nothing on the committer is shown here. The proof calls the same theorems as
sound_of_verify_at's (the key file's and the proof file's conditions; the link's inside
soundUnderPolicyAtZ_of_two), and its limits travel whole: the random-oracle model; the format's second,
fixed hash function; public files fixed before the hash function is drawn; exact match. Where the test
on the public files fails the verifier rejects everything, and the statement holds for that reason.
-/
import Johnson.Face.FinalBindingStatement
import Johnson.Goal.Skeleton.SoundAndBindingPlain
import Johnson.Goal.Skeleton.SoundOfVerifyMore
import Johnson.Goal.Conditions.KeyOpenHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve VerifiableInference.OnPublicFiles OnBytes.FrontRoad OnBytes.WholeKey
open IntegerTransformer (Settings)
open scoped ENNReal

section Ties

variable (D : Description) (Z : PublicFiles) (s : Settings) (idx : ModelWeights s → (D.C Z).I) (c₀ : Digest)
  (m₀ : D.More) (T : OnPublicFiles.LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D)
  (agree : ∀ c m, T.at (pair c m) = D.input Z c m) (x₀ : (D.C Z).X)
  (provers : HonestProvers ((D.F Z).withProvers (D.P Z)))
  (settings : (reading : T.D) →
    CompiledSettings ((wiringOf D Z s idx c₀ m₀ T pair agree x₀).layoutAtReading reading) provers)
  (firstBlockTest : (reading : T.D) → Rom.More (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256
    (D.input Z c₀ m₀).queryLayout.K (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier (D.input Z c₀ m₀).protocol
                (D.input Z c₀ m₀).LeafBody (D.input Z c₀ m₀).offlineRoundSplits (D.input Z c₀ m₀).linkRoundSplits)) 256)
  (coinBound : ℕ) (Form : Type) (parse : Parser D Z Form)
  (write : TypedProof ((D.F Z).withProvers (D.P Z)) (D.F Z).annT (D.F Z).annL → Form)

/-- **Soundness at a named extractor reads no honest part**: of compile it is that of VerifierAndGoals's system,
whatever its prover. -/
theorem compile_soundForWith_iff
    (prove : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
    (extractor : Commitment → QueryLog → Option (ModelWeights s)) (ε : ℕ → ℝ≥0∞) :
    SoundForWith (compile (atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings
        firstBlockTest coinBound Form parse write)) extractor
      (compile (atDescription D Z s idx c₀ m₀ T pair agree x₀ provers settings firstBlockTest
        coinBound Form parse write)).IsModelOutput ε ↔
      SoundForWith (system D Z s Form prove parse) extractor
        (system D Z s Form prove parse).IsModelOutput ε :=
  Iff.rfl

end Ties

/-- The same at flashProveAtFiles. -/
theorem flashProve_soundForWith_iff (files : PublicFiles) (settings : Settings)
    (part : HonestProversAndSettingsAtFiles files settings)
    (extractor : Commitment → QueryLog → Option (ModelWeights settings)) (ε : ℕ → ℝ≥0∞) :
    SoundForWith (compile (flashProveAtFiles files settings part)) extractor
      (compile (flashProveAtFiles files settings part)).IsModelOutput ε ↔
      SoundForWith (systemOfRecord flashProveDescription files settings) extractor
        (systemOfRecord flashProveDescription files settings).IsModelOutput ε :=
  compile_soundForWith_iff flashProveDescription files settings (backThe files settings) allZeroDigest []
    (layoutsOfBuiltDescription flashProveData allZeroDigest [] files) Prod.mk (familyLaws_the files).eq
    part.fallbackInstance part.provers part.compiledSettings (flashFirstBlockTest files)
    part.coinBound flashProveDescription.Form (flashProveDescription.parse files) (bytesWriter files) (flashProveDescription.prove files settings) extractor ε

/-- Soundness of compile flashProveAtFiles at the named extractor, at every honest part, at the error
soundnessErrorInQueries t n for every n ≥ 1. -/
theorem finalSoundAtExtractor_within (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (taken : FilesTaken files parameters)
    (part : HonestProversAndSettingsAtFiles files (settingsOfRead parameters)) (n : ℕ) (hn : 1 ≤ n) :
    SoundForWith (compile (flashProveAtFiles files (settingsOfRead parameters) part))
      (finalExtractor files (settingsOfRead parameters))
      (compile (flashProveAtFiles files (settingsOfRead parameters) part)).IsModelOutput
      fun t => soundnessErrorInQueries t n := by
  have sound := VerifierAndGoals.AtTheName.soundForWith_record_within (atSecondHashFunction theDescription) soundnessErrorInQueries files
    parameters
    (VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_of_two files parameters taken.inScope taken.read
      (VerifierAndGoals.AtTheName.keySound_at_live_holds files taken.inScope)
      (VerifierAndGoals.AtTheName.proofSoundAt_of_verify files parameters taken.inScope taken.read))
    taken.exactMatch n (within_mono _ hn (theDescription_within OnBytes.secondHashFunction files))
  rw [theDescription_eq] at sound
  exact (flashProve_soundForWith_iff files (settingsOfRead parameters) part _ _).2 sound

/-- **SOUNDNESS OF compile flashProveAtFiles AT THE NAMED EXTRACTOR**, at every honest part, at the error of the
first top line. -/
theorem finalSoundAtExtractor (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (taken : FilesTaken files parameters)
    (part : HonestProversAndSettingsAtFiles files (settingsOfRead parameters)) :
    SoundForWith (compile (flashProveAtFiles files (settingsOfRead parameters) part))
      (finalExtractor files (settingsOfRead parameters))
      (compile (flashProveAtFiles files (settingsOfRead parameters) part)).IsModelOutput
      finalSoundnessError :=
  finalSoundAtExtractor_within files parameters taken part 1 le_rfl

/-- The error of soundness grows with the parser's queries. -/
theorem bits_mono (t : ℕ) {n n' : ℕ} (h : n ≤ n') : soundnessErrorInQueries t n ≤ soundnessErrorInQueries t n' := by
  unfold soundnessErrorInQueries
  exact add_le_add
    (mul_le_mul' (Nat.cast_le.2 (Nat.mul_le_mul_left _ (by omega))) le_rfl)
    (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.pow_le_pow_left (by omega) 2)) _)

/-- The first top line's error is within the fourth's. -/
theorem finalSoundnessError_le_finalBindingError :
    ∀ queries, finalSoundnessError queries ≤ finalBindingError queries := fun queries =>
  (bits_mono queries (Nat.one_le_two_pow : 1 ≤ 2 ^ 23)).trans (le_max_left _ _)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.compile_soundForWith_iff
#print axioms VerifiableInference.Compilation.flashProve_soundForWith_iff
#print axioms VerifiableInference.Compilation.finalSoundAtExtractor_within
#print axioms VerifiableInference.Compilation.finalSoundAtExtractor
#print axioms VerifiableInference.Compilation.bits_mono
#print axioms VerifiableInference.Compilation.finalSoundnessError_le_finalBindingError
