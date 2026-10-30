-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InnerCompiledVerifierNumbers.lean: the soundness theorems about `innerCompiledVerifier r`
(`VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound`, `innerCompiledVerifier_soundFor`,
Johnson/Top/InnerCompiledVerifier.lean) at a closed bound, for any stated bound 2^-a on a round's error.

Statements and proofs, one definition. The bound that those theorems state is
t ↦ soundnessBoundOverTypedOracles r.queryLayout b.εs t 0 + b.εId t, that is n · εs + 2 (n + 1)² / 2^256 + εId t at
n = 5 (t + tVC r.queryLayout + 1) (Johnson/TypedOracleCompiler/RecCompile/CmsAnsPr.lean): the wire r.queryLayout stands in it, and no
hypothesis of `CompilerSoundnessConditionsWithMeaning b` says that it is small: at εs = ⊤ the clauses on errors of `keySound`,
`entrySound`, `proofSound` and `seedLaw` hold of everything. Three facts on numbers close that; they
are premises here, a line each:
  rounds: b.εs ≤ (1 + 1/4) · 2^-a, with a + s = 128; queries: tVC r.queryLayout ≤ n;
  cost: b.εId t ≤ (t + 2)² / 2^256 for every t.

Main names:
  `closedFormSoundnessErrorBound s n t`: levelAt s (5 (t + n + 1) + 1) + (t + 2)² / 2^256, where `levelAt s N`
    (Johnson/Thin/K/Level/LevelAt.lean) is 2^-(127 - (j + s)) at the least j with N ≤ 2^j, if
    j + s ≤ 126, and ⊤ else.
  `compiledSoundnessError_le_levelAt`: under rounds and queries:
    compiledSoundnessError b t ≤ levelAt s (5 (t + n + 1) + 1) + b.εId t.
  `compiledSoundnessError_le`: under the three: compiledSoundnessError b t ≤ closedFormSoundnessErrorBound s n t.
  `innerCompiledVerifier_soundFor_closed`, `innerCompiledVerifier_sound_closed`: the statements of
    `innerCompiledVerifier_soundFor` and `innerCompiledVerifier_sound` at that bound, under their hypotheses and the
    three.
  `closedFormSoundnessErrorBound_le`: t + n + 1 ≤ 2^i and i + 3 + s ≤ 126 give
    closedFormSoundnessErrorBound s n t ≤ 2^-(127 - (i + 3 + s)) + (t + 2)² / 2^256: the first term is
    2^-(a - 4 - i).

Limits: n and a are numbers that `innerCompiledVerifier r` does not read. t counts queries to the one hash
function, `tVC` the typed queries of the compiled verifier. These statements do not say that any r
and b have `CompilerSoundnessConditionsWithMeaning b` or the three facts. A number n that is proved for the count `tVC` of
Johnson/RecCompile/Cms.lean is not one for the count here. Against the stated bound the step
function gives away up to two bits (the power of two above 5 (t + n + 1) + 1; the factor 8/5 of
`level_arith`), and `closedFormSoundnessErrorBound_le` up to some two and a half. All that the head of
Johnson/Top/InnerCompiledVerifier.lean lists under Limits holds here too. The hash length 256 is fixed.


-/
import Johnson.Top.InnerCompiledVerifier
import Johnson.TypedOracleCompiler.RecCompile.ClosedAns

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch.Cms TopC

/-- The closed bound: s = 128 - a, n a bound on the verifier's own queries, t the adversary's. -/
def closedFormSoundnessErrorBound (s n t : ℕ) : ℝ≥0∞ :=
  levelAt s ((t + n + 1) * 5 + 1) + (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

variable {r : InnerCompilerInput}

/-- The stated bound is at most the closed step function and the commitment's cost. -/
theorem compiledSoundnessError_le_levelAt (b : SoundnessAnalysisData r) (a s n : ℕ) (has : a + s = 128)
    (rounds : b.εs ≤ (1 + (4 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ a)⁻¹) (queries : tVC r.queryLayout ≤ n) (t : ℕ) :
    compiledSoundnessError b t ≤ levelAt s ((t + n + 1) * 5 + 1) + b.εId t :=
  add_le_add (epsA_le_levelAt r.queryLayout b.εs _ a s n t 0 has rounds le_rfl queries) le_rfl

/-- The stated bound is at most the closed bound. -/
theorem compiledSoundnessError_le (b : SoundnessAnalysisData r) (a s n : ℕ) (has : a + s = 128)
    (rounds : b.εs ≤ (1 + (4 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ a)⁻¹) (queries : tVC r.queryLayout ≤ n)
    (cost : ∀ t, b.εId t ≤ (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) (t : ℕ) :
    compiledSoundnessError b t ≤ closedFormSoundnessErrorBound s n t :=
  le_trans (compiledSoundnessError_le_levelAt b a s n has rounds queries t)
    (add_le_add le_rfl (cost t))

/-- Soundness of `innerCompiledVerifier r` for a claim, at the closed bound. -/
theorem innerCompiledVerifier_soundFor_closed (b : SoundnessAnalysisData r)
    (claim : r.Index → List Token → List Token → Prop) (h : CompilerSoundnessConditions b) (hs : CompilerSoundnessConditionStatements.soundFor b claim)
    (a s n : ℕ) (has : a + s = 128)
    (rounds : b.εs ≤ (1 + (4 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ a)⁻¹) (queries : tVC r.queryLayout ≤ n)
    (cost : ∀ t, b.εId t ≤ (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    SoundForWith (innerSystem r) (compiledIndexExtractor b) claim (closedFormSoundnessErrorBound s n) :=
  fun tC tP St c hc p hp =>
    le_trans (innerCompiledVerifier_soundFor b claim h hs tC tP St c hc p hp)
      (compiledSoundnessError_le b a s n has rounds queries cost _)

/-- Soundness of `innerCompiledVerifier r`, at the closed bound. -/
theorem innerCompiledVerifier_sound_closed (b : SoundnessAnalysisData r) (h : CompilerSoundnessConditionsWithMeaning b) (a s n : ℕ) (has : a + s = 128)
    (rounds : b.εs ≤ (1 + (4 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ a)⁻¹) (queries : tVC r.queryLayout ≤ n)
    (cost : ∀ t, b.εId t ≤ (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    SoundForWith (innerSystem r) (compiledIndexExtractor b) (innerSystem r).IsModelOutput (closedFormSoundnessErrorBound s n) :=
  innerCompiledVerifier_soundFor_closed b _ h.toCompilerSoundnessConditions h.sound a s n has rounds queries cost

/-- The closed bound in levels. -/
theorem closedFormSoundnessErrorBound_le (s n t i : ℕ) (hi : t + n + 1 ≤ 2 ^ i) (hj : i + 3 + s ≤ 126) :
    closedFormSoundnessErrorBound s n t ≤
      ((2 : ℝ≥0∞) ^ (127 - (i + 3 + s)))⁻¹ + (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  add_le_add (levelAt_le s _ (i + 3) (by
    have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    rw [pow_add]
    omega) hj) le_rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.compiledSoundnessError_le_levelAt
#print axioms VerifiableInference.OnPublicFiles.compiledSoundnessError_le
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_soundFor_closed
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_sound_closed
#print axioms VerifiableInference.OnPublicFiles.closedFormSoundnessErrorBound_le
