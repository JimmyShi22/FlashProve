-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Binds.lean

The second clause of `SoundAndBinding` (Statements.lean), for a given extractor.
`BindsWith`: an opener of the committer's commitment opens it to the extractor's weights.
`soundAndBinding_iff`: `SoundAndBinding` says that one extractor meets both `SoundForWith`
(MoreStatements.lean), for the claim that the output tokens are the model's, and `BindsWith`.
Three lemmas on `BindsWith`, which is defined in MoreStatements.lean.
Nothing here is about a particular proof system.
-/
import VerifiableInference.MoreStatements

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- Binding with a bound holds with every larger bound. -/
theorem BindsWith.mono {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {ε₁ ε₂ : ℕ → ℝ≥0∞}
    (binds : BindsWith system extractor ε₁) (h : ∀ queries, ε₁ queries ≤ ε₂ queries) :
    BindsWith system extractor ε₂ :=
  fun committerQueries proverQueries State committer committerBound opener openerBound =>
    le_trans (binds committerQueries proverQueries State committer committerBound opener
      openerBound) (h _)

/-- `SoundAndBinding` is soundness and binding for one and the same extractor. -/
theorem soundAndBinding_iff (system : ArgumentSystem) (ε : ℕ → ℝ≥0∞) :
    SoundAndBinding system ε ↔
      ∃ extractor : Commitment → QueryLog → Option system.Weights,
        SoundForWith system extractor system.IsModelOutput ε ∧ BindsWith system extractor ε := by
  constructor
  · rintro ⟨extractor, h⟩
    exact ⟨extractor,
      fun committerQueries proverQueries State committer committerBound =>
        (h committerQueries proverQueries State committer committerBound).1,
      fun committerQueries proverQueries State committer committerBound =>
        (h committerQueries proverQueries State committer committerBound).2⟩
  · rintro ⟨extractor, sound, binds⟩
    exact ⟨extractor, fun committerQueries proverQueries State committer committerBound =>
      ⟨sound committerQueries proverQueries State committer committerBound,
        binds committerQueries proverQueries State committer committerBound⟩⟩

/-- `SoundAndBinding` from soundness with a bound ε₁ and binding with a bound ε₂ for one extractor,
if both bounds are at most ε. -/
theorem soundAndBinding_of_le (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (ε₁ ε₂ ε : ℕ → ℝ≥0∞)
    (sound : SoundForWith system extractor system.IsModelOutput ε₁)
    (binds : BindsWith system extractor ε₂)
    (h₁ : ∀ queries, ε₁ queries ≤ ε queries) (h₂ : ∀ queries, ε₂ queries ≤ ε queries) :
    SoundAndBinding system ε :=
  ⟨extractor, fun committerQueries proverQueries State committer committerBound =>
    ⟨fun prover proverBound =>
        le_trans (sound committerQueries proverQueries State committer committerBound prover
          proverBound) (h₁ _),
      fun opener openerBound =>
        le_trans (binds committerQueries proverQueries State committer committerBound opener
          openerBound) (h₂ _)⟩⟩

end VerifiableInference

#print axioms VerifiableInference.BindsWith.mono
#print axioms VerifiableInference.soundAndBinding_iff
#print axioms VerifiableInference.soundAndBinding_of_le
