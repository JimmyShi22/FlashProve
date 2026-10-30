-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SoundReads.lean: what `Sound` (VerifiableInference/Statements.lean; on that file's
source see lean/CREDITS.md) reads of an argument system, and that it is monotone in its error.

Why. Two systems with different public parameters, committers and honest provers can have one and
the same `Sound`. To compare two large systems Lean is not to unfold both side by side: each is
first brought to `SoundReads`, a form in the four things that `Sound` reads.

Main names (namespace `VerifiableInference`).
  `sysOfReads W Pf π₀ verify next`: the system with the four things that `Sound` reads (the weights'
    type, the proof's type, the verifier, the model's next token) and fillers for all other fields;
    π₀, a proof, serves the filler prover alone.
  `SoundReads W Pf π₀ verify next ε`: `Sound` of that system.
  `sound_eq_reads`: `Sound S ε` is `SoundReads S.Weights S.Proof π₀ S.verify S.nextToken ε`, at
    every π₀. By unfolding.
  `sound_mono`: a system that is `Sound` at ε₁ is `Sound` at every ε₂ above it.

Does not show: anything of any one system.

Terms: lean/GLOSSARY.md.

-/
import VerifiableInference.Statements

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- The system that has the four things that `Sound` reads and, for the rest, fillers: no public
parameters, no randomness, a committer that gives zeros, a prover that gives π₀. -/
def sysOfReads (W Pf : Type) (π₀ : Pf)
    (verify : Commitment → List Token → List Token → Pf → DeterministicAlgorithm Bool)
    (next : W → List Token → Option Token) : ArgumentSystem where
  Weights := W
  PublicParameters := Unit
  publicParameters := fun _ => ()
  CommitmentRandomness := Unit
  Proof := Pf
  nextToken := next
  sampleCommitmentRandomness := .done ()
  commit := fun _ _ => .done fun _ => false
  prove := fun _ _ _ _ => .done π₀
  verify := verify

/-- `Sound` of that system. -/
def SoundReads (W Pf : Type) (π₀ : Pf)
    (verify : Commitment → List Token → List Token → Pf → DeterministicAlgorithm Bool)
    (next : W → List Token → Option Token) (ε : ℕ → ℝ≥0∞) : Prop :=
  Sound (sysOfReads W Pf π₀ verify next) ε

/-- `Sound` reads four things of a system. -/
theorem sound_eq_reads (S : ArgumentSystem) (π₀ : S.Proof) (ε : ℕ → ℝ≥0∞) :
    Sound S ε = SoundReads S.Weights S.Proof π₀ S.verify S.nextToken ε := rfl

/-- `Sound` is monotone in the error. -/
theorem sound_mono {system : ArgumentSystem} {ε₁ ε₂ : ℕ → ℝ≥0∞} (h : Sound system ε₁)
    (le : ∀ n, ε₁ n ≤ ε₂ n) : Sound system ε₂ := by
  obtain ⟨ext, h⟩ := h
  exact ⟨ext, fun cq pq St c hc p hp => le_trans (h cq pq St c hc p hp) (le _)⟩

end VerifiableInference

#print axioms VerifiableInference.sound_eq_reads
#print axioms VerifiableInference.sound_mono
