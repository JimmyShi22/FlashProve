-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/TogetherOn.lean: with no condition on the requests, the three statements of
`CompleteSoundZeroKnowledgeOn` (VerifiableInference/MoreStatements.lean) give
`CompleteSoundZeroKnowledge` (VerifiableInference/Statements.lean).

One theorem and its proof, for every argument system.

Limits: this library shows the premise of no system.
-/
import VerifiableInference.Checks
import VerifiableInference.MoreStatements

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference

/-- With no condition on the requests, the three together give `CompleteSoundZeroKnowledge`
(VerifiableInference/Statements.lean), with the same three bounds. Not the other way round: the
first field asks more than `Sound`. This library shows the premise of no system. -/
theorem CompleteSoundZeroKnowledgeOn.toCompleteSoundZeroKnowledge {system : ArgumentSystem}
    {α : ℝ≥0∞} {ε : ℕ → ℝ≥0∞} {ζ : ℕ → ℕ → ℝ≥0∞}
    (h : CompleteSoundZeroKnowledgeOn system (fun _ _ _ => True) α ε ζ) :
    CompleteSoundZeroKnowledge system α ε ζ :=
  ⟨sound_of_soundAndBinding system ε h.sound, (complete_iff_completeOn system α).2 h.complete,
    (zeroKnowledge_iff_zeroKnowledgeOn system ζ).2 h.zeroKnowledge⟩

end VerifiableInference

#print axioms VerifiableInference.CompleteSoundZeroKnowledgeOn.toCompleteSoundZeroKnowledge
