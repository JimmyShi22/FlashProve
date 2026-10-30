-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalSoundProof.lean: the first top line, from the soundness theorem.

 1. sound_of_verify_at speaks of the verifier's own system at the description of the theorem.
 2. That description is flashProveDescription: theDescription_eq.
 3. compile_flashProve_sound_iff carries Sound from there to compile flashProveAtFiles, at every honest part.
-/
import Johnson.Face.FinalStatement
import Johnson.Goal.Skeleton.SoundOfVerifyAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve

/-- **Soundness of the final system, at every honest part.** -/
theorem finalSound (honest : HonestProversAndSettings) : FinalSound honest := by
  intro files parameters taken
  have sound := VerifierAndGoals.AtTheName.sound_of_verify_at files parameters taken.inScope taken.read
    taken.exactMatch
  rw [theDescription_eq] at sound
  exact (compile_flashProve_sound_iff files (settingsOfRead parameters) _ _).2 sound

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalSound
