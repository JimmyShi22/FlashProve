-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/BytesWriterNoProof.lean: the writer of the three files sends every typed proof without a proof string to the one empty form.
By the writer's second arm. Nothing else.
-/
import Johnson.Face.FinalStatement

set_option autoImplicit false
noncomputable section

namespace VerifiableInference.Compilation

/-- **The writer's second arm.** -/
theorem bytesWriterAt_noProof {Zk : OnBytes.K.Pub} (S : FlashProve.DescriptionDataAtFiles Zk) (typed : S.Typed)
    (h : typed.2.2.piB = none) : bytesWriterAt S typed = noProofForm := by
  obtain ⟨aux, ⟨cm, rcd⟩, ⟨copy, pT, ⟨cm', rcd', pL⟩, pB⟩⟩ := typed
  obtain rfl : pB = none := h
  cases pT <;> cases pL <;> rfl

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.bytesWriterAt_noProof
