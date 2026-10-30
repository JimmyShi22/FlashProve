-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: the statements of Johnson/M1/KeyNumbers.lean, by evaluation in Lean's kernel at the written values.
/-
Johnson/M1/KeyNumbersProved.lean: the count at the key file's three chains, with the tests that can fail. No property of the protocol is
claimed here.
-/
import Johnson.M1.KeyNumbers

set_option autoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

set_option maxRecDepth 1000000 in
/-- The fold's fresh mask, by its numbers: one mask row under mask code 0, no sample. -/
theorem foldSentK_is : foldSentK =
    #[⟨{ code := noId, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 0 }, 0⟩] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Mask code 0: length 2^13, tail 146. -/
theorem maskK0 : (Johnson.G.keyCodesWritten.mask.getD 0 default).logN = 13 ∧
    (Johnson.G.keyCodesWritten.mask.getD 0 default).r = 146 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem drawnK : Spec.drawnK := by
  unfold Spec.drawnK
  decide +kernel

set_option maxRecDepth 1000000 in
theorem tabWithinK : Spec.tabWithinK := by
  unfold Spec.tabWithinK
  decide +kernel

set_option maxRecDepth 1000000 in
theorem countK : Spec.countK := by
  unfold Spec.countK
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rootsTieK : Spec.rootsTieK := by
  unfold Spec.rootsTieK
  decide +kernel

set_option maxRecDepth 1000000 in
theorem edgesK : Spec.edgesK := by
  unfold Spec.edgesK
  decide +kernel

end OnBytes.M1

#print axioms OnBytes.M1.drawnK
#print axioms OnBytes.M1.countK
#print axioms OnBytes.M1.rootsTieK
#print axioms OnBytes.M1.edgesK
