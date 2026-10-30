-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/CanServe.lean

`CanServe`: side conditions on a prompt and an output. It is meant as the argument `domain` of
`CompleteOn` (Steps.lean), of `ZeroKnowledgeOn` and of `CompleteSoundZeroKnowledgeOn`
(MoreStatements.lean). One definition, over ModelWeights.lean.
-/
import VerifiableInference.ModelWeights
import IntegerModel.Window

set_option autoImplicit false

namespace VerifiableInference

/-- Side conditions on a prompt and an output at the given settings and weights, in addition to "the
output tokens are the model's": every token is in the vocabulary, the output is not empty, and the
model has a value on the whole window of 1,024 tokens: the prompt, the output, then token 0 as often
as needed, cut at 1,024 (`IntegerModel.zeroFilledWindow`, IntegerModel/Window.lean).
The last condition depends on the weights: a range condition of the integer program can fail at a
position after the output. `Cm.filler` (Cm/RelTrueExp.lean) shows that for a window whose last token
is 1; for a zero-filled window no example is proved. At some weights no prompt and output meet the
three conditions (`canServe_nowhere_atHaltingWeights`,
VerifiableInference/ModelGuardsAtReference.lean, at the settings of the reference table of scales).
Alone the three do not bound the lengths: an empty prompt can meet them. At valid settings, with
"the output tokens are the model's", they imply a non-empty prompt and at most 1,025 tokens together
(by hand, from `canServe_iff`, IntegerModel/Arrays/SameModel.lean;
`IntegerModel.canServeModelOutput_iff`, IntegerModel/ModelOutput.lean;
`IntegerModel.requestOf_some`, VerifiableInference/RequestOfTokens.lean). -/
def CanServe (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (prompt output : List Nat) : Prop :=
  (∀ token ∈ prompt ++ output, token < settings.vocabulary) ∧ output ≠ [] ∧
    (modelNextToken settings weights
      (IntegerModel.zeroFilledWindow prompt output)).isSome = true

end VerifiableInference
