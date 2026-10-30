-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Window.lean: the window of 1,024 tokens of a prompt and an output, as numbers. One
definition; no import.
-/

namespace IntegerModel

/-- The 1,024 tokens of a request that is built with the empty list for the prover's padding
(`requestOfTokens`, VerifiableInference/RequestOfTokens.lean): the prompt, the output, then token 0
as often as needed. With 1,025 tokens in all, the last output token is outside it. -/
def zeroFilledWindow (prompt output : List Nat) : List Nat :=
  (prompt ++ output ++ List.replicate 1024 0).take 1024

end IntegerModel
