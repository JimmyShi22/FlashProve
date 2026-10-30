-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Behind.lean: a test on the verifier's state BEHIND the block that draws the
batching element, asked from the state IN FRONT OF that block and the block's own challenges. ONE
DEFINITION, WITH CODE. NO THEOREM.

  `askBehind batch test s ds`   batch: the block's decision, at rounds as a view shows them. The
      block's round sends nothing: its view is the challenge alone. The decision is run from s at
      the challenges ds, and the test is asked of the state behind it.
Limits. Where the block's decision refuses the answer is false: such challenges are another set's
matter.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest

/-- The block's decision is run from s at its own challenges, and a test is asked of the state
behind it. Where the block refuses: false. -/
def askBehind (batch : S → List Fmt.RoundView → Except String S) (test : S → Bool) (s : S)
    (ds : List Fmt.Drawn) : Bool :=
  match batch s (ds.map fun d => ⟨[], d⟩) with
  | .ok t => test t
  | .error _ => false

end VerifiableInference.Desc.First.K8.Honest
