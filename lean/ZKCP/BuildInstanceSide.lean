-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/BuildInstanceSide.lean: the verifier of `Arg.buildInstance` (ZKCP/BuildInstance.lean) as a
function of its own.

Why. `Arg.buildInstance` makes a whole scheme, with the committer and the honest prover. The
verifier written out in Johnson/Top/InputV.lean needs that scheme's verifier alone.
Main name: `verifyBuilt`.
The tie (`Arg.buildInstance_V`): the field V of `Arg.buildInstance` is `verifyBuilt`. The proof of
`innerCompiledVerifier_eq` (Johnson/Top/InnerCompiledVerifierSide.lean) rests on it. If one of the two copies is changed
alone, this file no longer compiles: do not drop the tie in a clean-up.
Limits: one definition and this equation. Nothing on soundness.

-/
import ZKCP.BuildInstance

set_option autoImplicit false
open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X X' Aux W PP IVK ISK Pf : Type}

/-- The verifier on instances of another type: it builds V's instance from the new instance and the
first part of the proof, and rejects where none is built. -/
def verifyBuilt (V : IVK → X → Pf → OComp lam Bool) (build : X' → Aux → Option X) :
    IVK → X' → Aux × Pf → OComp lam Bool := fun key x' proof =>
  match build x' proof.1 with
  | some x => V key x proof.2
  | none => .pure false

/-! ## The tie -/

/-- The verifier of the scheme on instances of another type is `verifyBuilt`. -/
theorem Arg.buildInstance_V (A : Arg lam I X W IVK ISK Pf) (build : X' → Aux → Option X)
    (aux : X' → Aux) (π₀ : Pf) : (A.buildInstance build aux π₀).V = verifyBuilt A.V build := rfl

end ZKCP

#print axioms ZKCP.Arg.buildInstance_V
