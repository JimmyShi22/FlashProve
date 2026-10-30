-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/FinalCompleteValue.lean: completeness of the compiled system at the honest part.

 1. finalComplete_value: FinalComplete honestProversAndSettings, the line `complete` of the final statement.
 2. The proof reads that field of theFinalStatementHolds and does nothing else. What the theorem is
    worth is what theFinalStatementHolds is worth, and the limits in that file's head go with every
    use. It is about honestProversAndSettings exactly as written, stand-in values included.
-/
import AtFullSide.Face.TheFinalStatementHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation

/-- **Completeness, of the honest part**: at public files in use, at every well-formed request whose
claimed output is the model's result; nothing where the model has no result. -/
theorem finalComplete_value : FinalComplete honestProversAndSettings :=
  theFinalStatementHolds.complete

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalComplete_value
