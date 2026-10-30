-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/TestsAtSLaw.lean: BESIDE Johnson/Desc/First/Batch/TestsAtS.lean, NO PART OF
THE DESCRIPTION: that file's own test on the list of tables is the program `verify-on-bytes`'s test
of that meaning. No Mathlib.
Limits: one equation of two tests. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.TestsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- OnBytes/Model/Tail.lean:653-655, at every record and every list. -/
theorem closedList_eq (tl : HTailF2) (funs : Array HFun) : closedList tl funs = tl.funsHeld funs :=
  rfl

end VerifiableInference.Desc.K9
