-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeLengthsLit.lean: code switching: THE PREMISE hL OF hAt_at_place AND
ITS THREE ARMS (Tw/K2C/TieThreeAt.lean · TieThreeArms.lean), r.cs.lengthsOk = true, AT EVERY ENTRY
OF THE TWO WRITTEN TABLES (tableFullLit · tableSmallLit, K2Caller/LitRows.lean): by Lean's kernel.
Two closed facts and what they give at an entry (from tableFullLit[i]? = some r:
List.mem_of_getElem?). NO SUB-PROTOCOL IMPORTS THIS FILE.
LIMITS. Of the written tables alone: that they are those of the program that makes the list of
rounds is held by other tests. No soundness is claimed. On hiding nothing.
-/
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller

set_option maxRecDepth 1000000 in
theorem lengthsOk_full : (tableFullLit.all fun r => r.cs.lengthsOk) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem lengthsOk_small : (tableSmallLit.all fun r => r.cs.lengthsOk) = true := by decide +kernel

/-- **hL at an entry of the full size's written table.** -/
theorem hL_full {r : SwRow} (h : r ∈ tableFullLit) : r.cs.lengthsOk = true :=
  List.all_eq_true.1 lengthsOk_full r h

/-- **hL at an entry of the small size's written table.** -/
theorem hL_small {r : SwRow} (h : r ∈ tableSmallLit) : r.cs.lengthsOk = true :=
  List.all_eq_true.1 lengthsOk_small r h

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.lengthsOk_full
#print axioms VerifiableInference.Desc.First.K2Caller.lengthsOk_small
#print axioms VerifiableInference.Desc.First.K2Caller.hL_full
#print axioms VerifiableInference.Desc.First.K2Caller.hL_small
