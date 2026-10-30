-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3NumC.lean: THE LOT OF THE KIND "LOOKUP": CLOSED FACTS BY LEAN's KERNEL AT
THE WRITTEN VALUES (K3Written.lean): AT THE LOOKUPS ON THE CALLS, THE TABLES TAKEN OUT: the planner
makes the written number of rounds, and the plan's tests (K3.planOk, Law.fitsVia) accept. One
theorem a sort of segment.
Limits. Facts on written values. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Written

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Lots.K3

theorem num_c0 : numOf (coreW 0 false) (pubW 0 false) = (nW 0 false, true) := by decide +kernel
theorem num_c1 : numOf (coreW 1 false) (pubW 1 false) = (nW 1 false, true) := by decide +kernel
theorem num_c2 : numOf (coreW 2 false) (pubW 2 false) = (nW 2 false, true) := by decide +kernel
theorem num_c3 : numOf (coreW 3 false) (pubW 3 false) = (nW 3 false, true) := by decide +kernel

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.num_c0
#print axioms Johnson.AtFull.Lots.K3.num_c1
#print axioms Johnson.AtFull.Lots.K3.num_c2
#print axioms Johnson.AtFull.Lots.K3.num_c3
