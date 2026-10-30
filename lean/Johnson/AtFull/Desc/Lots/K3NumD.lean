-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3NumD.lean: THE LOT OF THE KIND "LOOKUP": CLOSED FACTS BY LEAN's KERNEL AT
THE WRITTEN VALUES (K3Written.lean): AT THE LOOKUPS ON THE DIGITS: the planner makes the written
number of rounds, and the plan's tests (K3.planOk, Law.fitsVia) accept. One theorem a sort of
segment.
Limits. Facts on written values. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Written

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Lots.K3

theorem num_d0 : numOf (coreW 0 true) (pubW 0 true) = (nW 0 true, true) := by decide +kernel
theorem num_d1 : numOf (coreW 1 true) (pubW 1 true) = (nW 1 true, true) := by decide +kernel
theorem num_d2 : numOf (coreW 2 true) (pubW 2 true) = (nW 2 true, true) := by decide +kernel
theorem num_d3 : numOf (coreW 3 true) (pubW 3 true) = (nW 3 true, true) := by decide +kernel

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.num_d0
#print axioms Johnson.AtFull.Lots.K3.num_d1
#print axioms Johnson.AtFull.Lots.K3.num_d2
#print axioms Johnson.AtFull.Lots.K3.num_d3
