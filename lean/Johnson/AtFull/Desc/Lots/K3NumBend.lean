-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3NumBend.lean: THE LOT OF THE KIND "LOOKUP": NEGATIVE TESTS BY LEAN's
KERNEL, ONE FOR EACH OF THE EIGHT CLOSED FACTS OF K3NumC.lean AND K3NumD.lean: with the first number
of padding keys one higher than the host's count the plan's tests reject, at each sort of segment,
at the calls and at the digits. (Segment 0's calls: `num_bend`, K3Table.lean.)
Limits. Facts on written values. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Written

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Lots.K3

/-- The plan's tests at the written parameters, the first number of padding keys one higher. -/
def bentOk (s : Nat) (d : Bool) : Bool :=
  (numOf { coreW s d with pub := (pubW s d).modify 0 (· + 1) } (pubW s d)).2

theorem bend_c1 : bentOk 1 false = false := by decide +kernel
theorem bend_c2 : bentOk 2 false = false := by decide +kernel
theorem bend_c3 : bentOk 3 false = false := by decide +kernel
theorem bend_d0 : bentOk 0 true = false := by decide +kernel
theorem bend_d1 : bentOk 1 true = false := by decide +kernel
theorem bend_d2 : bentOk 2 true = false := by decide +kernel
theorem bend_d3 : bentOk 3 true = false := by decide +kernel

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.bend_c1
#print axioms Johnson.AtFull.Lots.K3.bend_c2
#print axioms Johnson.AtFull.Lots.K3.bend_c3
#print axioms Johnson.AtFull.Lots.K3.bend_d0
#print axioms Johnson.AtFull.Lots.K3.bend_d1
#print axioms Johnson.AtFull.Lots.K3.bend_d2
#print axioms Johnson.AtFull.Lots.K3.bend_d3
