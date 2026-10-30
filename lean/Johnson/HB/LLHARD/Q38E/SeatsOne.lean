-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38E/SeatsOne.lean: one closed fact on a written value: among the sampled entries
of the written list of the first chain's seats (`P5T.psFull`, Johnson/P5T/PlanSeatsFull.lean) no
seat stands twice.

Row or tool. A closed fact with a negative test and a count. For the law on the digits of the
sub-protocol K8: the condition `DigAheadOk` at the state behind the draw of the approximate range
proof. The same two declarations stand, under other full names, in Johnson/HB/LLHARD/K6MaskText.lean
(`P5J.memsW`, `P5J.seats_one`), a file on another sub-protocol: they are typed anew here so that
these files do not stand on that one.

What it spends. No row of the entry tests and no field of the head: it names written values alone.

What is here (namespace Q38).
  `memsW`: the sampled entries of `psFull`: of each its shape and its seat.
  `seats_one`: the list of their seats has no entry twice.
  `e_seats_rejects`: the negative test: with the first of them laid in front once more, it has.
  `e_seats_count`: there are 167 of them: so the fact is not true for want of entries.
By evaluations in Lean's kernel (`decide +kernel`): all three.

Limits. That the seats at given public files are `psFull` is not said here. Nothing on soundness.


-/
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes
open P5T (psFull)

/-- The sampled entries of the written list: of each its shape and its seat. -/
def memsW : List (OracleShape × (ℕ × ℕ)) :=
  (psFull.filter (·.smpd)).map fun p => (p.shape, p.seat)

set_option maxRecDepth 1000000 in
/-- **No seat stands twice among the sampled seats.** -/
theorem seats_one : (memsW.map (·.2)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test. -/
theorem e_seats_rejects : ¬ ((memsW.head?.toList ++ memsW).map (·.2)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are 167 of them. -/
theorem e_seats_count : memsW.length = 167 := by decide +kernel

end Q38

#print axioms Q38.seats_one
#print axioms Q38.e_seats_rejects
#print axioms Q38.e_seats_count
