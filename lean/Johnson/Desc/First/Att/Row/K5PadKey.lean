-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5PadKey.lean: THE VALUE OF A CALL's PADDING KEY, OFF THE TABLE's OWN
DEFINITION. CallG.padKey (Johnson/Desc/First/Att/Geo.lean) reads one entry, number t0, of the call's
table of public row values. The attention's tables are made by OnBytes.Attention.tableOf k row
(OnBytes/Model/AttentionShape.lean): the array of row t for t below 2 ^ k, at k = 16 an array of
65,536 entries. These two laws give the padding key without that array. General; nothing is
evaluated; no value is named.

Main names (namespace H2K5.Row):
  padKey_tableOf: where the call's table is tableOf k row and t0 lies below 2 ^ k: the padding key
    is UInt64.ofNat (row c.t0).
  padKey_none: where the call has no table (row t has the value t): the padding key is t0.
WHY. A closed test on an attention segment's numbers that reads padKey was ended at a bound on
memory, without a verdict, when it was put to Lean's kernel; that the whole table is built for its
one entry is one of two guesses, neither shown. The laws serve under either.
BESIDE IT: the general fact on an entry of (Array.range n).map f stands in the library twice, each
by one simp (OnBytes.Slice.getD_map_range, OnBytes/Slice/BlkCsRows.lean;
OnBytes.Tie.Pv.Tail.Port.getD_map_range, OnBytes/Tie/Pv/Tail/EndClaimsB.lean), each in a file with
many imports. Here the same simp stands inside the proof: no third named copy.
Limits. That a given call's table IS tableOf k row, and that its t0 lies below 2 ^ k, are premises:
a law on the maker of the calls, by kind, would pay them; it is not here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GeoOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open VerifiableInference.Desc.First.Att.P (CallG)
open OnBytes.Attention (tableOf)

/-- **The padding key off the table's own definition.** -/
theorem padKey_tableOf (c : CallG) {k : Nat} {row : Nat → Nat} (h : c.tau = tableOf k row)
    (ht : c.t0 < 2 ^ k) : c.padKey = UInt64.ofNat (row c.t0) := by
  unfold CallG.padKey
  rw [h]
  simp [tableOf, Array.getD, ht]

/-- A call without a table: row t has the value t. -/
theorem padKey_none (c : CallG) (h : c.tau = none) : c.padKey = c.t0.toUInt64 := by
  unfold CallG.padKey
  rw [h]

end H2K5.Row

#print axioms H2K5.Row.padKey_tableOf
#print axioms H2K5.Row.padKey_none
