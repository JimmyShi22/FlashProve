-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38A/SeatOfCellParts.lean: what a seat of a cell is made of.

  `seatOf_cell_parts`: from `seatOf D i (.cell t r c) = some z`
    (Johnson/Desc/First/Look/K3CallerBase.lean): the entry bn of segment i's list of arrays at t; it
    bears the segment's own number; the array A by the layout; the place rp of the cell in A's
    rectangles (`A.blocks`); and z is ⟨A.message, false, rp.1, rp.2⟩. An unfolding of that reader's
    text: a bind, a test, a bind and a map. So at every cell of one array the seat's message is one
    number.

Limits. General: no public file, no written value, no head of conditions is read. Nothing on
soundness.
-/
import Johnson.Desc.First.Look.K3CallerBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Sent Seat seatOf laidPlace)

/-- **What a seat of a cell is made of.** -/
theorem seatOf_cell_parts {D : Sent} {i t r c : ℕ} {z : Seat}
    (hz : seatOf D i (.cell t r c) = some z) :
    ∃ bn A rp, (D.arrayOf.getD i #[])[t]? = some bn ∧ bn.1 = i ∧
      reqArray D.layout i bn.2 = some A ∧ laidPlace A.blocks r c = some rp ∧
      z = ⟨A.message, false, rp.1, rp.2⟩ := by
  unfold seatOf at hz
  obtain ⟨bn, h1, hz⟩ := Option.bind_eq_some_iff.1 hz
  split at hz
  · rename_i hb
    obtain ⟨A, h2, hz⟩ := Option.bind_eq_some_iff.1 hz
    obtain ⟨rp, h3, hz⟩ := Option.map_eq_some_iff.1 hz
    exact ⟨bn, A, rp, h1, eq_of_beq hb, h2, h3, hz.symm⟩
  · exact nomatch hz

end Q38

#print axioms Q38.seatOf_cell_parts
