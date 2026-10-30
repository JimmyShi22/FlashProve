-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndPortUnit.lean: in the world that the committed entries give at a state of the
verifier (`portWorld`, OnBytes/Tie/Pv/Led/LedPort.lean), an entry of the first virtual row of a
table's vector is the committed cell itself.

Theorems with their proofs.

Main names:
  `portWorld_unit`: entry i of the first virtual row of an array of one row with the weight 1 is
    cell (0, i).
  `portWorld_unitAt`: the same at a place pos below the number K of columns, written as the claims
    write it: virtual row pos / K, index pos % K.

Limits: the premises of OnBytes/Tie/Pv/Tail/EndPort.lean and EndRaw.lean (`RowsBelow`, `UnitRow`)
stay. At a place from K on nothing is said: such a place names a virtual row that the vector does
not have.


-/
import OnBytes.Tie.Pv.Tail.EndPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows Finset

variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J)

/-- An entry of the first virtual row of an array of one row with the weight 1 is the cell. -/
theorem portWorld_unit (F : Fork) (m : J → K) (t : Nat) (h : RowsBelow Y F t) (hu : UnitRow F t)
    (i : Nat) : (portWorld ρ Y F m).entry t 0 i = Y.cellAt m t 0 i := by
  rw [portWorld_row ρ Y F m t 0 h i, hu.1]
  simp only [Finset.sum_range_one, hu.2, ρ.one, one_mul]

/-- The same at a place below the number of columns, as the claims write it. -/
theorem portWorld_unitAt (F : Fork) (m : J → K) (t : Nat) (h : RowsBelow Y F t)
    (hu : UnitRow F t) (cols pos : Nat) (hp : pos < cols) :
    (portWorld ρ Y F m).entry t (pos / cols) (pos % cols) =
      Y.cellAt m t (pos / cols) (pos % cols) := by
  rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
  exact portWorld_unit ρ Y F m t h hu pos

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.portWorld_unitAt
