-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/TestPendingPort.lean: the hypothesis StretchMeans of
Johnson/Road/Rows/PendingPort.lean, evaluated for every stretch in small cubes.

For each number of row bits from 0 to 5, each first row and each length that fits the cube, with
made-up values: stretchInTheCube (OnBytes/Iop/Lin.lean) returns a list of vectors, and at each row
of the cube their entries add up to the value written for that row, and to 0 outside the stretch.
The sum is taken in the verifier's field; StretchMeans speaks of its reading in a field.

Every line "#guard" is evaluated when this file is compiled. It is a run and no theorem, and it
speaks of these numbers alone.

A control that must fail: the values read one row further. The last two lines print on which axioms
the proof of StretchMeans (Johnson/Road/Rows/StretchLaws.lean) and what follows from it rest.


-/
import Johnson.Road.Rows.StretchLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

/-- True if, for all stretches in the cube of 2^kRow rows, the vectors of stretchInTheCube add up to
the made-up values, read shift rows further. -/
def stretchToy (shift kRow : ℕ) : Bool :=
  (List.range (2 ^ kRow + 1)).all fun first =>
    (List.range (2 ^ kRow - first + 1)).all fun size =>
      let values : Array E := (Array.range size).map fun i => Model.ofNat (7 + 3 * i + 11 * first)
      match stretchInTheCube kRow first values with
      | none => false
      | some g =>
        (List.range (2 ^ kRow)).all fun j =>
          g.foldl (fun s t => addE s (t.entry j)) zeroE ==
            if first ≤ j ∧ j < first + size then values.getD (j - first + shift) zeroE else zeroE

/- the hypothesis holds for every stretch in the cubes of 1 to 32 rows -/
#guard (List.range 6).all (stretchToy 0)

/- the control -/
#guard !stretchToy 1 3

/- a stretch that reaches past the cube gets no answer, so the hypothesis says nothing of it -/
#guard (List.range 9).all fun first =>
  (stretchInTheCube 3 first (Array.replicate (2 ^ 3 - first + 1) oneE)).isNone

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.stretchMeans
#print axioms OnBytes.Road.Rows.pending_port_free
