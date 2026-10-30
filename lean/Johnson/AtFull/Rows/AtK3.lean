-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/AtK3.lean: THE TABLE OF THE PIECES OF «key 0» AT rowsW's WRITTEN VALUES: its 32
pieces (`key0Pieces`, Johnson/AtFull/Rows/CutKey.lean). Definitions alone. A law file; no running
text imports it.
  `placesK3`: 33 places in the written rounds of «key 0»: place i is where piece i begins; the last
    is the end.
  `tabK3 i`: the state in front of piece i: the scope «once», the three counters 0, and place i.
Whence: an evaluator's print of the walk piece by piece, which printed behind each piece the whole
small state (at each of the 32: once · 0 · 0 · 0) and the place; pasted by program. The sheet is
not in this repository (its sum db1af6dd011f621f…; its print's fcc56b3153676a7b…). Each entry is
held by Lean's kernel in the piece's own closed fact.

Limits. Nothing is proved here.
-/
import Johnson.AtFull.Rows.CutKey
import Johnson.AtFull.Rows.AtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

def placesK3 : List Nat :=
  [0, 3, 5, 157, 931, 1705, 2479, 3253, 4027, 4801, 5575, 6349,
    7123, 7897, 8671, 9445, 9586, 9735, 10470, 11205, 11940, 12675, 13410,
    14145, 14880, 15615, 16350, 17085, 17820, 18555, 18806, 18849, 18852]

def tabK3 (i : Nat) : SmallSt × Nat := (⟨.once, 0, 0, 0⟩, placesK3.getD i 0)

end VerifiableInference.Desc.LinkJoin
