-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/Layout/Pieces.lean: the fourteen written pieces of the stored full-size layout
file's bytes (Johnson/Unfolds/Layout/P01.lean … P14.lean: 400 lines a piece, the last 319; each ends
in a line feed), as one list of lists; and three closed facts by Lean's checker: every byte is below
128; each piece ends in a line feed; the bytes number 224,975.
Definitions and closed facts. That the pieces joined are the file's bytes:
AtFullSide/Layout/Tie.lean (a side library outside the main library). THE COST, MEASURED ON ONE
MACHINE: some two minutes and about 6 GB resident.
-/
import Johnson.Unfolds.Layout.P01
import Johnson.Unfolds.Layout.P02
import Johnson.Unfolds.Layout.P03
import Johnson.Unfolds.Layout.P04
import Johnson.Unfolds.Layout.P05
import Johnson.Unfolds.Layout.P06
import Johnson.Unfolds.Layout.P07
import Johnson.Unfolds.Layout.P08
import Johnson.Unfolds.Layout.P09
import Johnson.Unfolds.Layout.P10
import Johnson.Unfolds.Layout.P11
import Johnson.Unfolds.Layout.P12
import Johnson.Unfolds.Layout.P13
import Johnson.Unfolds.Layout.P14

namespace Johnson.Unfolds.Layout

/-- **The fourteen pieces.** -/
def pieces : List (List UInt8) :=
  [p01, p02, p03, p04, p05, p06, p07, p08, p09, p10, p11, p12, p13, p14]

/-- Every byte of every piece is below 128. -/
theorem pieces_ascii : (pieces.all fun p => p.all (· < 128)) = true := by decide +kernel

/-- Each piece ends in a line feed. -/
theorem pieces_end : (pieces.all fun p => p.getLast? == some 10) = true := by decide +kernel

/-- The number of bytes. -/
theorem pieces_length : (pieces.map (·.length)).sum = 224975 := by decide +kernel

end Johnson.Unfolds.Layout

#print axioms Johnson.Unfolds.Layout.pieces_ascii
#print axioms Johnson.Unfolds.Layout.pieces_end
#print axioms Johnson.Unfolds.Layout.pieces_length
