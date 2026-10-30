-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/LayoutRead/PiecesAre.lean: EACH OF THE FOURTEEN WRITTEN PIECES OF THE STORED
FULL-SIZE LAYOUT FILE (Johnson.Unfolds.Layout.pieces) HAS ITS CLOSED FACT (Piece01.lean to
Piece14.lean), AS ONE STATEMENT; and what the layout file's reader's routines return at the pieces
joined. Three theorems: calls.

  `LW_row`: the written value LW (Values/All.lean) is the fourteen values in a row, in Pieces.lean's
    word rowOf.
  **`pieces_are`** : List.Forall₂ PieceIs Johnson.Unfolds.Layout.pieces values.
  `gather_full`: so the routines at the pieces joined return LW, in the file's order.
Limits. That the pieces joined are the stored file's bytes is not used here (Full.lean). Nothing on
soundness.

-/
import Johnson.AtFull.LayoutRead.Piece01
import Johnson.AtFull.LayoutRead.Piece02
import Johnson.AtFull.LayoutRead.Piece03
import Johnson.AtFull.LayoutRead.Piece04
import Johnson.AtFull.LayoutRead.Piece05
import Johnson.AtFull.LayoutRead.Piece06
import Johnson.AtFull.LayoutRead.Piece07
import Johnson.AtFull.LayoutRead.Piece08
import Johnson.AtFull.LayoutRead.Piece09
import Johnson.AtFull.LayoutRead.Piece10
import Johnson.AtFull.LayoutRead.Piece11
import Johnson.AtFull.LayoutRead.Piece12
import Johnson.AtFull.LayoutRead.Piece13
import Johnson.AtFull.LayoutRead.Piece14
import Johnson.AtFull.LayoutRead.Values.All
import Johnson.Unfolds.Layout.Pieces

set_option autoImplicit false

namespace Johnson.AtFull.LayoutRead
open OnBytes.Plan

/-- The written value is the fourteen values in a row. -/
theorem LW_row : LW = rowOf values := rfl

/-- **Each written piece has its closed fact.** -/
theorem pieces_are : List.Forall₂ PieceIs Johnson.Unfolds.Layout.pieces values :=
  .cons piece01 <|
  .cons piece02 <|
  .cons piece03 <|
  .cons piece04 <|
  .cons piece05 <|
  .cons piece06 <|
  .cons piece07 <|
  .cons piece08 <|
  .cons piece09 <|
  .cons piece10 <|
  .cons piece11 <|
  .cons piece12 <|
  .cons piece13 <|
  .cons piece14 <|
  .nil

/-- The reader's routines at the pieces joined. -/
theorem gather_full :
    (gatherLines (linesOf Johnson.Unfolds.Layout.pieces.flatten) {}).map rev2 = some LW := by
  rw [LW_row]
  exact gather_pieces _ _ pieces_are

end Johnson.AtFull.LayoutRead

#print axioms Johnson.AtFull.LayoutRead.LW_row
#print axioms Johnson.AtFull.LayoutRead.pieces_are
#print axioms Johnson.AtFull.LayoutRead.gather_full
