-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/LayoutRead/Piece02.lean: piece 2 of 14 of the stored full-size layout file (lines 401
to 800; 16039 bytes): THE PIECE's CLOSED FACT, by Lean's kernel: at the written bytes
Johnson.Unfolds.Layout.p02 the layout file's reader's routines return the written value v02
(Values/V02.lean), and the piece ends in a line feed. One theorem. Made by program.
Limits. Of the bytes it says what the reader returns at them, no more. Nothing on soundness.

-/
import Johnson.AtFull.LayoutRead.Pieces
import Johnson.AtFull.LayoutRead.Values.V02
import Johnson.Unfolds.Layout.P02

set_option autoImplicit false

namespace Johnson.AtFull.LayoutRead

/-- **The piece's closed fact.** -/
theorem piece02 : PieceIs Johnson.Unfolds.Layout.p02 v02 :=
  pieceIs_of_test (by decide +kernel)

end Johnson.AtFull.LayoutRead

#print axioms Johnson.AtFull.LayoutRead.piece02
