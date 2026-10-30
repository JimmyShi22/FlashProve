-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/GatePiece/P133.lean: one evaluation in Lean's kernel: the test pieceOK
(Johnson/Meaning/GateFine.lean) at piece 133 of 257. Some seconds. Made by program, one file for
each piece.
-/
import Johnson.Meaning.GateFine

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Meaning.Gate

theorem piece_133 : pieceOK 133 = true := by decide +kernel

end Meaning.Gate
