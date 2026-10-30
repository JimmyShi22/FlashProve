-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/KeyPiecesA.lean: pieces 0 to 7 of the 32 of «key 0» at rowsW's written values,
each walked call by call with the rest of the written rounds handed on (`pieceD`,
Johnson/AtFull/Rows/Slice.lean): from the table's state in front of it (`tabK3`, AtK3.lean) it ends
at the next, and its calls' rounds are, by `sameAll`, the written rounds between the two places.
CLOSED FACTS, by evaluation in Lean's kernel alone (`decide +kernel`): no compiled code is trusted;
one a piece. A law file; no running text imports it. Made by program from one template.
  `pieceK_00`: the two first notes: places 0 to 3.
  `pieceK_01`: the head of the proof of the ranges: places 3 to 5.
  `pieceK_02`: the first lookup's head: places 5 to 157.
  `pieceK_03`: product tree 1 of the first lookup's twelve: places 157 to 931.
  `pieceK_04`: product tree 2 of the first lookup's twelve: places 931 to 1705.
  `pieceK_05`: product tree 3 of the first lookup's twelve: places 1705 to 2479.
  `pieceK_06`: product tree 4 of the first lookup's twelve: places 2479 to 3253.
  `pieceK_07`: product tree 5 of the first lookup's twelve: places 3253 to 4027.

Limits. At the written values alone. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.AtK3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

theorem pieceK_00 :
    pieceD sW (kW 0).rounds (tabK3 0) ((key0Pieces cW).getD 0 (pure ())) =
      some (tabK3 (0 + 1)) := by decide +kernel

theorem pieceK_01 :
    pieceD sW (kW 0).rounds (tabK3 1) ((key0Pieces cW).getD 1 (pure ())) =
      some (tabK3 (1 + 1)) := by decide +kernel

theorem pieceK_02 :
    pieceD sW (kW 0).rounds (tabK3 2) ((key0Pieces cW).getD 2 (pure ())) =
      some (tabK3 (2 + 1)) := by decide +kernel

theorem pieceK_03 :
    pieceD sW (kW 0).rounds (tabK3 3) ((key0Pieces cW).getD 3 (pure ())) =
      some (tabK3 (3 + 1)) := by decide +kernel

theorem pieceK_04 :
    pieceD sW (kW 0).rounds (tabK3 4) ((key0Pieces cW).getD 4 (pure ())) =
      some (tabK3 (4 + 1)) := by decide +kernel

theorem pieceK_05 :
    pieceD sW (kW 0).rounds (tabK3 5) ((key0Pieces cW).getD 5 (pure ())) =
      some (tabK3 (5 + 1)) := by decide +kernel

theorem pieceK_06 :
    pieceD sW (kW 0).rounds (tabK3 6) ((key0Pieces cW).getD 6 (pure ())) =
      some (tabK3 (6 + 1)) := by decide +kernel

theorem pieceK_07 :
    pieceD sW (kW 0).rounds (tabK3 7) ((key0Pieces cW).getD 7 (pure ())) =
      some (tabK3 (7 + 1)) := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pieceK_00
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_01
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_02
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_03
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_04
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_05
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_06
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_07
