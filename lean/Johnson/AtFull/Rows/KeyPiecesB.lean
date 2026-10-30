-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/KeyPiecesB.lean: pieces 8 to 15 of the 32 of «key 0» at rowsW's written values,
each walked call by call with the rest of the written rounds handed on (`pieceD`,
Johnson/AtFull/Rows/Slice.lean): from the table's state in front of it (`tabK3`, AtK3.lean) it ends
at the next, and its calls' rounds are, by `sameAll`, the written rounds between the two places.
CLOSED FACTS, by evaluation in Lean's kernel alone (`decide +kernel`): no compiled code is trusted;
one a piece. A law file; no running text imports it. Made by program from one template.
  `pieceK_08`: product tree 6 of the first lookup's twelve: places 4027 to 4801.
  `pieceK_09`: product tree 7 of the first lookup's twelve: places 4801 to 5575.
  `pieceK_10`: product tree 8 of the first lookup's twelve: places 5575 to 6349.
  `pieceK_11`: product tree 9 of the first lookup's twelve: places 6349 to 7123.
  `pieceK_12`: product tree 10 of the first lookup's twelve: places 7123 to 7897.
  `pieceK_13`: product tree 11 of the first lookup's twelve: places 7897 to 8671.
  `pieceK_14`: product tree 12 of the first lookup's twelve: places 8671 to 9445.
  `pieceK_15`: the first lookup's end: places 9445 to 9586.

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

theorem pieceK_08 :
    pieceD sW (kW 0).rounds (tabK3 8) ((key0Pieces cW).getD 8 (pure ())) =
      some (tabK3 (8 + 1)) := by decide +kernel

theorem pieceK_09 :
    pieceD sW (kW 0).rounds (tabK3 9) ((key0Pieces cW).getD 9 (pure ())) =
      some (tabK3 (9 + 1)) := by decide +kernel

theorem pieceK_10 :
    pieceD sW (kW 0).rounds (tabK3 10) ((key0Pieces cW).getD 10 (pure ())) =
      some (tabK3 (10 + 1)) := by decide +kernel

theorem pieceK_11 :
    pieceD sW (kW 0).rounds (tabK3 11) ((key0Pieces cW).getD 11 (pure ())) =
      some (tabK3 (11 + 1)) := by decide +kernel

theorem pieceK_12 :
    pieceD sW (kW 0).rounds (tabK3 12) ((key0Pieces cW).getD 12 (pure ())) =
      some (tabK3 (12 + 1)) := by decide +kernel

theorem pieceK_13 :
    pieceD sW (kW 0).rounds (tabK3 13) ((key0Pieces cW).getD 13 (pure ())) =
      some (tabK3 (13 + 1)) := by decide +kernel

theorem pieceK_14 :
    pieceD sW (kW 0).rounds (tabK3 14) ((key0Pieces cW).getD 14 (pure ())) =
      some (tabK3 (14 + 1)) := by decide +kernel

theorem pieceK_15 :
    pieceD sW (kW 0).rounds (tabK3 15) ((key0Pieces cW).getD 15 (pure ())) =
      some (tabK3 (15 + 1)) := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pieceK_08
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_09
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_10
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_11
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_12
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_13
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_14
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_15
