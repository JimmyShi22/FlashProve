-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/KeyPiecesC.lean: pieces 16 to 23 of the 32 of «key 0» at rowsW's written values,
each walked call by call with the rest of the written rounds handed on (`pieceD`,
Johnson/AtFull/Rows/Slice.lean): from the table's state in front of it (`tabK3`, AtK3.lean) it ends
at the next, and its calls' rounds are, by `sameAll`, the written rounds between the two places.
CLOSED FACTS, by evaluation in Lean's kernel alone (`decide +kernel`): no compiled code is trusted;
one a piece. A law file; no running text imports it. Made by program from one template.
  `pieceK_16`: the second lookup's head: places 9586 to 9735.
  `pieceK_17`: product tree 1 of the second lookup's twelve: places 9735 to 10470.
  `pieceK_18`: product tree 2 of the second lookup's twelve: places 10470 to 11205.
  `pieceK_19`: product tree 3 of the second lookup's twelve: places 11205 to 11940.
  `pieceK_20`: product tree 4 of the second lookup's twelve: places 11940 to 12675.
  `pieceK_21`: product tree 5 of the second lookup's twelve: places 12675 to 13410.
  `pieceK_22`: product tree 6 of the second lookup's twelve: places 13410 to 14145.
  `pieceK_23`: product tree 7 of the second lookup's twelve: places 14145 to 14880.

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

theorem pieceK_16 :
    pieceD sW (kW 0).rounds (tabK3 16) ((key0Pieces cW).getD 16 (pure ())) =
      some (tabK3 (16 + 1)) := by decide +kernel

theorem pieceK_17 :
    pieceD sW (kW 0).rounds (tabK3 17) ((key0Pieces cW).getD 17 (pure ())) =
      some (tabK3 (17 + 1)) := by decide +kernel

theorem pieceK_18 :
    pieceD sW (kW 0).rounds (tabK3 18) ((key0Pieces cW).getD 18 (pure ())) =
      some (tabK3 (18 + 1)) := by decide +kernel

theorem pieceK_19 :
    pieceD sW (kW 0).rounds (tabK3 19) ((key0Pieces cW).getD 19 (pure ())) =
      some (tabK3 (19 + 1)) := by decide +kernel

theorem pieceK_20 :
    pieceD sW (kW 0).rounds (tabK3 20) ((key0Pieces cW).getD 20 (pure ())) =
      some (tabK3 (20 + 1)) := by decide +kernel

theorem pieceK_21 :
    pieceD sW (kW 0).rounds (tabK3 21) ((key0Pieces cW).getD 21 (pure ())) =
      some (tabK3 (21 + 1)) := by decide +kernel

theorem pieceK_22 :
    pieceD sW (kW 0).rounds (tabK3 22) ((key0Pieces cW).getD 22 (pure ())) =
      some (tabK3 (22 + 1)) := by decide +kernel

theorem pieceK_23 :
    pieceD sW (kW 0).rounds (tabK3 23) ((key0Pieces cW).getD 23 (pure ())) =
      some (tabK3 (23 + 1)) := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pieceK_16
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_17
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_18
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_19
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_20
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_21
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_22
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_23
