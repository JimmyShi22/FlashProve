-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/KeyPiecesD.lean: pieces 24 to 31 of the 32 of «key 0» at rowsW's written values,
each walked call by call with the rest of the written rounds handed on (`pieceD`,
Johnson/AtFull/Rows/Slice.lean): from the table's state in front of it (`tabK3`, AtK3.lean) it ends
at the next, and its calls' rounds are, by `sameAll`, the written rounds between the two places.
CLOSED FACTS, by evaluation in Lean's kernel alone (`decide +kernel`): no compiled code is trusted;
one a piece. A law file; no running text imports it. Made by program from one template.
  `pieceK_24`: product tree 8 of the second lookup's twelve: places 14880 to 15615.
  `pieceK_25`: product tree 9 of the second lookup's twelve: places 15615 to 16350.
  `pieceK_26`: product tree 10 of the second lookup's twelve: places 16350 to 17085.
  `pieceK_27`: product tree 11 of the second lookup's twelve: places 17085 to 17820.
  `pieceK_28`: product tree 12 of the second lookup's twelve: places 17820 to 18555.
  `pieceK_29`: the second lookup's end: places 18555 to 18806.
  `pieceK_30`: the end of the proof of the ranges: places 18806 to 18849.
  `pieceK_31`: the end of «key 0»: places 18849 to 18852.

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

theorem pieceK_24 :
    pieceD sW (kW 0).rounds (tabK3 24) ((key0Pieces cW).getD 24 (pure ())) =
      some (tabK3 (24 + 1)) := by decide +kernel

theorem pieceK_25 :
    pieceD sW (kW 0).rounds (tabK3 25) ((key0Pieces cW).getD 25 (pure ())) =
      some (tabK3 (25 + 1)) := by decide +kernel

theorem pieceK_26 :
    pieceD sW (kW 0).rounds (tabK3 26) ((key0Pieces cW).getD 26 (pure ())) =
      some (tabK3 (26 + 1)) := by decide +kernel

theorem pieceK_27 :
    pieceD sW (kW 0).rounds (tabK3 27) ((key0Pieces cW).getD 27 (pure ())) =
      some (tabK3 (27 + 1)) := by decide +kernel

theorem pieceK_28 :
    pieceD sW (kW 0).rounds (tabK3 28) ((key0Pieces cW).getD 28 (pure ())) =
      some (tabK3 (28 + 1)) := by decide +kernel

theorem pieceK_29 :
    pieceD sW (kW 0).rounds (tabK3 29) ((key0Pieces cW).getD 29 (pure ())) =
      some (tabK3 (29 + 1)) := by decide +kernel

theorem pieceK_30 :
    pieceD sW (kW 0).rounds (tabK3 30) ((key0Pieces cW).getD 30 (pure ())) =
      some (tabK3 (30 + 1)) := by decide +kernel

theorem pieceK_31 :
    pieceD sW (kW 0).rounds (tabK3 31) ((key0Pieces cW).getD 31 (pure ())) =
      some (tabK3 (31 + 1)) := by decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pieceK_24
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_25
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_26
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_27
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_28
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_29
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_30
#print axioms VerifiableInference.Desc.LinkJoin.pieceK_31
