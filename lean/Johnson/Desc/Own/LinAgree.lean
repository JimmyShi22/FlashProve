-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/LinAgree.lean: the tests of Johnson/Desc/Own/Lin.lean say just what the
hand-written program's say, at all arguments, without a premise. Theorems. No block imports this
file.

  twoPower_eq · lengthsFit_eq · shapeSound_eq · codeFits_eq · indexFits_eq · foldeqShapeFits_eq ·
  foldFits_eq · splitMessageFits_eq · vectorMessageFits_eq · linShapeFits_eq · linFits_eq:
  own = the program's.
What is not claimed. That the tests ask enough. Nothing on soundness.

-/
import Johnson.Desc.Own.Lin
import Johnson.Desc.Own.RoomMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Params

theorem twoPower_eq (n : Nat) : twoPower n = powerOfTwo n := rfl

theorem lengthsFit_eq (c : Codes) : lengthsFit c = c.lengthsOk := rfl

theorem shapeSound_eq (s : OracleShape) : shapeSound s = shapeFaultless s := rfl

theorem codeFits_eq (c : Code) : codeFits c = c.ok := rfl

theorem indexFits_eq (s : IndexShape) : indexFits s = s.ok := rfl

theorem foldeqShapeFits_eq (S : FoldeqShape) : foldeqShapeFits S = S.ok := rfl

theorem foldFits_eq (codes : Codes) (S : FoldeqShape) : foldFits codes S = foldeqOk codes S := by
  unfold foldFits foldeqOk
  rw [roomOf_eq, foldeqShapeFits_eq]

theorem splitMessageFits_eq (o : OracleShape) (maskCode : Nat) :
    splitMessageFits o maskCode = LinShape.splitMessageOk o maskCode := rfl

theorem vectorMessageFits_eq (o : OracleShape) :
    vectorMessageFits o = LinShape.vectorMessageOk o := rfl

theorem linShapeFits_eq (S : LinShape) : linShapeFits S = S.ok := rfl

theorem linFits_eq (codes : Codes) (S : LinShape) : linFits codes S = linOk codes S := by
  unfold linFits linOk
  rw [roomOf_eq, roomOf_eq, foldFits_eq, linShapeFits_eq]

end VerifiableInference.Desc.Own
