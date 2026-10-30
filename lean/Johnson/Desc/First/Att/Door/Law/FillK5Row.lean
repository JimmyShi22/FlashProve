-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/FillK5Row.lean: TOWARD A MEMBER: K5FillRel.row (Johnson/Desc/First/Att/K05Riders.lean: "the open segment's classes of rows ride back over the kind's lay") AT THE LAYER FOR THE ITEM row (fillRowFirst, Johnson/Desc/First/Close/Law/FillRowFirst.lean): what that item says reads of the record the statement and the book alone, which the lay leaves: BY THE MAKE. The layer is taken by the one equation that it pays by rfl (fillRowFirst_row). Mathlib beneath.
import Johnson.Desc.First.Att.Door.FillK5
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.Desc.First.Att.K05BehindLay

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (behind Heard)
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.Sound (MsgT)

theorem at_row {Pp Cells Tok : Type} (d : K5Data) (Mg1 : Meaning Pp (Wit Cells Tok MsgT)) (π : Pp) (arr : Nat → Nat → Nat)
    (N : Numbers) (hrow : Mg1.row = rowSays N (wordsAtFirst arr)) (n : Nat) (c : RowClass) (s : S) (a : AttOwn) (h : Heard)
    (G : Fork) (y y' : Strs) (w : Wit Cells Tok MsgT) :
    (fillK5 d Mg1).row n c (π, behind s a h G) y' w → (fillK5 d Mg1).row n c (π, s) y w := by
  show Mg1.row n c _ _ _ → Mg1.row n c _ _ _
  rw [hrow]
  exact fun x => x

#print axioms at_row

end H2K5.Door
