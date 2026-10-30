-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyStoredDecodes.lean: THEOREMS. **What is read off a boundary's strings, where their stored side is the stored table of a table M of full messages over the base field, decodes with M's true record to M's message parts: at every seed, at any other component of the strings.**
OBJECT: the library's decoder with a record at the full size, DF.dcd (Johnson/RunOne/KeyMemberTableFull.lean), at fun p => ((strsOf Fr y').cell p.val).getD (0, []): the body of other files' written decoder of the stored table off its cells, unfolded, at no name of theirs. USER: Johnson/RunOne/KeyPinwStored.lean calls stored_decodes (KeyPinwAtLetters.lean's premise hd). LETTERS: DK · M · ρ · y'.
WHICH DATA. D := DK.at frS.P.T.a: so that the frame's stored table has the decoder's length by unfolding.
  cells_are        what is read off the strings' cells is their stored side (general in the second component)
  stored_decodes   **the sentence above**
  stored_not_wrong a control: at a record whose answers are not M's at its seed the same term is not that value
What is not claimed. That any run lays such a table or record. «In range». No collision's chance. Nothing on soundness.

-/
import Johnson.RunOne.KeyMemberTableFull
import Johnson.RunOne.KeyRowsAtFk
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Maker OnBytes.Slice OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Johnson.RunOne.KeyRows23 (fr₁)

/-- What is read off the strings' cells is their stored side. -/
theorem cells_are (DK : WholeD) (y' : (fr₁ (DK.at frS.P.T.a)).E.Str) :
    (fun p : Fin (2 ^ frS.P.T.a) => ((strsOf (fr₁ (DK.at frS.P.T.a)) y').cell p.val).getD (0, [])) = y'.1 := by
  funext p
  show ((cellAt (fr₁ (DK.at frS.P.T.a)) y' p.val).getD (0, [])) = y'.1 p
  unfold cellAt
  rw [dif_pos p.isLt]
  rfl

/-- **The stored table, read off a boundary's strings, decodes with its true record.** -/
theorem stored_decodes (DK : WholeD) (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (ρ : DF.Z.D)
    (y' : (fr₁ (DK.at frS.P.T.a)).E.Str) (h : y'.1 = stored DF M) :
    DF.dcd (fun p => ((strsOf (fr₁ (DK.at frS.P.T.a)) y').cell p.val).getD (0, [])) (recOfM DF M ρ) = some (DF.ix.view (upM DF M)) := by
  have e := cells_are DK y'
  rw [h] at e
  exact (congrArg (fun f => DF.dcd f (recOfM DF M ρ)) e).trans (dcd_full M ρ).1

/-- A control: a record with other answers does not give that value. -/
theorem stored_not_wrong (DK : WholeD) (M : (Fin DF.v → Bool) → Fin (DF.T.r + DF.T.l) → GF) (rec : DF.Rec)
    (hw : DF.ix.ZR.val rec.1 (DF.ix.view (upM DF M)) ≠ rec.2) (y' : (fr₁ (DK.at frS.P.T.a)).E.Str) :
    DF.dcd (fun p => ((strsOf (fr₁ (DK.at frS.P.T.a)) y').cell p.val).getD (0, [])) rec ≠ some (DF.ix.view (upM DF M)) :=
  not_dcd_of_wrong_rec _ _ _ _ hw

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.cells_are
#print axioms Johnson.RunOne.KeyLetters.stored_decodes
#print axioms Johnson.RunOne.KeyLetters.stored_not_wrong
