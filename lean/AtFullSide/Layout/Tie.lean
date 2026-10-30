-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Layout/Tie.lean: THE TIE: THE STORED FULL-SIZE LAYOUT FILE's BYTES ARE THE FOURTEEN
WRITTEN PIECES, JOINED.
  `lay_is`: `VerifierAndGoals.storedPublicFiles.lay = OnBytes.Tie.Pv.Plan.layoutF.toUTF8`: two names unfolded.
  **`lay_bytes`**: `VerifierAndGoals.storedPublicFiles.lay.data.toList = pieces.flatten`.
  `lay_toList`: the same of `VerifierAndGoals.storedPublicFiles.lay.toList` (by `VerifierAndGoals.Read.toList_eq`): for
    callers; nothing in this folder spends it.
From `lay_chars` (TieRfl.lean: Lean's checker's comparison of the literal with the pieces'
characters), the general law `bytes_of_ascii` (Johnson/Unfolds/StringBytes.lean) and `pieces_ascii`,
JOINED AS A TERM in `lay_bytes`: no tactic that rewrites or reduces is let near the literal (a
proof with show | rw died of the stack within four seconds; why, was not looked
into). `lay_is` is by `kernel_rfl`, which lays `Eq.refl` and leaves the comparison to Lean's
checker. No byte of the literal is looked at here: this file passes at the default stack. It lies in
this side library because it imports TieRfl.lean (see that file's head).
Limits. One stored file. Nothing on what a parser makes of these bytes. Nothing on soundness.

-/
import AtFullSide.Layout.TieRfl
import Ladder.FilesReadLaws

namespace Johnson.Unfolds.Layout

theorem flatten_ascii : (pieces.flatten.all (· < 128)) = true := by
  rw [List.all_flatten]
  exact pieces_ascii

/-- The stored file is the literal's bytes: by unfolding two names; the literal is not opened. -/
theorem lay_is : VerifierAndGoals.storedPublicFiles.lay = OnBytes.Tie.Pv.Plan.layoutF.toUTF8 := by
  kernel_rfl

/-- **The file's bytes are the pieces, joined.** -/
theorem lay_bytes : VerifierAndGoals.storedPublicFiles.lay.data.toList = pieces.flatten :=
  (congrArg (fun b : ByteArray => b.data.toList)
    (lay_is.trans (congrArg String.toUTF8 lay_chars))).trans
    (Johnson.Unfolds.bytes_of_ascii _ flatten_ascii)

theorem lay_toList : VerifierAndGoals.storedPublicFiles.lay.toList = pieces.flatten :=
  (VerifierAndGoals.Read.toList_eq _).trans lay_bytes

end Johnson.Unfolds.Layout

#print axioms Johnson.Unfolds.Layout.flatten_ascii
#print axioms Johnson.Unfolds.Layout.lay_is
#print axioms Johnson.Unfolds.Layout.lay_bytes
#print axioms Johnson.Unfolds.Layout.lay_toList
