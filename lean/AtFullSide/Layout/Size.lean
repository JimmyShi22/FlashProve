-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Layout/Size.lean: THE STORED FULL-SIZE LAYOUT FILE HAS 224,975 BYTES.
  **`lay_size`**: `VerifierAndGoals.storedPublicFiles.lay.size = 224975`: from the tie `lay_bytes` (Tie.lean) and the
    closed fact `pieces_length` (Johnson/Unfolds/Layout/Pieces.lean). No byte of the literal is
    looked at here.
  `size_eq`: a general tool: an array of bytes has as many bytes as its list.
It lies in this side library because it stands on TieRfl.lean (see that file's head).
Limits. One stored file. Nothing on soundness.
-/
import AtFullSide.Layout.Tie

namespace Johnson.Unfolds.Layout

/-- An array of bytes has as many bytes as its list. -/
theorem size_eq (b : ByteArray) : b.size = b.data.toList.length :=
  (Array.length_toList).symm

/-- **The file's size.** Joined as a term: no tactic is let near the literal. -/
theorem lay_size : VerifierAndGoals.storedPublicFiles.lay.size = 224975 :=
  (size_eq _).trans ((congrArg List.length lay_bytes).trans
    (List.length_flatten.trans pieces_length))

end Johnson.Unfolds.Layout

#print axioms Johnson.Unfolds.Layout.size_eq
#print axioms Johnson.Unfolds.Layout.lay_size
