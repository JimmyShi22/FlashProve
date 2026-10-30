-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/LayoutRead/Full.lean: WHAT THE LAYOUT FILE's READER (OnBytes.Plan.layoutRead,
OnBytes/Plan/ReqFrame.lean) RETURNS AT THE STORED FULL-SIZE LAYOUT FILE (VerifierAndGoals.storedPublicFiles.lay): the
written value LW (Johnson/AtFull/LayoutRead/Values/All.lean): 99 groups and 5,419 blocks, in the
file's order. One theorem: a call.
  **`layoutRead_full`** : layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW: by `layoutRead_pieces`
    (Johnson/AtFull/LayoutRead/Pieces.lean) at the tie of the file's bytes to the written pieces
    (Johnson.Unfolds.Layout.lay_bytes, AtFullSide/Layout/Tie.lean) and the fourteen closed facts
    (`pieces_are`, Johnson/AtFull/LayoutRead/PiecesAre.lean).
Why. The planner reads the layout file anew in each of its runs. This theorem gives that reading's
value at the stored file. (The goals' scope asks Z.lay = VerifierAndGoals.storedPublicFiles.lay: whoever holds that
equation can rewrite with it first; it is not used here.)
Limits. It says what the reader returns, not that the layout fits the segments' declared arrays
(Plan.reqFrame). ONE CONSTANT BENEATH IT, `lay_chars` (AtFullSide/Layout/TieRfl.lean), WAS SEEN TO
FAIL IN LEAN's KERNEL AT THE DEFAULT STACK, AND PASSES AT 128 MB: so this file lies with it in the
side library AtFullSide, which is built with that larger thread stack (lake build AtFullSide).
"Stored" means the Lean constant `VerifierAndGoals.storedPublicFiles.lay`, as Ladder/Stored.lean spells it: no Lean code
compares that text with a file on a disk. Nothing on soundness.

-/
import Johnson.AtFull.LayoutRead.PiecesAre
import AtFullSide.Layout.Tie

set_option autoImplicit false

namespace Johnson.AtFull.LayoutRead
open OnBytes.Plan

/-- **What the reader returns at the stored full-size layout file.** -/
theorem layoutRead_full : layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW := by
  rw [LW_row]
  exact layoutRead_pieces Johnson.Unfolds.Layout.lay_bytes pieces_are

end Johnson.AtFull.LayoutRead

#print axioms Johnson.AtFull.LayoutRead.layoutRead_full
