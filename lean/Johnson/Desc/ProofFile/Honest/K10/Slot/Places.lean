-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Slot/Places.lean: the closing of a segment (K10): THE LOT's LIST OF PLACES (`closePars`,
Honest/K10/AtLot.lean) AT A PUBLIC PART WITH THE WRITTEN TABLE OF PLACES, ENTRIES AND GROUPS IS THE SPELLED LIST
`writtenClosings` (Honest/K10/Slot/Written.lean). So that list is the lot's own there, and not only a list held against
WP's blocks. The three premises are the ones that the library's row of K9 takes (`k9_row_written`,
Johnson/AtFull/Desc/Lots/K9RowWritten.lean); under the head they stand as `spots_at_head`, `entries_at_head`,
`groups_at_head`.

  `closeParsEntries`   the body of `closePars` on the stretches of entries: the library's readers `k9LinksE`, `k9WhereE`,
      `k10ParE`
  `closePars_is`       the first text is the second, with no hypothesis
  `closeParsEntries_written`  Lean's kernel: at the written values it is `writtenClosings`
  **`closePars_written`**   at every Z with those three values
  `closePars_bite`     THE TEST CAN FAIL: at the entries with the first dropped the list is not `writtenClosings`

Limits. That a given Z has these three values is a premise here. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K10.Slot.Written
import Johnson.AtFull.Desc.SpotsWritten
import Johnson.AtFull.Desc.Lots.K9RowWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Slot
open VerifiableInference.Desc.First.Close (Par)
open Johnson.AtFull.Desc (spotsWritten)
open Johnson.AtFull.Desc.Lots (XsE toE stretchedE stretched_entries k9LinksE k9WhereE k10ParE k9Links_eq
  k9Where_eq k10ParG_eq groupsW esW)

/-- The body of `closePars`, on stretches of entries. -/
def closeParsEntries (groups : Array OnBytes.ReqGroup) (xs : XsE) : List Par :=
  (k9LinksE xs).filterMap fun l => (k9WhereE xs l).bind fun p => k10ParE groups xs p

/-- The first text is the second, with no hypothesis. -/
theorem closePars_is (Z : ProofFile.Pub) :
    closePars Z = closeParsEntries Z.s₀.check.frame.groups ((ProofFile.k9Stretches Z).map toE) := by
  show (ProofFile.k9Links (ProofFile.k9Stretches Z)).filterMap
    (fun l => (ProofFile.k9Where (ProofFile.k9Stretches Z) l).bind fun p => ProofFile.k10Par Z (ProofFile.k9Stretches Z) p) = _
  unfold closeParsEntries
  rw [k9Links_eq]
  refine congrArg (fun f => List.filterMap f _) (funext fun l => ?_)
  rw [k9Where_eq]
  exact congrArg _ (funext fun p => k10ParG_eq _ _ p)

/-- **At the written values.** -/
theorem closeParsEntries_written :
    closeParsEntries groupsW (stretchedE spotsWritten esW 0) = writtenClosings := by
  decide +kernel

/-- **So at every Z with those three values.** -/
theorem closePars_written (Z : ProofFile.Pub) (hs : ProofFile.spotsOf Z.cuts = some spotsWritten)
    (he : Z.D.1.map (·.entry) = esW) (hg : Z.s₀.check.frame.groups = groupsW) :
    closePars Z = writtenClosings := by
  have ex : (ProofFile.k9Stretches Z).map toE = stretchedE spotsWritten esW 0 := by
    unfold ProofFile.k9Stretches
    rw [hs, ← he]
    exact stretched_entries spotsWritten Z.D.1 0
  rw [closePars_is, ex, hg]
  exact closeParsEntries_written

/-- **The test can fail.** -/
theorem closePars_bite :
    closeParsEntries groupsW (stretchedE spotsWritten (esW.drop 1) 0) ≠ writtenClosings := by
  decide +kernel

end ProofFile.Honest.K10.Slot

#print axioms ProofFile.Honest.K10.Slot.closeParsEntries
#print axioms ProofFile.Honest.K10.Slot.closePars_is
#print axioms ProofFile.Honest.K10.Slot.closeParsEntries_written
#print axioms ProofFile.Honest.K10.Slot.closePars_written
#print axioms ProofFile.Honest.K10.Slot.closePars_bite
