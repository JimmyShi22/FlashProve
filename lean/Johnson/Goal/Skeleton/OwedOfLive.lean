-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/OwedOfLive.lean: `owed_of_live`: where the description's test `protocolDataWellFormed`
accepts at three public files Z, the closed condition `P5J.At.CondsOwed Z` (`rowsRead Z`) holds.
One theorem with its proof.
IT STANDS OVER THE LIST OF FOURTEEN ROWS OF THE PROOF FILE'S ENTRY TESTS
(`LPFD.lawsAsk`).

Why. Row 14 of that list asks `rowsMadeB` at the public part that the maker returns, at every
size. So `verify` itself runs the test, and a top need not assume it.

How, by three calls, all of other files' theorems:
  `laid_at_name`      (Johnson/P5J/AtName.lean) live: the verifier's own value is laid
  `laid_opens`        (Johnson/P5J/LaidOpens.lean) it opens at letters Zp Np cF: `LaidAt`, whose
                      field `asks` says that every entry test has accepted
  `rowsRead_of_laid`  (Johnson/P5J/RowsOfLaid.lean) so row 14's bare test has accepted at Zp, and
                      where `protocolDataWellFormed` accepts its yes is `rowsRead Z`

Limits. No scope is asked: row 14 is asked at every size. It says nothing where `protocolDataWellFormed` rejects.
That `protocolDataWellFormed` accepts at some Z is not shown here (see AtFullSide/Top/LiveAtFull.lean, a side
library). At the second hash function. Nothing on soundness.

-/
import Johnson.P5J.AtName
import Johnson.Goal.Skeleton.CondsOfLaid
import Johnson.P5J.RowsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **Live: the one closed condition holds: the verifier has run its test.** -/
theorem owed_of_live {Z : VerifierAndGoals.PublicFiles} (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) : At.CondsOwed Z := by
  obtain ⟨Zp, Np, cF, L⟩ := laid_opens (laid_at_name hl)
  exact ⟨rowsRead_of_laid hl L⟩

end P5J

#print axioms P5J.owed_of_live
