-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FitsLaterClosed.lean: the hypothesis `hone` of `fits_shared`
and `fits_last` (FitsLater.lean): the test `fwdFit` (Thr.lean) at the written lists of places of the
shared chain and the second chain. No statement here has a free variable. All are decided by the
kernel's evaluation (`decide +kernel`), so they are counted apart from the other lemmas.
SharedRows.lean and LastRows.lean evaluate the same two tests in `#guard` lines. No definition.

  1  `onePass_shared`, `onePass_last`   the two tests pass
  2  `onePass_shared_control`, `onePass_last_control`   the tests can fail: each fails from an empty
     start

Limits.
  * The tests read lists of items only: they say nothing about what an item means.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SharedRows
import Johnson.Desc.ProofFile.Honest.Thread.LastRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

theorem SharedRows.onePass_shared :
    fwdFit SharedRows.start (SharedRows.rows true)
      (VerifiableInference.Desc.Shared.sharedPlaces true).length = true := by
  decide +kernel

/-- A control: from an empty start the same test fails. -/
theorem SharedRows.onePass_shared_control :
    fwdFit [] (SharedRows.rows true)
      (VerifiableInference.Desc.Shared.sharedPlaces true).length = false := by
  decide +kernel

theorem LastRows.onePass_last :
    fwdFit VerifiableInference.Desc.Last.startLast LastRows.rows
      VerifiableInference.Desc.Last.lastPlaces.length = true := by
  decide +kernel

/-- A control: from an empty start, and with the first sub-protocol's row left out, the same test
fails. -/
theorem LastRows.onePass_last_control :
    fwdFit [] (fun b => LastRows.rows (b + 1))
      VerifiableInference.Desc.Last.lastPlaces.length = false := by
  decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.SharedRows.onePass_shared
#print axioms ProofFile.Honest.SharedRows.onePass_shared_control
#print axioms ProofFile.Honest.LastRows.onePass_last
#print axioms ProofFile.Honest.LastRows.onePass_last_control
