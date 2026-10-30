-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K12.lean: the proximity test (the kind K12) as a lot for the fold over
blocks: its own block at its place on the first chain, «F:2»; all the steps of that place are the
lot's.

No control stands here: the file imports the fold's records (Johnson/Desc/ProofFile/LotCore.lean),
the kind's seat and the place's numbers alone, so that it can sit in the seat of the run of record.
What lies beneath these three is for a walk of the import lines to say.
  the block: `atFinish` (Johnson/Desc/K12/AtFinish.lean), at the numbers that
    Johnson/Desc/K12/AtPlan.lean makes of the plan (`H2U.p12OfMade Z.made`). It takes no letter of
    the harness.
It states no run of claims: the proximity test stands behind the last segment, in no link, and its
block has no list of claims.
Limits: definitions only; nothing is proved here. No soundness is claimed, and nothing is said on
hiding.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K12.AtFinish

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12

/-- **The lot**: the proximity test's own block at «F:2». No control. -/
def lot (Z : ProofFile.Pub) : ProofFile.Lot :=
  { name := "the proximity test at F:2 (K12)"
    letters := false
    own := fun _ => [atFinish (H2U.p12OfMade Z.made)]
    controls := [] }

end VerifiableInference.Desc.K12
