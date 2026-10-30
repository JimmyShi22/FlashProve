-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/PlanFitsAll.lean: THE SMALLNESS TEST: THE ONE NAMED TEST ON THE PUBLIC
PARAMETERS THAT ITS THEOREM AT THE FOLD ASKS. A DEFINITION WITH CODE. NO THEOREM HERE. NO SOUNDNESS
IS CLAIMED.

  `planFitsAllB W`: W: the public parameters (`OnBytes.Model.Verify.Public`). A TEST: `planFitsB`
    (Johnson/Desc/First/K8/PlanFits.lean) says yes at the planned value of the smallness test's part
    in each plan of a layers' sub-proof (W.G), in the seam of each plan of an attention sub-proof
    (W.A), and in the head's plan (W.H).
It reads the public parameters alone: no proof's byte, no weight. No block of the description asks
it.

-/
import Johnson.Desc.First.K8.PlanFits
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model

/-- The test at all planned values. -/
def planFitsAllB (W : Verify.Public) : Bool :=
  (W.G.all fun hp => planFitsB hp.tl) && (W.A.all fun a => planFitsB a.seam.tl) &&
    planFitsB W.H.tl

end VerifiableInference.Desc.First.K8.Ready
