-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/Front.lean: THE SMALLNESS TEST: WHAT ITS LAW ASKS OF THE VERIFIER'S STATE IN
FRONT OF THE DRAW, BESIDE "WHAT THE MATRIX MULTIPLIES IS SENT", AS ONE TEST WITH CODE ON THE STATE
ALONE. A DEFINITION. NO THEOREM HERE. NO SOUNDNESS IS CLAIMED.

  `frontB s`: A TEST: a link is open in s; the list of tables of the smallness test's part is
    closed; every table of it lies on the third vector of reads (`onThirdB`,
    Johnson/Desc/First/K8/Cond.lean); and that part passes `planFitsB`
    (Johnson/Desc/First/K8/PlanFits.lean).
It names no value of the plan: since the law's letters are taken off the statement in front, the
law's public value of the smallness test's part is the state's own. Meant as one fact along the
fold: at every state that is reached in front of a draw the test says yes.

-/
import Johnson.Desc.First.K8.Cond
import Johnson.Desc.First.K8.PlanFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model

/-- The test in front of the draw. -/
def frontB (s : S) : Bool := onThirdB s && (s.tl?.map planFitsB == some true)

end VerifiableInference.Desc.First.K8.Ready
