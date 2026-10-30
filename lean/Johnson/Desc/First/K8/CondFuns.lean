-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/CondFuns.lean: THE SMALLNESS TEST: ONE TEST WITH CODE ON THE VERIFIER'S STATE
IN FRONT OF THE SENDING OF THE READS AT A LAYERS' LINK. A DEFINITION. NO THEOREM HERE. NO SOUNDNESS
IS CLAIMED.

  funsThirdB s: A TEST: the tables as the claims take them (S.funs?) are there in s, and every one
    lies on the third vector of reads.
It stands beside Johnson/Desc/First/K8/Cond.lean's onThirdB, which asks the like of the smallness
test's own list. What ties the two is Johnson/Desc/First/K8/LawCondK1.lean's k1Reads_makes_layers.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

/-- A test: the tables as the claims take them are there, and every one lies on the third vector of
reads. -/
def funsThirdB (s : S) : Bool :=
  (s.funs?.map fun f => f.toList.all fun Fn => Fn.tree == 2) == some true

end VerifiableInference.Desc.First.K8.Ready
