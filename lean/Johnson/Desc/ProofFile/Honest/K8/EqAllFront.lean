-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/EqAllFront.lean: THE SMALLNESS TEST: WHERE THE SEARCH FOR A COLUMN
OF WEIGHT 0 FINDS NONE, THE THIRD TEST ON VALUES OF `eqAll_returns` HOLDS. One lemma; none of the
library's goals.

  `liveCols_of_front`   `zeroColumnWeight tl chi = none`
                        (Johnson/Desc/ProofFile/Honest/K8/Share.lean: the search behind the named
                        fall `k8Front`) gives `LiveCols tl funs chi`
                        (Johnson/Desc/K8/Honest/EqAllReturns.lean), for every list of tables
The search goes over all matrices of the list; `LiveCols` asks only those on which a read lies, and
every read of the library's list lies on a matrix of the list (`mat_lt_of_mem`,
Johnson/Desc/K8/Honest/ReadsMem.lean).
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.FrontMeans
import Johnson.Desc.K8.Honest.EqAllReturns
import Johnson.Desc.K8.Honest.ReadsMem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- Where the search for a column of weight 0 finds none, no column of a matrix on which a read lies
has the weight 0. -/
theorem liveCols_of_front (tl : HTailF2) (funs : Array HFun) (chi : E)
    (h : zeroColumnWeight tl chi = none) : LiveCols tl funs chi :=
  fun x hx c hc => front_none tl chi h x.1.mat (mat_lt_of_mem hx) c hc

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.liveCols_of_front
