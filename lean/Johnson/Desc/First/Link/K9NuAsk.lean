-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/K9NuAsk.lean: ONE TEST WITH CODE ON PUBLIC NUMBERS, A SEGMENT AT A TIME:
"THE VECTOR OF READS IS PLANNED WITH AT LEAST ONE ENTRY": the plan's length of the third vector at
the segment is not 0.
Definitions alone. No Mathlib. HELD ASIDE: a candidate conjunct for the test `k9Entry`
(Johnson/Desc/First/Link/K9Asks.lean); it stands in no running text.

  `nuB W X`: the plan's lengths of the vectors of reads at the built segment X: by X's kind and
    group: the head's plan's nU; the attention plan's seam.nU; the layers' plan's nU.
  `nuPosB W X`: **THE TEST**: 0 < (nuB W X).getD 2 0.
EVERY "none" ENDS IN false: where the group has no plan the lengths are #[], and the default at
number 2 is 0.
SECOND TEXT: `nuB` repeats `ProofFile.k8NU` (Johnson/Desc/ProofFile/Lot/K8.lean), at the public parameters
in place of the letters that hold them: it will have to be turned with it. The tie (by rfl) is in
Law/K9NuAskLaw.lean.
NO LOOP. NO POWER.
IT READS X's kind AND g ALONE OF THE BUILT SEGMENT; THE LENGTHS ARE THE PLANS'.
Limits. A yes says what the clause says and no more.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Model.StagesLinks
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model

/-- The plan's lengths of the vectors of reads at a built segment. -/
def nuB (W : Verify.Public) (X : Stages.LinkH) : Array Nat :=
  if X.kind == 2 then W.H.nU
  else if X.kind == 1 then ((W.A[X.g]?).map (·.seam.nU)).getD #[]
  else ((W.G[X.g]?).map (·.nU)).getD #[]

/-- **THE TEST.** -/
def nuPosB (W : Verify.Public) (X : Stages.LinkH) : Bool := decide (0 < (nuB W X).getD 2 0)

end VerifiableInference.Desc.K9Asks
