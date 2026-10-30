-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/PlanFits.lean: THE SMALLNESS TEST: THREE FACTS THAT ITS LAW ASKS OF THE PLAN'S
VALUE OF ITS PART OF THE VERIFIER'S STATE, AS ONE TEST WITH CODE ON PUBLIC DATA. A DEFINITION. NO
THEOREM HERE. NO SOUNDNESS IS CLAIMED.

  `planFitsB tl`: tl: a value of the Lean structure `HTailF2`; meant: the plan's, for one link. A
    TEST: (1) each of the tl.NM shapes has its matrix's numbers of rows of cells and of columns;
    (2) there are at least tl.NM numbers of symbol arrays; (3) the index of the arrays names a third
    vector of reads.
It reads five fields: the number of matrices, the shapes, the matrices, the symbol arrays' numbers,
the index of the arrays: all among the seven of the public item "K8.lay7"
(Johnson/Desc/First/K8/Cond.lean). What a yes gives is Johnson/Desc/First/K8/LawPlanFits.lean's. No
block of the description asks this test.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model

/-- The three facts, as one test. -/
def planFitsB (tl : HTailF2) : Bool :=
  ((List.range tl.NM).all fun mu =>
    (tl.shp.getD mu {}).m == (tl.mats.getD mu {}).m &&
      (tl.shp.getD mu {}).k == (tl.mats.getD mu {}).k) &&
  decide (tl.NM ≤ tl.gtTree.size) &&
  (match tl.ix.U[2]? with
    | some (some _) => true
    | _ => false)

end VerifiableInference.Desc.First.K8.Ready
