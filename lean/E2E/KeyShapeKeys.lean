--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeKeys.lean: OF THE LOOKUPS' CLAIMS ON THE KEYS, IN THE KEY FILE's FIRST CHAIN: what the
chain's shape holds of them, and the one test on their values. Four definitions with code; no
theorem. It imports the library alone, so that the files on the chain's front half and on its back
half can both import it.

  `keysB`: THE MARK, on form: of each lookup that has its claims: a claim for each part, and the two
    tests on a claim's form that "the rows on the table" asks (`Key.tableRowsOf`,
    Johnson/Desc/Key/TableRows.lean).
  `keysFormB`: the mark, and every lookup has its claims.
  `keysSumB`: that step's third test, ON VALUES.
  `keysSlots`: of each claim the slots that its mask form names.

Limits.
- Nothing is shown here. The laws: E2E/KeyShapeBack.lean.


-/
import OnBytes.Iop.Wf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params

/-- **The mark on the lookups' claims on the keys**: on form: of each lookup that has its claims: a
claim for each part, and the two tests on a claim's form. -/
def keysB (m : Wf.Matrix) (lookups : List WfLookup) (keys : List (List Lkp.Keys)) : Bool :=
  (zipT lookups keys).all fun x =>
    x.1.parts.length == x.2.length && (zipT x.1.parts x.2).all fun y =>
      y.2.point.length == m.kCol + y.1.logPlaces && y.2.weights.tensors.all (·.denseVars.isEmpty)

/-- The mark, and every lookup has its claims. -/
def keysFormB (m : Wf.Matrix) (lookups : List WfLookup) (keys : List (List Lkp.Keys)) : Bool :=
  lookups.length == keys.length && keysB m lookups keys

/-- **The test on values**: each claim's weights add up to the sum of the equality vector over the
places that the part's runs cover. -/
def keysSumB (m : Wf.Matrix) (lookups : List WfLookup) (keys : List (List Lkp.Keys)) : Bool :=
  (zipT lookups keys).all fun x => (zipT x.1.parts x.2).all fun y =>
    Wf.sumOfForm y.2.weights == Wf.coveredSum y.1 (Wf.eqPlaces m y.2.point)

/-- Of each claim on a part's keys: the slots that its mask form names. -/
def keysSlots (keys : List (List Lkp.Keys)) : List (List (List Slot)) :=
  keys.map fun ks => ks.map fun k => k.masks.map (·.1)

end AtPublicFiles.AtFiles
