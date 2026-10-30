-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookSkel.lean: NO HYPOTHESIS.

What is here. A RELATION ON TWO VALUES OF WHAT THE LOOKUP IN FRONT HAS SAMPLED (`Forest.Heard`,
OnBytes/Model/Look.lean): what of them the public test on the parts of the feed-forward layers' own
rounds (`k4Fits`, Honest/K4/Part.lean) reads at most: the lookup's public numbers and six lengths.
One definition, that it holds of a thing and itself, a member and a negative test.

  `LookSkel`   the relation.
  `lookSkel_refl`   it holds of a thing and itself.

Debts and ends. `LookSkel` IS A DEBT: a hypothesis of the laws at this family's rim:
`k4MakersAt_skel` and `k4Makers_everywhere` (Law/MakersAt.lean (no part of the library yet));
`k4Fits_everywhere` (Law/MakersSkel.lean (no part of the library yet)), which no file of its writers
calls; `k4Makers_run` (Law/PtsFullOf.lean (no part of the library yet)), which
`k4_makers_seated_all` (Law/SeatedRun.lean (no part of the library yet)) alone calls, and pays; and,
outside the family, of the seven laws on a maker's return at a run, and of `makersAt_one` and
`makersAt_any`, through which they stand on the first (Law/SumAtRun.lean (no part of the library
yet), Law/SumAtRun2.lean (no part of the library yet)); of five laws of Law/FlatRun.lean (no part of
the library yet), which call five of these; and of two of Law/FlatFields.lean (no part of the
library yet), which call those: each hands it on as a hypothesis of its own. ITS PAYERS, ALL THAT
ITS WRITERS KNOW OF: `lookSkel_refl`, here; `entry_look` (Law/FlatLed.lean (no part of the library
yet)), `stand_run` (Law/W/MakersReturn.lean (no part of the library yet)) and `k4_seated_run`
(Law/SeatedRun.lean), all three by it. ALL FOUR STAND AT ONE AND THE SAME FRONT: they serve where
the test is asked at what `look` returns at the run's own challenges in front. BETWEEN WHAT `look`
RETURNS AT TWO LISTS OF CHALLENGES NO LAW THAT THEY KNOW OF CONCLUDES IT. IT READS NO ELEMENT: one
field of public numbers, and six lengths.

Not shown here. THAT THE TEST READS NO MORE THAN THIS: `k4Fits_skel` (Law/MakersSkel.lean). The
relation asks MORE than the test's own clause on the lookup (`k4LookFits`) gives: all the lookup's
public numbers, where that clause holds seven of them against the layout, and the lengths of the
lookup's two points on the planes, of which that clause says nothing.

Kin. No twin is known to its writers. Of like make, on the verifier's own structures: the library's
`EnvSkel` and `Skel` (Johnson/Road/K4/Total/Returns.lean); its `HearSkel` there asks of two lookups
the first clause alone, fo.shape = fo₀.shape.
No property is claimed.
-/
import OnBytes.Model.Look

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Forest.Heard)

/-- **What of the lookup's sampled values the public test reads AT MOST**: the public numbers, and
the lengths of the place in a tree, of the list of the calls' weights, of the list of the calls'
points, of each call's point and of the two points on the planes. NOT in it: any element. That the
test reads no more is not shown here. -/
structure LookSkel (fo fo₀ : Forest.Heard) : Prop where
  shape : fo.shape = fo₀.shape
  zx : fo.zx.size = fo₀.zx.size
  e : fo.e.size = fo₀.e.size
  zks : fo.zk.size = fo₀.zk.size
  zk : ∀ q, (fo.zk.getD q #[]).size = (fo₀.zk.getD q #[]).size
  zb0 : fo.zb0.size = fo₀.zb0.size
  zb1 : fo.zb1.size = fo₀.zb1.size

/-- The relation holds of a thing and itself. -/
theorem lookSkel_refl (fo : Forest.Heard) : LookSkel fo fo :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩

/-- A member of the relation: other elements in every place that the relation measures, and another
alpha and theta; lengths kept. -/
example (fo : Forest.Heard) (f : E → E) (a t : E) :
    LookSkel
      { fo with
        alpha := a, theta := t, zx := fo.zx.map f, e := fo.e.map f, zk := fo.zk.map (·.map f),
        zb0 := fo.zb0.map f, zb1 := fo.zb1.map f } fo := by
  refine ⟨rfl, Array.size_map .., Array.size_map .., Array.size_map .., fun q => ?_,
    Array.size_map .., Array.size_map ..⟩
  show ((fo.zk.map (·.map f)).getD q #[]).size = _
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases fo.zk[q]? with
  | none => rfl
  | some z => exact Array.size_map ..

/-- Negative test: a place in a tree with one coordinate more is not in the relation. -/
example (fo : Forest.Heard) : ¬ LookSkel { fo with zx := fo.zx.push zeroE } fo := fun S => by
  have e := S.zx
  rw [Array.size_push] at e
  omega

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.LookSkel
#print axioms ProofFile.Honest.K4.lookSkel_refl
