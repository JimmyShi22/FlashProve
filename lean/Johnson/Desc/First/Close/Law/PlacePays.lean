-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/PlacePays.lean: THREE PREMISES OF K10's LAW ON THE GROUP's STAGE AND
RADIUS, PAID AT A PLACE THAT PASSES ITS TEST. Statements and proofs.

K10's law (`k10_leads_good` and all above it, beside this file) asks of the group's stage R.s and
radius R.e: the radius lies inside the Johnson radius (hj); the two counts of exceptional points
hold (hc); the radius is below the distance (he). A place of Johnson/Bridge/FoldPriced.lean
(`FoldedPlace`: a stage, a radius, two brackets) that passes the test `good` has all three, with no
hypothesis on codes.
  `place_inJ`, `place_counts`, `place_radius`: the three, at a place x with `x.good = true` whose
    stage and radius are the group's; the counts are x's own (x.bC, x.bZ).
Limits. That a group of the description stands at such a place is not shown. This file rests,
through FoldPriced.lean, on the files under ThirdParty/ (lean/LIMITS.md, L15). Nothing on soundness
of the protocol.

-/
import Johnson.Top.H.GroupRowsKept
import Johnson.Top.H.CountsBridge
import Johnson.Bridge.FoldPriced

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Cb Johnson.Top.H

variable {S : Sig GE} (R : RowsK S) (x : Johnson.Bridge.FoldedPlace)

theorem place_inJ (hg : x.good = true) (hs : x.s = R.s) (he : x.e = R.e) : InJ R.s R.e := by
  have h := (Johnson.Bridge.FoldedPlace.stageJ hg).joh
  rw [hs, he] at h
  exact ⟨h.1, h.2⟩

theorem place_counts (hg : x.good = true) (hs : x.s = R.s) (he : x.e = R.e) :
    CountsAt R.s R.e x.bC x.bZ := by
  have h := Johnson.Bridge.FoldedPlace.counts hg
  rw [hs, he] at h
  exact countsAt_iff.2 h

theorem place_radius (hg : x.good = true) (hs : x.s = R.s) (he : x.e = R.e) : R.G.e < R.s.d := by
  have h := Johnson.Bridge.FoldedPlace.radius_lt hg
  rw [hs, he] at h
  exact h

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.place_inJ
#print axioms VerifiableInference.Desc.First.Close.place_counts
#print axioms VerifiableInference.Desc.First.Close.place_radius
