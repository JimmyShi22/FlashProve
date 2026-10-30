-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodLayRestK4.lean: `LayRest` (Honest/K9/GoodLayRest.lean) FROM outC, cover AND THE
FEED-FORWARD LAYERS' HOUSE's TWO TEXTS `K4.Live4Text`, `K4.Un4Text` (definitions of that house's, in
Honest/K4/Law/Live/GoodLayFormFits.lean, which it has set under our namespace: live4's and un4's text). A bridge of one
line, in a file of its own BELOW the frame's Honest/Strat.lean, so that the files above need write no list. No
definition; no goal is stated.
  `layRest_of_texts`   the four laid together at a set W4: that the two texts ARE `LayRest`'s last two clauses is
      checked by Lean's kernel here, by unfolding
WHAT IS NOT CLAIMED. Any of the four at any state: NO MEMBER. Called by Honest/K9/BatFrontHandedK4.lean alone. Nothing
on any property.
GROUND: beneath this file lie 176 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodLayRest
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.GoodLayFormFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K9 (mergeOf)
open ProofFile.Honest.K3 (Run)
open ProofFile.Honest.K3.Good.Live (Outside InWin)

/-- `LayRest` from outC, cover and the feed-forward layers' house's two texts. -/
theorem layRest_of_texts (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat) (pC pD : First.Look.P)
    (hC hD : Forest.Shape) (W4 : Nat → Prop) (oC : ∀ j < n, mergeOf s = some j → Outside pC hC j)
    (cov : ∀ j < n, mergeOf s ≠ some j →
      InWin pC hC Run.objects j ∨ W4 j ∨ (pD.first ≤ j ∧ j < pD.first + Forest.elems hD))
    (l4 : K4.Live4Text p4 a₀ W4) (u4 : K4.Un4Text p4 s a₀ n) : LayRest p4 s a₀ n pC pD hC hD :=
  ⟨W4, oC, cov, l4, u4⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.layRest_of_texts
