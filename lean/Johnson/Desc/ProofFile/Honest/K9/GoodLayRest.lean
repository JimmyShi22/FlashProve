-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodLayRest.lean: FOUR OF THE NINE PREMISES OF `liveLayers_of_clauses`
(Honest/K9/GoodLayLive.lean) AS ONE NAMED SENTENCE, so that a file which stands over the frame's Honest/Strat.lean
(where the short name of a list of ours means another list) need write no list. ONE DEFINITION and one lemma; no goal is
stated.
  `LayRest p4 s a₀ n pC pD hC hD`   A DEFINITION: there is a set W4 of slots with: outC (the merge's slot lies outside
      the calls' stretch) · cover (every slot below n but the merge's lies in the calls' window "objects", in W4 or in
      the digits' stretch) · live4, un4 (K4's lists are live on W4, and do not name the merge's slot): these four
      premises' text, to the letter
  `liveLayers_of_rest`   `LiveLayers` from the two shapes, the lookups' two clauses, hlt (the merge's slot lies below
      the digits' first slot: it gives outD) and `LayRest`: one call
WHAT IS NOT CLAIMED. `LayRest` at any state: IT IS NOT SHOWN: NO MEMBER (but at n := 0, where an empty W4 meets it for
nothing). W4 stands under "there is": a set that is too large makes cover light and live4 heavy. `liveLayers_of_rest` is
called by Honest/K9/BatFrontHanded.lean alone; `LayRest` is made in Honest/K9/GoodLayRestK4.lean from premises. Nothing
on any property.
GROUND: beneath this file lie 134 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodLayLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8.Honest (layersFront layersBack plainOf)
open VerifiableInference.Desc.K9 (mergeOf Where)
open VerifiableInference.Desc.K9H (liveAt unnamedAt slotsLive)
open ProofFile.Honest.K3 (Run)
open ProofFile.Honest.K3.Good.Live (Clause Outside InWin)

/-- **Four of the nine premises of `liveLayers_of_clauses` (Honest/K9/GoodLayLive.lean), as one sentence**: outC, cover,
live4, un4, at some set W4 of slots. -/
def LayRest (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat) (pC pD : First.Look.P)
    (hC hD : Forest.Shape) : Prop :=
  ∃ W4 : Nat → Prop,
    (∀ j < n, mergeOf s = some j → Outside pC hC j) ∧
    (∀ j < n, mergeOf s ≠ some j →
      InWin pC hC Run.objects j ∨ W4 j ∨ (pD.first ≤ j ∧ j < pD.first + Forest.elems hD)) ∧
    (∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j, W4 j → liveAt (plainOf lf ++ layersBack o) j = true) ∧
    ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf lf ++ layersBack o) j = true

/-- "Live" from the two shapes, the two clauses, "the merge's slot lies below the digits' first" and the rest. -/
theorem liveLayers_of_rest (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat)
    {pC pD : First.Look.P} {hC hD : Forest.Shape} (spC : pC.shape = some hC) (spD : pD.shape = some hD)
    (JC : Clause pC a₀.lookHeard) (JD : Clause pD a₀.tl.heard) (hlt : ∀ j, mergeOf s = some j → j < pD.first)
    (R : LayRest p4 s a₀ n pC pD hC hD) :
    LiveLayers p4 s a₀ n := by
  obtain ⟨W4, oC, cov, l4, u4⟩ := R
  exact liveLayers_of_clauses p4 s a₀ n spC spD JC JD oC (fun j _ hm => Or.inl (hlt j hm)) W4 cov l4 u4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.LayRest
#print axioms ProofFile.Honest.K9.liveLayers_of_rest
