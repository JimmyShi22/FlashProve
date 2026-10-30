-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodLayLive.lean: "GOOD" AT A FEED-FORWARD SEGMENT WITHOUT THE LENGTH.
`goodLayers_of_clauses` (Honest/K9/GoodLayPaid.lean) has ten premises; the tenth, len, says that the written list is
within the plan's number of claims. THE BOUND ON K9's FALL SPENDS `goodW` (Honest/K9/GateArms.lean), WHICH ASKS NO
LENGTH: SO len IS STRUCK HERE, NOT PAID. ONE DEFINITION; statements and proofs; no goal is stated. These files are not
turned.
  `LiveLayers p4 s a₀ n`   A DEFINITION OF THIS FILE: `GoodLayers` (Honest/K9/LayersFree.lean) without the length: at
      whatever four things the state's part holds as heard (`Heard4`), the written list is live on the slots below n
      (the library's Bool `slotsLive`). Where `Heard4` fails it holds for nothing; under the walk's premises draw and
      gatherer then return at no challenge (`heard_layers`), and `goodW` is idle with it
  `liveLayers_of_good`: "good" gives "live" · **`goodW_layers_live`**: `goodW` from the walk's premises (`Walk`) and
      "live": by `slotsLive_of_cut` (Honest/K9/CutLaw.lean), `cut_layers`, `heard_layers` · `liveLayers_of_shares`:
      `goodLayers_of_shares` less len: `goodCut_of_shares` called at plan := the list's own length ·
      **`liveLayers_of_clauses`**: `goodLayers_of_clauses` less len: NINE PREMISES; its text else
WHAT IS NOT CLAIMED. Any of the nine at any state: spC, spD (public) · JC, JD (the lookups' clause at what the two
lookups have heard) · outC, outD · cover · live4, un4 (the feed-forward layers' own). pC, pD, hC, hD are tied to s by
nothing here. No member. `goodW_layers_live` is called by Honest/K9/FallFormLay.lean; `liveLayers_of_clauses` by
Honest/K9/GoodLayRest.lean; `liveLayers_of_good` by no line. Nothing on any property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 133 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodLayPaid
import Johnson.Desc.ProofFile.Honest.K9.GoodLay

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
open ProofFile.Honest.K3.Good.Live (Clause Outside InWin pay_live pay_unnamed pay_live8 pay_unnamed8 stretch_iff)

/-- **"Live", on data in front of the draw**: `GoodLayers` (Honest/K9/LayersFree.lean) without the length. -/
def LiveLayers (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat) : Prop :=
  ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf →
    slotsLive n (mergeOf s)
      (cutList (layersFront gC gD lf) (K9L.four8 a₀.tl gD) (k8Len a₀.tl o.funs) (layersBack o)) = true

/-- "Good" gives "live". -/
theorem liveLayers_of_good (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat)
    (good : GoodLayers p4 s a₀ n) : LiveLayers p4 s a₀ n := fun gC gD o lf H => by
  have G := good gC gD o lf H
  unfold goodCut at G
  rw [Bool.and_eq_true] at G
  exact G.1

/-- **"Good" without a yes and without a length, at a feed-forward segment, from "live"**: no length is asked. -/
theorem goodW_layers_live (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat) (p : Where) (s : S)
    (a₀ : LayOwn) (w : Walk L p4 nU s a₀) (n : Nat) (live : LiveLayers p4 s a₀ n) :
    goodW p (claimsInBy L.each L.hear L.order) s n := fun x y hy => by
  have lists := lists_of_walk L p4 nU p s a₀ w
  obtain ⟨gC, gD, o, lf, hh⟩ := heard_layers L p4 p s a₀ lists x y hy
  rw [slotsLive_of_cut p _ s _ _ _ _ _ (cut_layers L p4 p s a₀ lists gC gD o lf hh) n x y hy]
  exact live gC gD o lf hh

/-- **"Live" from four shares**: `goodLayers_of_shares` (Honest/K9/GoodLayShares.lean) less its premise len. -/
theorem liveLayers_of_shares (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat)
    (WC W4 WD W8 : Nat → Prop)
    (cover : ∀ j < n, mergeOf s ≠ some j → WC j ∨ W4 j ∨ WD j ∨ W8 j)
    (liveC : ∀ gC, a₀.lookHeard = some gC → ∀ j, WC j → liveAt (plainOf gC.rows.toList) j = true)
    (live4 : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j, W4 j → liveAt (plainOf lf ++ layersBack o) j = true)
    (liveD : ∀ gD, a₀.tl.heard = some gD → ∀ j, WD j → liveAt (plainOf gD.rows.toList) j = true)
    (live8 : ∀ gD, a₀.tl.heard = some gD → ∀ j, W8 j → liveAt (K9L.four8 a₀.tl gD) j = true)
    (unC : ∀ gC, a₀.lookHeard = some gC → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf gC.rows.toList) j = true)
    (un4 : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf lf ++ layersBack o) j = true)
    (unD : ∀ gD, a₀.tl.heard = some gD → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf gD.rows.toList) j = true)
    (un8 : ∀ gD, a₀.tl.heard = some gD → ∀ j < n, mergeOf s = some j →
      unnamedAt (K9L.four8 a₀.tl gD) j = true) :
    LiveLayers p4 s a₀ n := fun gC gD o lf H => by
  have G := goodCut_of_shares n (mergeOf s) gC.rows.toList lf gD.rows.toList (K9L.four8 a₀.tl gD)
    (k8Len a₀.tl o.funs) (K4Values.backForms o) _ (four8_own a₀.tl gD) WC W4 WD W8 cover (liveC gC H.calls)
    (live4 gC gD o lf H) (liveD gD H.digits) (live8 gD H.digits) (unC gC H.calls) (un4 gC gD o lf H)
    (unD gD H.digits) (un8 gD H.digits) (Nat.le_refl _)
  unfold goodCut at G
  rw [Bool.and_eq_true] at G
  exact G.1

/-- **"LIVE" AT A FEED-FORWARD SEGMENT**: `goodLayers_of_clauses` (Honest/K9/GoodLayPaid.lean) less its premise len:
nine premises. -/
theorem liveLayers_of_clauses (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat)
    {pC pD : First.Look.P} {hC hD : Forest.Shape} (spC : pC.shape = some hC) (spD : pD.shape = some hD)
    (JC : Clause pC a₀.lookHeard) (JD : Clause pD a₀.tl.heard)
    (outC : ∀ j < n, mergeOf s = some j → Outside pC hC j) (outD : ∀ j < n, mergeOf s = some j → Outside pD hD j)
    (W4 : Nat → Prop)
    (cover : ∀ j < n, mergeOf s ≠ some j →
      InWin pC hC Run.objects j ∨ W4 j ∨ (pD.first ≤ j ∧ j < pD.first + Forest.elems hD))
    (live4 : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j, W4 j → liveAt (plainOf lf ++ layersBack o) j = true)
    (un4 : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf lf ++ layersBack o) j = true) :
    LiveLayers p4 s a₀ n := by
  refine liveLayers_of_shares p4 s a₀ n (InWin pC hC Run.objects) W4 (InWin pD hD Run.objects)
    (fun j => InWin pD hD Run.planes j ∨ InWin pD hD Run.join j) ?_ (pay_live spC JC) live4 (pay_live spD JD)
    (pay_live8 a₀.tl spD JD) (fun g hg j hj hm => pay_unnamed spC JC g hg j (outC j hj hm)) un4
    (fun g hg j hj hm => pay_unnamed spD JD g hg j (outD j hj hm))
    (fun g hg j hj hm => pay_unnamed8 a₀.tl spD JD g hg j (outD j hj hm))
  intro j hj hm
  rcases cover j hj hm with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨r, hr⟩ := (stretch_iff pD hD j).1 h
    cases r with
    | objects => exact Or.inr (Or.inr (Or.inl hr))
    | planes => exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
    | join => exact Or.inr (Or.inr (Or.inr (Or.inr hr)))

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.LiveLayers
#print axioms ProofFile.Honest.K9.liveLayers_of_good
#print axioms ProofFile.Honest.K9.goodW_layers_live
#print axioms ProofFile.Honest.K9.liveLayers_of_shares
#print axioms ProofFile.Honest.K9.liveLayers_of_clauses
