-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodLayPaid.lean: FOR K9's FALL ON THE FREE SLOT, AT A FEED-FORWARD SEGMENT:
`goodLayers_of_shares` (Honest/K9/GoodLayShares.lean) WITH SIX OF THE EIGHT BINDERS THAT IT ASKS OF OTHER HOUSES LAID IN
BY THE LOOKUPS' HOUSE's THEOREMS: liveC, liveD, live8 FROM THAT HOUSE's CLAUSE ALONE; unC, unD, un8 FROM THE CLAUSE AND
ONE NUMBER A LOOKUP, WHICH STAYS A PREMISE. THE LAWS ARE THAT HOUSE's; OURS IS THE JOIN. Statements and proofs ON THE
VERIFIER's DATA; no prover is in this file, and no goal is stated. No probability is in this file.
  **`goodLayers_of_clauses`**   `GoodLayers p4 s a₀ n` FROM: the two places' shapes (spC, spD) · JC, JD: the lookups'
      `Clause` (Honest/K3/Good/Live/Clause.lean) at what the state's part a₀ holds as heard by the lookup on the calls
      (`a₀.lookHeard`) and on the digits (`a₀.tl.heard`) · outC, outD: the merge's slot, where it lies below n, lies
      outside each lookup's stretch (that house's `Outside`) · a set W4 with K4's house's live4 and un4, as they stand
      in `goodLayers_of_shares` · cover: every slot below n but the merge's lies in the calls' window of "objects", or
      in W4, or in the digits' stretch · len
HOW. WC := the calls' window of "objects" · WD := the digits' · W8 := the digits' windows of "planes" and "join" (that
(`InWin`): `pay_live`, `pay_live8`, `pay_unnamed`, `pay_unnamed8` (Honest/K3/Good/Live/Shares.lean) ARE the
six binders at these sets; its `stretch_iff` (SharesCover.lean) cuts the digits' stretch into the three windows: SO THE
DIGITS' WHOLE STRETCH IS ANSWERED FOR; of the calls' stretch the window of "objects" alone: the two other windows there
stand in W4.
WHAT IS LEFT. live4, un4: K4's, with the lookups' laws on the forms' words · outC, outD, cover:
with K4's tiling of its own stretch · len: from each kind's lengths · JC, JD at a state in front
of the batching: each from that kind's law behind its own member, and a CARRIAGE, which is not typed.
WHAT IS NOT CLAIMED. Any premise at any state. That a W4 exists with which cover holds. NO MEMBER: no state is shown at
which the premises hold together; `Heard4` is shown of none; where `Heard4` fails `GoodLayers` holds idly. The places
pC, pD and their shapes are tied to s by nothing here. Called by no line. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 124 files, this one among them; by their folders: 16 of ours ·
85 of the lookups' · 12 of the hash build's · 11 of the frame's: reading copies, all but ours. The files under
Johnson/Desc/K9/Honest/ and Johnson/Desc/K8/Honest/ on which it also stands are the sealed library's.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodLayShares
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.SharesCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8.Honest (layersFront layersBack plainOf)
open VerifiableInference.Desc.K9 (mergeOf)
open VerifiableInference.Desc.K9H (liveAt unnamedAt)
open ProofFile.Honest.K3 (Run)
open ProofFile.Honest.K3.Good.Live (Clause Outside InWin pay_live pay_unnamed pay_live8 pay_unnamed8 stretch_iff)

/-- **"GOOD" AT A FEED-FORWARD SEGMENT, WITH SIX BINDERS LAID IN BY THE LOOKUPS' THEOREMS** (two of them, live8 and un8,
the form's K8's house's): from their clause at what the state's part holds as heard by the two lookups; the merge's slot
outside both stretches; K4's two binders; cover; len. -/
theorem goodLayers_of_clauses (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat)
    {pC pD : First.Look.P} {hC hD : Forest.Shape} (spC : pC.shape = some hC) (spD : pD.shape = some hD)
    (JC : Clause pC a₀.lookHeard) (JD : Clause pD a₀.tl.heard)
    (outC : ∀ j < n, mergeOf s = some j → Outside pC hC j) (outD : ∀ j < n, mergeOf s = some j → Outside pD hD j)
    (W4 : Nat → Prop)
    (cover : ∀ j < n, mergeOf s ≠ some j →
      InWin pC hC Run.objects j ∨ W4 j ∨ (pD.first ≤ j ∧ j < pD.first + Forest.elems hD))
    (live4 : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j, W4 j → liveAt (plainOf lf ++ layersBack o) j = true)
    (un4 : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf lf ++ layersBack o) j = true)
    (len : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf →
      (cutList (layersFront gC gD lf) (K9L.four8 a₀.tl gD) (k8Len a₀.tl o.funs) (layersBack o)).length ≤
        a₀.F.planClaimsF) :
    GoodLayers p4 s a₀ n := by
  refine goodLayers_of_shares p4 s a₀ n (InWin pC hC Run.objects) W4 (InWin pD hD Run.objects)
    (fun j => InWin pD hD Run.planes j ∨ InWin pD hD Run.join j) ?_ (pay_live spC JC) live4 (pay_live spD JD)
    (pay_live8 a₀.tl spD JD) (fun g hg j hj hm => pay_unnamed spC JC g hg j (outC j hj hm)) un4
    (fun g hg j hj hm => pay_unnamed spD JD g hg j (outD j hj hm))
    (fun g hg j hj hm => pay_unnamed8 a₀.tl spD JD g hg j (outD j hj hm)) len
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

#print axioms ProofFile.Honest.K9.goodLayers_of_clauses
