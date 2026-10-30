-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/CoverLay.lean: THE PREMISE cover OF `liveLayers_of_clauses`
(Honest/K9/GoodLayLive.lean), AT THE FEED-FORWARD LAYERS' HOUSE's SET OF SLOTS `k4W4`
(Honest/K4/Law/Live/GoodLayForm.lean), EXCHANGED FOR THE CALLS' CLAUSE AND THREE SENTENCES ON NUMBERS. One statement and
its proof; no definition; no state and no walk stand in it; no goal is stated.
  **`cover_k4W4`**   spC: the calls' shape · JC: the lookups' clause at what the calls' lookup has heard (fo) · hoa: the
      part a₀ holds o · h0: the calls' first slot is 0 · hseam: the digits' first slot is at most o.wo.sFv + 1 · hn: n
      is at most the end of the digits' stretch. THE END: every j < n other than o.wo.sFv lies in the calls' window
      "objects", in `k4W4 (pC.first + Forest.elems hsC) fo a₀`, or in the digits' stretch. HOW, IN FOUR STRIPS: the
      calls' stretch: the lookups' house's `stretch_iff` cuts it in three windows: "objects" is the first arm; "join":
      its `cEnd_sc` is `k4W4`'s second clause; "planes": its `planes_sc` is the third and the fourth · from the calls'
      end to below o.wo.sFv: `k4W4`'s first clause · o.wo.sFv itself is shut out · behind it: the digits' stretch, by
      hseam and hn
TO KNOW. The lookups' house's coefficient `sc` (Honest/K3/Good/Coef.lean) and the feed-forward layers' house's `cf
Reading.gl` (Honest/K4/Law/Live/Coef.lean) unfold to one term: Lean's kernel takes the one for the other here.
WHAT IS NOT CLAIMED. Any of the six premises at anything, in this file: at the states that the frame's field hands all
six are had in Honest/K9/BatFrontHandedNums.lean and BatFrontHandedFilled.lean (hn at the tests' number of filled slots
alone). NO MEMBER: no part, shape or number is shown at which they hold together. At n := 0 the end says nothing. Called
by Honest/K9/BatFrontHandedNums.lean alone. Nothing on any property.
GROUND: beneath this file lie 163 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.SharesCover
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Forms
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.GoodLayForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (LayOwn)
open ProofFile.Honest.K3 (Run)
open ProofFile.Honest.K3.Good.Live (Clause InWin stretch_iff cEnd_sc planes_sc)
open ProofFile.Honest.K4.Live (k4W4)

/-- **cover AT THE FEED-FORWARD LAYERS' HOUSE's SET OF SLOTS, FROM THE CALLS' CLAUSE AND THREE SENTENCES ON
NUMBERS.** -/
theorem cover_k4W4 {pC pD : First.Look.P} {hsC hsD : Forest.Shape} (spC : pC.shape = some hsC)
    {fo : Forest.Heard} (JC : Clause pC (some fo)) {a₀ : LayOwn} {o : Layer.Own} (hoa : a₀.own = some o) (n : ℕ)
    (h0 : pC.first = 0) (hseam : pD.first ≤ o.wo.sFv + 1) (hn : n ≤ pD.first + Forest.elems hsD) :
    ∀ j < n, j ≠ o.wo.sFv → InWin pC hsC Run.objects j ∨
      k4W4 (pC.first + Forest.elems hsC) fo a₀ j ∨ (pD.first ≤ j ∧ j < pD.first + Forest.elems hsD) := by
  intro j hj hne
  by_cases h1 : j < pC.first + Forest.elems hsC
  · -- the calls' stretch: three windows
    obtain ⟨r, hr⟩ := (stretch_iff pC hsC j).1 ⟨by omega, h1⟩
    cases r with
    | objects => exact Or.inl hr
    | join =>
      obtain ⟨j', hj', rfl⟩ := hr
      exact Or.inr (Or.inl (Or.inr (Or.inl (cEnd_sc spC JC hj'))))
    | planes =>
      obtain ⟨j', hj', rfl⟩ := hr
      rcases planes_sc spC JC hj' with k | k
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl k))))
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr k))))
  · by_cases h2 : j < o.wo.sFv
    · -- K4's own slots, below the merge's
      exact Or.inr (Or.inl (Or.inl ⟨o, hoa, by omega, h2⟩))
    · -- behind the merge's slot: the digits' stretch
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.cover_k4W4
