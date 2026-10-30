-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/BatFrontHanded.lean: `BatFrontLay` (Honest/K9/FallFormLay.lean: the one sentence on the
state for which K9's fall's bound at the twelve feed-forward segments is exchanged) AT THE STATES THAT THE FRAME's FIELD
HANDS IN FRONT OF THE BATCHING, WITH FIVE OF ITS NINE PREMISES PAID AND FOUR ASKED. NOT THE TWIN OF THE SMALLNESS TEST's
HOUSE's `attClauses_handed` YET: A FRAME FOR IT. One statement and its proof; no definition; no goal is stated.
  **`batFrontLay_handed`**   under the head · the two public places pC, pD of the segment's lookups · the lookups' marks
      and the fit's among the marks asked · the walk's premises at A.length = 14 (2 g) + 9 · p4, n: LETTERS · hrest: at
      the part a₀ at which s' stands and the two places' shapes: `LayRest` (Honest/K9/GoodLayRest.lean: outC · cover ·
      live4 · un4). PAID: spC, spD (public: `site_pars`) · JC, JD (`looksClauses_handed`,
      Johnson/P1K8R/ClausesAtLinks.lean: from the marks' silence) · outD (`merge_below_digits`,
      Honest/K9/OutDHanded.lean)
WHAT IS NOT CLAIMED. hrest at anything: IT IS NOT SHOWN WHOLE: Honest/K9/BatFrontHandedK4.lean pays live4, un4 and outC in
it by the feed-forward layers' theorems, under premises of their own, and leaves cover. p4 and n are tied to the
segment by nothing here: the caller lays them. At n := 0 an empty W4 meets hrest and the end says nothing: it bites only
at the n that the fall asks (the tests' number of filled slots), where hrest is not shown. That any walk returns. NO
MEMBER: no walk, state or list of marks is shown at which the premises hold together. Called by
Honest/K9/BatFrontHandedK4.lean alone. At the full size and the format's second hash function alone. Nothing on any property.
GROUND: beneath this file lie 512 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodLayRest
import Johnson.Desc.ProofFile.Honest.K9.FallFormLay
import Johnson.Desc.ProofFile.Honest.K9.OutDHanded
import Johnson.P1K8R.ClausesAtLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

/-- **`BatFrontLay` AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING, WITH FIVE
OF THE NINE PREMISES PAID**: the two shapes (public), the lookups' two clauses (from the silence of the lookups' marks
and the fit's) and outD; the other four are asked as `LayRest` (Honest/K9/GoodLayRest.lean). -/
theorem batFrontLay_handed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) {g : ℕ} (hg : g < 12)
    {pC pD : Look.P} (hC : Look.placeAt (P5J.At.X Zp) (2 * g) false = some pC)
    (hD : Look.placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (ms : List Mark) (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * (2 * g) + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {w₀ z : ProofFile.Honest.ChainProgress S ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true)
    (ha : ProofFile.Honest.ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) [] = .ok w₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr w₀ = .ok z) (hv : z.ver = some s')
    (p4 : OnBytes.Desc.First.K4.Par) (n : ℕ)
    (hrest : ∀ a₀ hsC hsD, s'.here = .lay a₀ → pC.shape = some hsC → pD.shape = some hsD →
      LayRest p4 s' a₀ n pC pD hsC hsD) :
    BatFrontLay p4 n s' := by
  intro a₀ ha₀
  obtain ⟨JC, JD⟩ := P1K8.looksClauses_handed h G₀ (l := 2 * g) (by omega) hC hD ms hsub hall hfit hA hpos L hft
    hm ha hn hq hz hv
  -- the two shapes
  obtain ⟨s, hs, el, hd, -, -⟩ := site_at_all_fifty h (2 * g) (by omega) false
  obtain ⟨sD, hsD, elD, hdD, -, -⟩ := site_at_all_fifty h (2 * g) (by omega) true
  obtain rfl : s.p = pC := by
    have k := (P1K8.site_pars s hs).1
    rw [el, hd] at k
    exact Option.some.inj (k.symm.trans hC)
  obtain rfl : sD.p = pD := by
    have k := (P1K8.site_pars sD hsD).1
    rw [elD, hdD] at k
    exact Option.some.inj (k.symm.trans hD)
  have spC := (P1K8.site_pars s hs).2
  have spD := (P1K8.site_pars sD hsD).2
  -- what the state holds as heard is what its part holds
  have eC : s'.lookHeard? = a₀.lookHeard := by simp [S.lookHeard?, ha₀]
  have eD : s'.tl?.bind (·.heard) = a₀.tl.heard := by simp [S.tl?, ha₀]
  rw [eC] at JC
  rw [eD] at JD
  exact liveLayers_of_rest p4 s' a₀ n spC spD JC JD
    (merge_below_digits h hg hD ms hall hfit hA hpos L hft hm ha hn hq hz hv) (hrest a₀ _ _ ha₀ spC spD)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batFrontLay_handed
