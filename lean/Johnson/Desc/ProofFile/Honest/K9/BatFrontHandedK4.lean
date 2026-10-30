-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/BatFrontHandedK4.lean: `BatFrontLay` (Honest/K9/FallFormLay.lean) AT THE STATES THAT
THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING, AT K4's OWN PARAMETERS, WITH EIGHT OF ITS NINE
PREMISES PAID. NOT YET THE TWIN OF THE SMALLNESS TEST's HOUSE's `attClauses_handed`: ONE OF THE NINE (cover) AND THREE
PREMISES OF THE JOIN ARE ASKED. One statement and its proof; no definition; no goal is stated.
  **`batFrontLay_handed_k4`**   the premises of `k4_texts_handed` (Honest/K9/K4TextsHanded.lean: hsub4 · hll · hLam
      among them) · hD · h4: p4 IS K4's parameters at 2 g · n: a letter · hcov: at the part a₀ at which s' stands, what
      it holds (o; fo) and the two shapes: cover at W4 := `k4W4 (pC.first + Forest.elems hsC) fo a₀`, the
      feed-forward layers' own set of slots. PAID: spC, spD · JC, JD · outD (`batFrontLay_handed`,
      Honest/K9/BatFrontHanded.lean) · live4, un4 (`k4_texts_handed`) · outC (that theorem's inequality; the merge's
      slot is o.wo.sFv)
WHAT IS NOT CLAIMED. hcov here: it is paid by Honest/K9/CoverLay.lean, LayNumbers.lean, PlanUsed.lean and
SeamHanded.lean, laid together in BatFrontHandedFilled.lean. The join's three premises; its caution on K4's fall's share
holds here. At n := 0 hcov is met for nothing and the end says nothing. That any walk returns. NO MEMBER: no walk, state
or list of marks is shown at which the premises hold together. Called by Honest/K9/BatFrontHandedNums.lean alone. At the
full size and the format's second hash function alone. Nothing on any property.
GROUND: beneath this file lie 556 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.K4TextsHanded
import Johnson.Desc.ProofFile.Honest.K9.GoodLayRestK4
import Johnson.Desc.ProofFile.Honest.K9.BatFrontHanded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.K9 (mergeOf)
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3 (Run)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K3.Good.Live (Outside InWin)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty)
open ProofFile.Honest.K4 (k4MarkWide)
open ProofFile.Honest.K4.Live (k4W4)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

set_option maxHeartbeats 1000000 in
/-- **`BatFrontLay` AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING, AT K4's
OWN PARAMETERS, WITH EIGHT OF THE NINE PREMISES PAID**: left: cover, at the feed-forward layers' set of slots
(hcov); and what `k4_texts_handed` (Honest/K9/K4TextsHanded.lean) asks. -/
theorem batFrontLay_handed_k4 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (G₀ : ProofFile.Ground) {g : ℕ} (hg : g < 12)
    {pC pD : Look.P} (hC : Look.placeAt (P5J.At.X Zp) (2 * g) false = some pC)
    (hD : Look.placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (ms : List Mark) (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms)
    {hp : Layer.HPlan2} (hhp : Bs.G₀.W.G[g]? = some hp) (r0 sg : ℕ)
    (hsub4 : k4MarkWide ⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, r0, sg⟩ ∈ ms)
    (hll : Bs.G₀.W.layers.y.h.ll - 1 = 1) (hLam : Bs.G₀.W.layers.y.LamM ≤ 2)
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
    {p4 : OnBytes.Desc.First.K4.Par} (h4 : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) (n : ℕ)
    (hcov : ∀ (a₀ : LayOwn) (fo : Forest.Heard) (o : Layer.Own) (hsC hsD : Forest.Shape), s'.here = .lay a₀ →
      a₀.own = some o → a₀.lookHeard = some fo → pC.shape = some hsC → pD.shape = some hsD →
      ∀ j < n, mergeOf s' ≠ some j → InWin pC hsC Run.objects j ∨
        k4W4 (pC.first + Forest.elems hsC) fo a₀ j ∨ (pD.first ≤ j ∧ j < pD.first + Forest.elems hsD)) :
    BatFrontLay p4 n s' := by
  obtain ⟨p4', a, a₀, fo, o, hsC, e4, ha₀, hoa, hlk, spC, hnext, hle, l4, u4⟩ :=
    k4_texts_handed h hB G₀ hg hC ms hsub hhp r0 sg hsub4 hll hLam hall hfit hA hpos L hft hm ha hn hq hz hv n
  obtain rfl : p4 = p4' := Option.some.inj (h4.symm.trans e4)
  rw [hnext] at l4
  refine batFrontLay_handed h G₀ hg hC hD ms hsub hall hfit hA hpos L hft hm ha hn hq hz hv p4 n ?_
  intro a₁ hs1 hs2 ha₁ sp1 sp2
  obtain rfl : a₀ = a₁ := by
    have k := ha₀.symm.trans ha₁
    injection k
  obtain rfl : hsC = hs1 := Option.some.inj (spC.symm.trans sp1)
  have cov := hcov a₀ fo o hsC hs2 ha₀ hoa hlk spC sp2
  have hmo : mergeOf s' = some o.wo.sFv := OnBytes.Road.K4.mergeOf_own (by
    unfold S.own?
    rw [ha₀]
    exact hoa)
  have oC : ∀ j < n, mergeOf s' = some j → Outside pC hsC j := by
    intro j _ hj
    obtain rfl : o.wo.sFv = j := Option.some.inj (hmo.symm.trans hj)
    exact Or.inr hle
  exact layRest_of_texts p4 s' a₀ n pC pD hsC hs2 _ oC cov l4 u4

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batFrontLay_handed_k4
