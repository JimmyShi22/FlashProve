-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/BatFrontHandedNums.lean: `BatFrontLay` (Honest/K9/FallFormLay.lean) AT THE STATES THAT
THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING: `batFrontLay_handed_k4`
(Honest/K9/BatFrontHandedK4.lean) WITH ITS PREMISE hcov (cover) EXCHANGED, NOT PAID, FOR THREE SENTENCES ON NUMBERS. One
statement and its proof; no definition; no goal is stated. One option is raised (maxHeartbeats).
  **`batFrontLay_handed_nums`**   that theorem's premises less hcov (the join's hsub4 · hll · hLam · hhp among them) ·
      h0: the calls' first slot is 0 · hseam: at the part at which s' stands and what it holds (o): the digits' first
      slot is at most o.wo.sFv + 1 · hnum: n is at most the end of the digits' stretch. HOW: `cover_k4W4`
      (Honest/K9/CoverLay.lean) at the clause that the smallness test's `looksClauses_handed` hands; the merge's
      slot is o.wo.sFv (`mergeOf_own`)
WHAT IS NOT CLAIMED. h0, hseam, hnum here: h0 is paid in Honest/K9/LayNumbers.lean, hseam in SeamHanded.lean, hnum AT n
:= the tests' number of filled slots ALONE in LayNumbers.lean over PlanUsed.lean; they are laid in by
Honest/K9/BatFrontHandedFilled.lean. The join's premises; its caution on K4's fall's share holds here. That any walk
returns. NO MEMBER: no walk, state or list of marks is shown at which the premises hold together. Called by
Honest/K9/BatFrontHandedFilled.lean alone. At the full size and the format's second hash function alone. Nothing on any
property.
GROUND: beneath this file lie 558 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.BatFrontHandedK4
import Johnson.Desc.ProofFile.Honest.K9.CoverLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.K9 (mergeOf)
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K4 (k4MarkWide)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

set_option maxHeartbeats 1000000 in
/-- **`BatFrontLay` AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING: EIGHT OF
THE NINE PREMISES OF `liveLayers_of_clauses` PAID, AND cover EXCHANGED, NOT PAID**: for three sentences on numbers (h0,
hseam, hnum). The join's premises (hsub4, hll, hLam; hhp) stand. -/
theorem batFrontLay_handed_nums (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
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
    (h0 : pC.first = 0)
    (hseam : ∀ (a₀ : LayOwn) (o : Layer.Own), s'.here = .lay a₀ → a₀.own = some o → pD.first ≤ o.wo.sFv + 1)
    (hnum : ∀ hsD, pD.shape = some hsD → n ≤ pD.first + Forest.elems hsD) :
    BatFrontLay p4 n s' := by
  refine batFrontLay_handed_k4 h hB G₀ hg hC hD ms hsub hhp r0 sg hsub4 hll hLam hall hfit hA hpos L hft hm ha hn hq
    hz hv h4 n ?_
  intro a₀ fo o hsC hsD ha₀ hoa hlk spC spD j hj hne
  obtain ⟨JC, -⟩ := P1K8.looksClauses_handed h G₀ (l := 2 * g) (by omega) hC hD ms hsub hall hfit hA hpos L hft
    hm ha hn hq hz hv
  have eC : s'.lookHeard? = some fo := by
    simpa [S.lookHeard?, ha₀] using hlk
  rw [eC] at JC
  have hmo : mergeOf s' = some o.wo.sFv := OnBytes.Road.K4.mergeOf_own (by
    unfold S.own?
    rw [ha₀]
    exact hoa)
  exact cover_k4W4 spC JC hoa n h0 (hseam a₀ o ha₀ hoa) (hnum hsD spD) j hj (fun e => hne (by rw [hmo, e]))

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batFrontLay_handed_nums
