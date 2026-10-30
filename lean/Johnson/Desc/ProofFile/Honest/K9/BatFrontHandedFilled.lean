-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/BatFrontHandedFilled.lean: `BatFrontLay` AT THE STATES THAT THE FRAME's FIELD HANDS IN
FRONT OF A FEED-FORWARD SEGMENT's BATCHING, AT K4's OWN PARAMETERS AND THE TESTS' NUMBER OF FILLED SLOTS: ITS END, h4
AND hu ARE THOSE OF THE PREMISE hPr1 OF `k9_fallDebt_form_lay_with` (Honest/K9/FallFormLayWith.lean). UNDER FOUR
PREMISES THAT THE SMALLNESS TEST's HOUSE's `attClauses_handed` HAS NOT: THREE PUBLIC FACTS AND ONE MEMBERSHIP: THE STEP
BENEATH THE TWIN (Honest/K9/BatFrontHandedMarks.lean). One statement and its proof; no definition; no goal is stated.
One option is raised (maxHeartbeats).
  **`batFrontLay_handed_filled`**   under the head · hB · the lookups' marks and the fit's among the marks asked · the
      walk's premises at A.length = 14 (2 g) + 9 · h4, hu · AND FOUR: hhp (which plan stands at g: public) · hsub4 (K4's
      wider mark at ⟨the layers' public data, hp, g, 2 g, 3, r0, sg⟩ is among the marks asked; r0, sg: idle letters) ·
      hll, hLam (two public numbers of the layers' data). HOW: the two public places by the sealed
      `P1K9.bothPlaces_at_head` · `batFrontLay_handed_nums` · `calls_first_lay`, `filled_le_digits_end`
      (Honest/K9/LayNumbers.lean) · `ground_used` (Honest/K9/PlanUsed.lean) · `seam_handed` (Honest/K9/SeamHanded.lean)
WHAT IS NOT CLAIMED. The four here: they are paid in Honest/K9/BatFrontHandedMarks.lean, hsub4 from
a premise on a list of marks. THE LINK FROM THE FRAME's FIELD TO THE WALK's PREMISES is not made
here: it is `layE_handed` (Johnson/P1K8R/FieldAtLay.lean), and `firstAsks_k9`
(Johnson/P1K8R/MemberAtK9.lean) pays hPr1 at one condition: the caller's Pr together with
`BatFrontLay` itself (a projection: that condition asks more of the state than Pr; K9's bound stays
exchanged, not paid). The inequality hq that `k9_fallDebt_form_lay_with` asks beside hPr1 is not
touched here. The join's caution on K4's fall's share holds here. That any walk returns. The head's
segment. NO MEMBER: no walk, state or list of marks is shown at which the premises hold together.
Called by Honest/K9/BatFrontHandedMarks.lean alone. At the full size and the format's second hash
function alone. Nothing on any property.
GROUND: beneath this file lie 563 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.BatFrontHandedNums
import Johnson.Desc.ProofFile.Honest.K9.LayNumbers
import Johnson.Desc.ProofFile.Honest.K9.PlanUsed
import Johnson.Desc.ProofFile.Honest.K9.SeamHanded
import Johnson.P1K9R.AreadyClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K4 (k4MarkWide)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

set_option maxHeartbeats 1000000 in
/-- **`BatFrontLay` AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING, AT K4's
OWN PARAMETERS AND THE TESTS' NUMBER OF FILLED SLOTS**: its end, and h4 and hu, are those of the premise hPr1 of
`k9_fallDebt_form_lay_with`. UNDER FOUR PREMISES BESIDE THE WALK's AND THE MARKS'. -/
theorem batFrontLay_handed_filled (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (G₀ : ProofFile.Ground) {g : ℕ} (hg : g < 12)
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
    {p4 : OnBytes.Desc.First.K4.Par} (h4 : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4)
    {u : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hu : Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u) :
    BatFrontLay p4 u.2.2.filled s' := by
  obtain ⟨pC, pD, hC, hD⟩ := P1K9.bothPlaces_at_head h (2 * g) (by omega)
  have hused : hp.used ≤ hp.ns := by
    obtain ⟨Bs', base, O⟩ := h.laid.opened
    obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
    exact Nat.le_of_eq (ground_used h.scope h.reads O hg hhp)
  exact batFrontLay_handed_nums h hB G₀ hg hC hD ms hsub hhp r0 sg hsub4 hll hLam hall hfit hA hpos L hft hm ha hn hq
    hz hv h4 u.2.2.filled (calls_first_lay h hg hC)
    (seam_handed h hg hD ms hall hfit hA hpos L hft hm ha hn hq hz hv)
    (filled_le_digits_end h hB hg hD hu (fun hp' e => by
      obtain rfl : hp = hp' := Option.some.inj (hhp.symm.trans e)
      exact hused))

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batFrontLay_handed_filled
