-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/BatFrontHandedMarks.lean: THE TWIN, AT THE TWELVE FEED-FORWARD SEGMENTS, OF THE
SMALLNESS TEST's HOUSE's `attClauses_handed`: `BatFrontLay` (Honest/K9/FallFormLay.lean: the one sentence on the state
for which K9's fall's bound there is exchanged) AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF THE BATCHING,
WHERE THE LOOKUPS' MARKS, K4's WIDER MARKS AND THE FIT's ARE AMONG THE MARKS ASKED AND ALL MARKS ASKED HAVE BEEN SILENT.
NO PREMISE ON A PUBLIC NUMBER OF THE LAYERS' DATA OR THE PLAN; NONE ON THE STATE: the lengths hA, hpos, hn are the
walk's, and h4, hu are hPr1's own, as at attention. One statement and its proof; no definition; no goal is stated. One
option is raised (maxHeartbeats).
  **`batFrontLay_handed_marks`**   under the head · hB · hsub: the lookups' marks are among the marks asked (G₀: their
      idle letter) · hsub4: the feed-forward layers' list `k4MarksWide Zp Bs.G₀` is · hfit: the fit's marks at
      the members in front are · the walk's premises at A.length = 14 (2 g) + 9 · h4: p4 is K4's parameters at 2 g · hu:
      u is the tests' numbers at 2 g. THE END: `BatFrontLay p4 u.2.2.filled s'`: h4, hu and the end are those of the
      premise hPr1 of `k9_fallDebt_form_lay_with` (Honest/K9/FallFormLayWith.lean). HOW: `batFrontLay_handed_filled`
      (Honest/K9/BatFrontHandedFilled.lean) with its four premises paid: hhp: `IM.k4_of` · hsub4 there: the
      mark at ⟨the layers' public data, the plan at g, g, 2 g, 3, 0, 2 g⟩ is a member of `k4MarksWide`, by that list's
      text · hll, hLam: the feed-forward layers' `llLam_at_base` (Honest/K4/Law/Live/AtBase.lean)
WHAT IS NOT CLAIMED. That any walk returns: at a prover whose walk returns at no challenges, and at challenges at which
a mark asked has spoken, the statement is true for nothing. THE LINK FROM THE FRAME's FIELD TO THE WALK's PREMISES is
not made here: it is `layE_handed` (Johnson/P1K8R/FieldAtLay.lean), and `firstAsks_k9` (Johnson/P1K8R/MemberAtK9.lean)
pays hPr1 at one condition: the caller's Pr together with `BatFrontLay` itself (a projection: that condition asks more
of the state than Pr). K9's BOUND THERE STAYS EXCHANGED, NOT PAID. That `k4MarksWide` stands in any list of marks. The
inequality hq that `k9_fallDebt_form_lay_with` asks beside hPr1. THE EVENT OF K4's FALL IS NOT SAVED
(Honest/K9/K4TextsHanded.lean): whoever sums shares may not drop that fall's
on the strength of this file. The head's segment. NO MEMBER: no walk, state or list of marks is shown at which the
premises hold together. Called by Johnson/P1K8R/FieldAtLay.lean alone. At the full size and the format's second hash
function alone. Nothing on any property.
GROUND: beneath this file lie 568 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.BatFrontHandedFilled
import Johnson.Desc.ProofFile.Honest.K4.Law.K4MarksWide
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.AtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K4 (k4MarkWide k4MarksWide)
open ProofFile.Honest.K4.Live (llLam_at_base)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

set_option maxHeartbeats 1000000 in
/-- **`BatFrontLay` AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING, WHERE THE
LOOKUPS' MARKS, K4's WIDER MARKS AND THE FIT's ARE AMONG THE MARKS ASKED AND THESE HAVE BEEN SILENT.** No premise on a
public number of the layers' data or the plan; none on the state (hA, hpos, hn: the walk's lengths; h4, hu: hPr1's). -/
theorem batFrontLay_handed_marks (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (G₀ : ProofFile.Ground) {g : ℕ} (hg : g < 12)
    (ms : List Mark) (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms) (hsub4 : ∀ mk ∈ k4MarksWide Zp Bs.G₀, mk ∈ ms)
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
  obtain ⟨hll, hLam⟩ := llLam_at_base h hB
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  obtain ⟨-, -, xm, -, -, -, -, -, -, -, hG, -⟩ := IM.k4_of h.scope h.reads O g hg
  have hmem : k4MarkWide ⟨Bs.G₀.W.layers, xm.2.hp, g, 2 * g, 3, 0, 2 * g⟩ ∈ k4MarksWide Zp Bs.G₀ := by
    unfold k4MarksWide
    exact List.mem_filterMap.2 ⟨g, List.mem_range.2 hg, by rw [hG]; rfl⟩
  exact batFrontLay_handed_filled h hB G₀ hg ms hsub hG 0 (2 * g) (hsub4 _ hmem) hll hLam hall hfit hA hpos L hft hm ha
    hn hq hz hv h4 hu

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batFrontLay_handed_marks
