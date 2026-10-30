-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/GoodHeadHandedMarks.lean: "GOOD" (`goodW`, Honest/K9/GateArms.lean) AT THE STATE THAT
THE FRAME's FIELD HANDS IN FRONT OF THE OUTPUT HEAD's SEGMENT's BATCHING, FROM THE SILENCE OF THE LISTED MARKS ALONE:
THE TWIN, AT l = 24, OF `batFrontLay_handed_marks` (Honest/K9/BatFrontHandedMarks.lean) AND OF THE SMALLNESS TEST's
HOUSE's `attClauses_handed`: a twin by its road and its premises; the three ends are of three kinds. One statement with
its proof, by two calls; no definition; no goal is stated.
**`goodW_head_handed_marks`** under the head · hB · the lookups' marks (`k3Marks Zp G₀`), the output
head's own rounds' (`part4Marks Zp Bs.G₀`), the smallness test's (`P1K8.part1Marks Zp Bs.G₀`) and the fit's among the marks
asked · the walk's premises at A.length = 347 · K9's seat at 24: `goodW p ‹the segment's gatherer› s' w.2.2.filled`: THE
END OF THE PREMISE hPr24 OF `k9_fallDebt_form_head_with` (Honest/K9/FallFormHeadWith.lean), to the sign. HOW:
`goodW_head_handed_of_k6` (Honest/K9/GoodHeadHanded.lean) at hK := `k6Good_handed` (Honest/K9/K6GoodHanded.lean), at the
ground Bs.G₀, whose public part is the head's (the sealed lemma `IM.Open.W`)
WHAT IS NOT CLAIMED. That any walk returns. ARGUED, STATED IN NO THEOREM: AT A FILLING WITH NO SIDE OF THE CLOSING (K10),
AS `widerFillAt` (`k10_ten`, Honest/K10/AtFill.lean), NO STEP IS TAKEN BEHIND NUMBER 12; THE PREMISES HERE STAND AT 347:
AT SUCH A FILLING THE THEOREM SPEAKS OF NOTHING. At the shipped filling (onlineFilling), which has the closings, nothing
here shows the premises met. (The statement stands in the walk's words: the link from the frame's field to these premises
is the smallness test's house's; it is not called here.) Nor that the marks are silent at any run;
how often a mark speaks: where one speaks the theorem says nothing: that is the marks' shares. hPr24
at any Pr. NO MEMBER: no walk, state or list of marks is shown at which the premises hold together. K9's BOUND AT THIS
SEGMENT IS EXCHANGED BY THIS, NOT PAID. IT STANDS OVER MANY FILES OF OTHER HOUSES THAT ARE NO PART OF THE SEALED LIBRARY:
those that the heads of GoodHeadHanded.lean and K6GoodHanded.lean name. u is a letter, read by nothing in the conclusion.
Called by no line. At the full size and the format's second hash function alone, as h. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodHeadHanded
import Johnson.Desc.ProofFile.Honest.K9.K6GoodHanded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3.Good (k3Marks)
open ProofFile.Honest.K6 (part4Marks)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

/-- **"GOOD" AT THE STATE THAT THE FRAME's FIELD HANDS IN FRONT OF THE HEAD's SEGMENT's BATCHING, FROM THE SILENCE OF
THE LISTED MARKS ALONE**: the twin, at l = 24, of `batFrontLay_handed_marks`. -/
theorem goodW_head_handed_marks (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (G₀ : ProofFile.Ground) (ms : List Mark)
    (hsub : ∀ mk ∈ k3Marks Zp G₀, mk ∈ ms) (hsubK : ∀ mk ∈ part4Marks Zp Bs.G₀, mk ∈ ms)
    (hsub1 : ∀ mk ∈ P1K8.part1Marks Zp Bs.G₀, mk ∈ ms)
    {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 347) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a₀ z : ProofFile.Honest.ChainProgress S ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true)
    (ha : ProofFile.Honest.ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) [] = .ok a₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a₀ = .ok z) (hv : z.ver = some s')
    {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp 24 kk Lk p w) (u : HTailF2) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' w.2.2.filled := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  exact goodW_head_handed_of_k6 h hB G₀ ms hsub hsub1 hall hfit hA hpos L hft hm ha hn hq hz hv Sd u
    (k6Good_handed h G₀ Bs.G₀ O.W ms hsub hsubK hall hfit hA hpos L hft hm ha hn hq hz hv)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.goodW_head_handed_marks
