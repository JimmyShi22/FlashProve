-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public premises of trees_first at the written plan.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesLAt.lean: what trees_first (Sim2/TreesL.lean) asks of
public numbers: by Lean's kernel at the closed list of the code switch's places (placesW,
K2/Law/PlacesWritten.lean) and the written last test (piLFull), and under the head at the seated
place. Nothing on a run.

  finishWritten    the finish of the code switch at the closed list
  finishWritten_fits, finishWritten_width   fitsL and the column's words there
  fitsL_congr      fitsL reads of the test's parameters their numbers and their place
  fits_at_head, width_at_finish, source_at_head   the premises hfit, hW, hsrc of trees_first
  finish_at_head   under the head and the opening the finish is finishWritten
  trees_in_front_written, trees_to_at_head   the premise hj: 76 trees in front of block 353

Limits. That the finish stands at block number 353 is not shown here: the count 76 holds at the
numbers 345 to 353, read off where treesTold steps. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.PublicL
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K2.Law (placesW treesTo_at_head)
open H2K.Member (piLFull)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)

/-- The finish of the code switch, at the closed list. -/
def finishWritten : Option K2.SwitchPlace := placesW.find? fun p => p.place.link.isNone

/-- The public test of jobL at the written plan. -/
theorem finishWritten_fits : (finishWritten.map fun p => fitsL piLFull p) = some true := by
  decide +kernel

/-- A column's words at the written plan. -/
theorem finishWritten_width : (finishWritten.map fun p => columnWidth (finishSending p) 0 ==
    ((finishTrees p).shapes.getD 0 default).mainWidth +
      ((finishTrees p).shapes.getD 0 default).maskWidth) =
    some true := by decide +kernel

/-- fitsL reads of the test's parameters their numbers and their place. -/
theorem fitsL_congr {q q' : VerifiableInference.Desc.K12.P12} (p : K2.SwitchPlace)
    (hn : q.nums = q'.nums) (hp : q.place = q'.place) : fitsL q p = fitsL q' p := by
  unfold fitsL fitsLs
  rw [hn, hp]

/-- The written test's one first tree is own tree number 76. -/
theorem first_written : ∀ o ∈ piLFull.nums.first, o.2 = Fmt.TreeSource.own 76 := by
  decide +kernel

/-- 76 trees stand in front of block number 353. -/
theorem trees_in_front_written : treesTold toldFull 353 = 76 := by decide +kernel

section Head
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The seated test's numbers and place are the written ones. -/
theorem seated_written (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    (H2U.p12OfMade Zp.made).nums = piLFull.nums ∧ (H2U.p12OfMade Zp.made).place = piLFull.place := by
  rw [numbersL_at_head h]
  exact ⟨nums_head_L h, Blind.placeL_of_four Np⟩

/-- **hfit under the head**, where pl is the written finish. -/
theorem fits_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {pl : K2.SwitchPlace}
    (hf : finishWritten = some pl) : fitsL (H2U.p12OfMade Zp.made) pl = true := by
  have e := finishWritten_fits
  rw [hf] at e
  rw [fitsL_congr pl (seated_written h).1 (seated_written h).2]
  exact Option.some.inj e

/-- **hW**, where pl is the written finish. -/
theorem width_at_finish {pl : K2.SwitchPlace} (hf : finishWritten = some pl) :
    columnWidth (finishSending pl) 0 = ((finishTrees pl).shapes.getD 0 default).mainWidth +
      ((finishTrees pl).shapes.getD 0 default).maskWidth := by
  have e := finishWritten_width
  rw [hf] at e
  exact beq_iff_eq.1 (Option.some.inj e)

/-- **hsrc under the head.** -/
theorem source_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) :
    ∀ o ∈ (H2U.p12OfMade Zp.made).nums.first, o.2 = Fmt.TreeSource.own 76 := by
  rw [(seated_written h).1]
  exact first_written

/-- **Under the head and the opening the finish is the written one.** -/
theorem finish_at_head {Bs : ProofFile.PureBase}
    {base : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) :
    finishAt Zp Bs.G₀ = finishWritten := by
  unfold finishAt finishWritten
  rw [ProofFile.Honest.K2.Law.places_at_head h O]

/-- **hj under the head and the opening**, at 353 blocks in front. -/
theorem trees_to_at_head {Bs : ProofFile.PureBase}
    {base : List (VerifiableInference.Desc.Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) :
    treesTo cF.blocksInOrder 353 = 76 := by
  rw [treesTo_at_head h O]
  exact trees_in_front_written

end Head

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.finishWritten_fits
#print axioms ProofFile.Honest.K12.Sim2.finishWritten_width
#print axioms ProofFile.Honest.K12.Sim2.first_written
#print axioms ProofFile.Honest.K12.Sim2.trees_in_front_written
#print axioms ProofFile.Honest.K12.Sim2.fits_at_head
#print axioms ProofFile.Honest.K12.Sim2.width_at_finish
#print axioms ProofFile.Honest.K12.Sim2.source_at_head
#print axioms ProofFile.Honest.K12.Sim2.finish_at_head
#print axioms ProofFile.Honest.K12.Sim2.trees_to_at_head
