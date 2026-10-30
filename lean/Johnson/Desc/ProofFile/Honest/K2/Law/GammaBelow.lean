-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/GammaBelow.lean: the kind "the code switch" (K2): THE NUMBERS
OF THE FOLDS' CHALLENGES OF THE SEGMENTS IN FRONT OF A GROUP LIE BELOW THE NUMBER OF ROUNDS IN FRONT
OF THE PLACE WHOSE SWITCH OPENS THAT GROUP. One definition (a test on public data, with code);
statements with their proofs.

  `gammaBelow` the test at m: every number in `Sg.gamma`, Sg among the first m + 1 written segments,
                    lies below `offW (noAt m)`
  `gammaBelowW` BY THE KERNEL: it accepts at all 25
  `gammaBelowW_can_fail` with one segment more in front it rejects, at each of the first 24
  `gamma_below_at_head` `AtMg` · the opening · m < 25 ⊢ ∀ Sg ∈ `(segmentsOf Zp Bs.G₀).take (m + 1)`,
                    ∀ g ∈ Sg.gamma, `g < roundsAhead cF.blocksInOrder (noAt m)`

The letters. `noAt m` (Johnson/P1K2R/CarryAtConst.lean): the number, in the chain's list of
sub-protocols, of the place whose switch opens group m + 1 · `offW k` (Johnson/LPFE1R/RowsQAt.lean):
the written number of rounds of the first k · `roundsAhead` (Johnson/Desc/K13/Honest/FoldCut.lean).
By: `segments_at_head` (Honest/K2/Law/PlacesWritten.lean), `roundsAhead_written`
(Honest/K2/Law/GammaHeard.lean), the library's `pins_of_laid`
(Johnson/Goal/Skeleton/PinsOfLaid.lean). NEAR, NOT CALLED: `gammaNumbersW` (GammaHeard.lean): each
segment's numbers are a stretch from the third round of its closing on.

Limits. ON PUBLIC NUMBERS ALONE: nothing on what a part has heard: that a list of challenges heard
in front of the switch's part has `roundsAhead cF.blocksInOrder (noAt m)` entries is said nowhere here.
Closed facts by Lean's kernel, replayed by no independent checker. The full size and the format's
second hash function alone, under the head. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.GammaHeard
import Johnson.Desc.ProofFile.Honest.K2.Law.TiesWritten
import Johnson.P1K2R.CarryAtConst
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open VerifiableInference.Desc.LinkJoin (offW)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **The test**, on public data: the numbers of the folds' challenges of the written segments in
front of group m + 1 lie below the written number of rounds in front of the place whose switch opens
that group. -/
def gammaBelow (m : Nat) : Bool :=
  (segsW.take (m + 1)).all fun Sg => Sg.gamma.all fun g =>
    decide (g < offW (VerifiableInference.Desc.First.K2Caller.noAt m))

set_option maxRecDepth 1000000 in
/-- **It accepts at all 25.** By Lean's kernel. -/
theorem gammaBelowW : ((List.range 25).all gammaBelow) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **It can fail**: with one segment more in front it rejects, at each of the first 24: a number of
the next segment's does not lie below. -/
theorem gammaBelowW_can_fail : ((List.range 24).all fun m =>
    !((segsW.take (m + 2)).all fun Sg => Sg.gamma.all fun g =>
      decide (g < offW (VerifiableInference.Desc.First.K2Caller.noAt m)))) = true := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD**: the numbers of the folds' challenges of the segments in front of group m + 1
lie below the number of rounds of the chain's sub-protocols in front of the place whose switch opens
that group. -/
theorem gamma_below_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {m : Nat} (hm : m < 25) :
    ∀ Sg ∈ (segmentsOf Zp Bs.G₀).take (m + 1), ∀ g ∈ Sg.gamma,
      g < roundsAhead cF.blocksInOrder (VerifiableInference.Desc.First.K2Caller.noAt m) := by
  intro Sg hSg g hg
  rw [segments_at_head h O] at hSg
  have k := List.all_eq_true.1 gammaBelowW m (List.mem_range.2 hm)
  have k2 := List.all_eq_true.1 (List.all_eq_true.1 k Sg hSg) g hg
  rw [roundsAhead_written (bs := cF.blocksInOrder) (P5J.pins_of_laid h.scope h.laid).2]
  exact of_decide_eq_true k2

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.gammaBelow
#print axioms ProofFile.Honest.K2.Law.gammaBelowW
#print axioms ProofFile.Honest.K2.Law.gammaBelowW_can_fail
#print axioms ProofFile.Honest.K2.Law.gamma_below_at_head
