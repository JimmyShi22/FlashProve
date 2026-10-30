-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/FenceTie.lean: THE TABLE's TEST `fenceFit` AT THE VERIFIER's OWN VALUE, IN THE GOALS'
SCOPE: the closed fact `fence_full` (Johnson/P5T/FenceFull.lean) carried from the written values
to the numbers that are made of a public part Z and of the first chain's own sub-protocols. Three
theorems. Nothing is evaluated here.
Why. A law on the first chain takes "`fenceFit N links ps = true`" as a premise, at the numbers N
that count. These are: the core off the seats (`numbersOf (planSeats Z Z.D.1)`), with `rowsAt`
laid (`withRows`), filled off what the sub-protocols tell (`withTold`).
  `fenceFit_withRows`: `withRows` turns the field `rowsAt` alone, which the test does not read.
  `fence_in_scope`: the test accepts there, from five premises: hW: the scope; h: the public part
  is made; hy: the test `madePinnedAt` on the sizes, the lists of rounds and the sendings accepts;
  hl: the value is laid (these four are those of `seats_in_scope`, Johnson/P5T/PlanSeatsTie.lean);
  hc: the cut of the sub-protocols bs is the written one.
  `fence_of_laid`: **FROM TWO PREMISES ALONE: the scope, and the value is laid**: there are F, the
  IOP as written in Lean that the maker returns, and the public part Z, and the test accepts at
  Z's numbers and F's own first chain. hy and hc are paid: the verifier's list of entry tests
  (`LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean) has, in its first thirteen rows, one for each
  (`madeRow`; `cutRow F`), and a laid value has passed every row: `laidPOf_pins_scope`
  (Johnson/Goal/Numbers/LaidPinsInScope.lean), `pinnedAt_of_row`
  (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean), `cut_of_row`
  (Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean).
Limits. `fence_of_laid` STANDS OVER THE LIST OF THIRTEEN ROWS ALONE: at the earlier list of eight
neither test is a row, and hy and hc are premises that nothing pays. Can its two premises be met?
The scope: at the two stored sets of public files it is a theorem (`VerifierAndGoals.filesRead`,
Johnson/Goal/Files/FilesReadProof.lean). That the value is laid under the list's thirteen
rows: Lean's evaluator has shown it at five sets of public files in scope, the two stored ones
among them (all thirteen rows accept; the value is laid): a run, no theorem. Outside the full
size's key the two rows accept without asking: the goals' scope is the full size alone. s, t, n
(the arguments of `withRows`) are letters. The full size alone. No probability: no soundness
follows.
Terms: lean/GLOSSARY.md.


-/
import Johnson.P5T.FenceFull
import Johnson.P5T.PlanSeatsTie
import Johnson.Desc.First.RowsAtPlan
import Johnson.Goal.Numbers.LaidPinsInScope
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.Ok.PlanWritten.CutTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt pinnedAt_of_row cut_of_row)

/-- `withRows` turns the field `rowsAt` alone, which the test does not read. -/
theorem fenceFit_withRows (N : Numbers) (s : OnBytes.Params.ReqShape) (t : Nat → Nat) (n : Nat)
    (links : List ModelPart) (ps : List Place) (told : List (List Oracle)) :
    fenceFit ((N.withRows s t n).withTold ps told) links ps =
      fenceFit (N.withTold ps told) links ps := rfl

/-- In the goals' scope the table's test on the fence accepts, from five premises. -/
theorem fence_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D} {r}
    {St Cl : Type} {bs : List (Block St Cl)}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r))
    (hc : VerifiableInference.PlanWritten.cutOf bs = cutFirstFull)
    (s : OnBytes.Params.ReqShape) (t : Nat → Nat) (n : Nat) :
    fenceFit (((numbersOf (planSeats Z Z.D.1)).withRows s t n).withTold
      (flatPlacesOf linksFull true) (toldOf bs)) linksFull (flatPlacesOf linksFull true) =
      true := by
  rw [fenceFit_withRows, (seats_in_scope hW h hy hl).2.2, (told_at_written hc).2, ← placesCut_is]
  exact fence_full

/-- **In the goals' scope, where the value is laid, the table's test on the fence accepts at the
verifier's own value.** -/
theorem fence_of_laid {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {D} {r}
    (hW : VerifierAndGoals.InScope W = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    ∃ F Z, ProofFile.onlineDescription o W.pol W.lay W.KL = .ok F ∧
      ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z ∧
      ∀ (s : OnBytes.Params.ReqShape) (t : Nat → Nat) (n : Nat),
        fenceFit (((numbersOf (planSeats Z Z.D.1)).withRows s t n).withTold
          (flatPlacesOf linksFull true) (toldOf F.first.blocksInOrder)) linksFull
          (flatPlacesOf linksFull true) = true := by
  obtain ⟨F, Z, hF, hZ, hm, hcR, -⟩ := LPFD.Full.laidPOf_pins_scope hW hl
  exact ⟨F, Z, hF, hZ, fun s t n =>
    fence_in_scope hW hZ (pinnedAt_of_row (by rw [hm, Bool.or_true])) hl (cut_of_row hcR).1 s t n⟩

end P5T

#print axioms P5T.fenceFit_withRows
#print axioms P5T.fence_in_scope
#print axioms P5T.fence_of_laid
