-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/TreesOfCut.lean: the premises hI and hV of the law on the shared
chain, TO THE BINDERS' LETTERS: the index masks' message's and W's trees lie below the number of
trees that the first chain's sub-protocols tell. Statements with their proofs; nothing is evaluated
here.

  `oraclesOf_told`: what a chain's sub-protocols send (`oraclesOf`, Johnson/Desc/Block.lean) is what
    they tell (`toldOf`, Johnson/Desc/First/NumbersAtBlocks.lean), in a row.
  `t1_of_cut`: where the cut of the IOP as written in Lean is the written one, that number is 83 (by
    `told_at_written`, Johnson/Desc/First/CutWritten.lean, and `cut_tells`,
    Johnson/HB/LLHARD/CountsAtCut.lean).
  `hI_hV_at_cut`: **(Z)**: in the goals' scope, at the numbers (`Numbers.atBlocks`).

THE PREMISES: the four of `seats_in_scope` (Johnson/P5T/PlanSeatsTie.lean), and ONE MORE: the cut of
the sub-protocols is the written one: an accept of the verifier's second test gives it: its owners'
law; not called here. That the law's own list of sub-protocols is this bs is the caller's. Limits.
Nothing on soundness.
-/
import Johnson.HB.LLHARD.IdxBelowWritten
import Johnson.HB.LLHARD.CountsAtCut
import Johnson.Desc.First.CutWritten
import Johnson.Desc.First.NumbersAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open VerifiableInference.Desc.First (toldOf told_at_written toldCut)
open VerifiableInference.PlanWritten (cutFirstFull)

section
variable {St Cl : Type}

/-- What a chain's sub-protocols send is what they tell, in a row. -/
theorem oraclesOf_told (bs : List (Block St Cl)) : oraclesOf bs = (toldOf bs).flatten := by
  unfold oraclesOf toldOf
  rw [List.flatMap_def]
  congr 1
  exact List.map_congr_left fun b _ => by rw [List.flatMap_def, List.map_id]

/-- **Where the cut is the written one, the chain tells 83 trees.** -/
theorem t1_of_cut {bs : List (Block St Cl)} (h : PlanWritten.cutOf bs = cutFirstFull) :
    (oraclesOf bs).length = 83 := by
  rw [oraclesOf_told, (told_at_written h).2]
  exact cut_tells.2.2

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}

/-- **hI and hV, to the binders' letters**: at the numbers over a chain's sub-protocols whose
cut is the written one, against the number of trees that these tell. -/
theorem hI_hV_at_cut (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) {bs : List (Block St Cl)}
    (hc : PlanWritten.cutOf bs = cutFirstFull) (s : OnBytes.Params.ReqShape)
    (links : List First.ModelPart) :
    ((P5T.numbersOf (P5T.planSeats Z Z.D.1)).atBlocks s links bs).index.1 <
        (oraclesOf bs).length ∧
      ((P5T.numbersOf (P5T.planSeats Z Z.D.1)).atBlocks s links bs).w.1 <
        (oraclesOf bs).length := by
  rw [t1_of_cut hc]
  exact hI_hV_in_scope hW h hy hl

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.oraclesOf_told
#print axioms VerifiableInference.Desc.K13.Law.t1_of_cut
#print axioms VerifiableInference.Desc.K13.Law.hI_hV_at_cut
