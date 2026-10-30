-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/ToldAt.lean: the code switch's law at the closed constant (mgAtAll):
THE TIE FROM THE WRITTEN CUT OF THE FIRST CHAIN TO THE CONSTANT's OWN NUMBERS ON THE BOOK: the three
readers of At.N Zp cF that WrittenAt.lean leaves because they are laid off what the chain's
sub-protocols tell.
  rowTold · toldFull  what a row of the written cut (cutFirstFull) tells; the list of these: A
               CLOSED TERM
  toldOf_of_cut  a list of sub-protocols with the written cut tells the written list. By
               toldRounds_flat (Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean)
  AtTold       told : At.told cF = toldFull · treesAt · msgsAt : at a place p: treesTold | msgsTold
               of toldFull at p's border in the written list of places · indexNo : msgNoOf toldFull
               at N0Full's index
  at_told      it holds where the chain has the written cut, under WrittenAt.lean's AtWritten
  told_trees   a look by Lean's kernel: the written cut tells 83 trees in all, none in front of the
               first sub-protocol
THE ONE NAMED PREMISE, IN THE FORM THAT ALL TAKE: hcut : PlanWritten.cutOf cF.blocksInOrder = cutFirstFull.
ITS PAYERS: cut_of_row (from its entry test cutRow) · pins_of_laid (Goal/Skeleton/PinsOfLaid.lean:
in scope, from LaidAt, over the proof file's entry tests when they had thirteen rows; this library's
have fourteen). NOT IN IT: rowsAt. withRows lays it off possAt cF.blocksInOrder: the positions that
the code switches' declared rounds draw. The cut's rows hold each sub-protocol's NUMBER of rounds,
not their entries: hcut alone does not give it (by report). K2's LAW SPENDS IT: the
debts on the table's numbers (Johnson/P1K2R/DebtsAt.lean's premise hcl: possAt … = n.positions).
LIMITS. A join and one look. No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.Desc.Ok.PlanWritten.CutTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes
open VerifiableInference.Desc (Chain Block Place Oracle)
open VerifiableInference.PlanWritten (cutFirstFull toldRounds toldRounds_flat)
open P5T (N0Full)
open P5J (TS)

/-- What a row of the written cut tells. -/
def rowTold (r : String × Place × ℕ × ℕ × List (ℕ × List Oracle) × List (ℕ × ℕ)) : List Oracle :=
  r.2.2.2.2.1.flatMap (·.2)

/-- **What the first chain's sub-protocols tell, by the written cut.** A closed term. -/
def toldFull : List (List Oracle) := cutFirstFull.map rowTold

/-- **A list of sub-protocols with the written cut tells the written list.** -/
theorem toldOf_of_cut {St Cl : Type} {bs : List (Block St Cl)}
    (h : PlanWritten.cutOf bs = cutFirstFull) : toldOf bs = toldFull := by
  unfold toldFull
  rw [← h]
  unfold PlanWritten.cutOf toldOf
  rw [List.map_map]
  refine List.map_congr_left fun b _ => ?_
  exact (toldRounds_flat b).symm

/-- **THE CONSTANT's NUMBERS ON THE BOOK ARE THE WRITTEN CUT's.** -/
structure AtTold (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) : Prop where
  told : P5J.At.told cF = toldFull
  treesAt : (P5J.At.N Zp cF).treesAt = fun p => treesTold toldFull (borderOf P5J.At.ps p)
  msgsAt : (P5J.At.N Zp cF).msgsAt = fun p => msgsTold toldFull (borderOf P5J.At.ps p)
  indexNo : (P5J.At.N Zp cF).indexNo = msgNoOf toldFull N0Full.index

theorem at_told {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} 
    (hcut : PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) (A : AtWritten Zp cF) : AtTold Zp cF := by
  have ht : P5J.At.told cF = toldFull := (P5J.At.told_is cF).trans (toldOf_of_cut hcut)
  refine ⟨ht, ?_, ?_, ?_⟩
  · show (fun p => treesTold (P5J.At.told cF) (borderOf P5J.At.ps p)) = _
    rw [ht]
  · show (fun p => msgsTold (P5J.At.told cF) (borderOf P5J.At.ps p)) = _
    rw [ht]
  · show msgNoOf (P5J.At.told cF) (P5J.At.N Zp cF).index = _
    rw [ht, A.index]

set_option maxRecDepth 1000000 in
/-- **A look by the kernel**: the written cut tells 83 trees in all; none in front of the first
sub-protocol. -/
theorem told_trees : treesTold toldFull 358 = 83 ∧ treesTold toldFull 0 = 0 := by decide +kernel

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.toldOf_of_cut
#print axioms VerifiableInference.Desc.First.K2Ties.at_told
#print axioms VerifiableInference.Desc.First.K2Ties.told_trees
