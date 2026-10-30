-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/PlanSitsCore.lean: THE FIVE TESTS ON THE LIST OF ROUNDS (`ToldDesc.PlanSits`), FIELD BY
FIELD, FROM THE HEAD ALONE: at the one head in front of the composed meaning's constant (`AtMg`,
Johnson/P5J/AtMg.lean): the index masks' message has the number 4 and W the number 197; in the list
of seats they sit where the first table's numbers say; in the list of shapes they have the shapes
that the planner's sizes say. And the number of oracle messages at the first chain's end: 199.

Why in this form. `PlanSits L M V idx nW` and the value V := `LLT25.vAt Zp (At.N Zp cF)` stand in
files that this file does not import. `PlanSits` is a structure of five look-ups; `vAt` is a
structure of four terms. Here the five look-ups are stated with the four terms written out: so the
structure is had from `AtMg.five_at_head` by its constructor.

WHICH HEAD. The head over the entry tests' list of thirteen rows (ProofAsksFirstThirteenTests.lean): both rows on
written values are spent (`AtMg.made_accepts`, `AtMg.cut_written`, Johnson/P5J/NumbersAtHead.lean).
Over the earlier list of eight rows (ProofAsksFirstEightTests.lean) nothing here can be had.

WHICH L, M AND nW. By report the meant terms are: L with `laidAtCodes
Zp.first.codes Zp.made.proof.1 = some L`; M := `msgsOfChain Zp.made.proof.1`; nW := `L.places.idxOf
(At.N Zp cF).w`. (`At.laid? Zp`, Johnson/P5J/LettersAt2.lean, is the first by unfolding.) Under the
head L and M are the written `LFull` and `MFull` (Johnson/HB/LLHARD/LaidWritten.lean), and nW is
197: `AtMg.laid_codes_at_head`, `AtMg.laid_at_head`, `AtMg.msgs_at_head`, `AtMg.nW_at_head`. The
five are stated in both spellings of L and M, at the numeral.

  `AtMg.told_at_head`: what the first chain's sub-protocols tell is the written list (`toldCut`,
    Johnson/Desc/First/CutWritten.lean).
  `AtMg.indexNo_at`: the index masks' message's number is 4 (`indexNo_of`,
    Johnson/HB/LLHARD/ToldCounts.lean; `treesAre_cut`, Johnson/HB/LLHARD/CountsAtCut.lean).
    `AtMg.msgs_end`: 199 oracle messages at the chain's end (`toldCut_counts`).
  Closed facts, by Lean's kernel (`decide +kernel`): `places_written`: seats number 4 and 197 of
    `LFull` are (1, 0) and (82, 0). `shapes_written`: shapes number 4 and 197 of `MFull` are, at the
    written sizes, the first message at the start's and W's. `places_rejects`, `shapes_rejects`: the
    negative tests: with the two numbers swapped each of the four look-ups fails. `idx_written`: the
    seat (82, 0) stands first at the number 197; `idx_rejects`: the seat (1, 0) does not.
  **`AtMg.five_at_head`**: the five, at `LFull` and `MFull`. **`AtMg.five_at_terms`**: the five, at
    any L with `laidAtCodes Zp.first.codes Zp.made.proof.1 = some L` and at `msgsOfChain
    Zp.made.proof.1`.

THE NUMERALS ARE THE WRITTEN VALUES' NUMBERS: they hold under the head because the head's own field
holds tests that compare with written values. They are no fact on what the maker of the IOP as
written in Lean makes of given public files.

Limits. The full size alone. That a head can be had at given public files is not said here. Nothing
on soundness.
-/
import Johnson.P5J.NumbersAtHead
import Johnson.P5J.LettersAt2
import Johnson.HB.LLHARD.PlanInScope
import Johnson.HB.LLHARD.CountsAtCut
import Johnson.Desc.First.CutWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (toldCut told_at_written toldCut_counts msgsTold)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain laidAtCodes)
open VerifiableInference.Desc.K13.Law (LFull MFull laid_in_scope msgs_in_scope indexNo_of
  treesAre_cut places_fit)
open VerifiableInference.PlanWritten (proofSizedFull)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-! ## L, M and what is told -/

/-- **The list of seats is the written one.** -/
theorem AtMg.laid_codes_at_head (h : AtMg o Z D r Zp Np cF) :
    laidAtCodes Zp.first.codes Zp.made.proof.1 = some LFull :=
  laid_in_scope h.scope h.laid.pub h.made_accepts

/-- The same in the constant's own name for it. -/
theorem AtMg.laid_at_head (h : AtMg o Z D r Zp Np cF) : At.laid? Zp = some LFull :=
  h.laid_codes_at_head

/-- **The list of shapes is the written one.** -/
theorem AtMg.msgs_at_head (h : AtMg o Z D r Zp Np cF) : msgsOfChain Zp.made.proof.1 = MFull :=
  msgs_in_scope h.scope h.laid.pub h.made_accepts

/-- **What the first chain's sub-protocols tell is the written list.** -/
theorem AtMg.told_at_head (h : AtMg o Z D r Zp Np cF) : At.told cF = toldCut := by
  have e : At.told cF = VerifiableInference.Desc.First.toldOf cF.blocksInOrder :=
    List.map_congr_left fun _ _ => List.flatMap_id
  rw [e]
  exact (told_at_written (bs := cF.blocksInOrder) h.cut_written).2

/-- The number of oracle messages at the last border, at numbers laid off what is told. -/
theorem withTold_msgs_none (N : VerifiableInference.Desc.First.Numbers)
    (ps : List VerifiableInference.Desc.Place)
    (told : List (List VerifiableInference.Desc.Oracle)) :
    (N.withTold ps told).msgsAt none = msgsTold told ps.length := rfl

/-- **The index masks' message has the number 4.** -/
theorem AtMg.indexNo_at (h : AtMg o Z D r Zp Np cF) : (At.N Zp cF).indexNo = 4 := by
  unfold At.N
  rw [h.told_at_head]
  refine indexNo_of ?_ treesAre_cut _
  exact h.seats_at.2

set_option maxRecDepth 1000000 in
/-- **At the first chain's end there are 199 oracle messages.** -/
theorem AtMg.msgs_end (h : AtMg o Z D r Zp Np cF) : (At.N Zp cF).msgsAt none = 199 := by
  have hp : At.ps.length = 358 := places_fit.1
  unfold At.N
  rw [withTold_msgs_none, h.told_at_head, hp]
  exact congrArg (·.2.2.2) toldCut_counts

/-! ## The closed facts -/

set_option maxRecDepth 1000000 in
/-- Seats number 4 and 197 of the written list. -/
theorem places_written :
    LFull.places[4]? = some (1, 0) ∧ LFull.places[197]? = some (82, 0) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with the two numbers swapped both look-ups fail. -/
theorem places_rejects :
    ¬ LFull.places[197]? = some (1, 0) ∧ ¬ LFull.places[4]? = some (82, 0) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Shapes number 4 and 197 of the written list, at the written sizes. -/
theorem shapes_written :
    MFull[4]? = some ((proofSizedFull.request.atStart.head?.map (·.shape)).getD default) ∧
      MFull[197]? = some proofSizedFull.batch.shape.w := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with the two numbers swapped both look-ups fail. -/
theorem shapes_rejects :
    ¬ MFull[197]? = some ((proofSizedFull.request.atStart.head?.map (·.shape)).getD default) ∧
      ¬ MFull[4]? = some proofSizedFull.batch.shape.w := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The seat (82, 0) stands first at the number 197. -/
theorem idx_written : LFull.places.idxOf (82, 0) = 197 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: the seat (1, 0) does not. -/
theorem idx_rejects : ¬ LFull.places.idxOf (1, 0) = 197 := by decide +kernel

/-! ## The five -/

/-- **THE FIVE TESTS ON THE LIST OF ROUNDS, AT THE WRITTEN LISTS.** -/
theorem AtMg.five_at_head (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).indexNo < 197 ∧
      LFull.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index ∧
      LFull.places[197]? = some (At.N Zp cF).w ∧
      MFull[(At.N Zp cF).indexNo]? =
        some ((Zp.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) ∧
      MFull[197]? = some Zp.p.chains.made.sized.proof.batch.shape.w := by
  have hs : Zp.p.chains.made.sized.proof = proofSizedFull :=
    VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
      (VerifiableInference.PlanWritten.sized_of_made h.made_accepts)
  rw [h.indexNo_at, h.seats_at.1, h.seats_at.2, hs]
  exact ⟨by decide, places_written.1, places_written.2, shapes_written.1, shapes_written.2⟩

/-- **THE SAME AT THE TERMS IN WHICH THE FACTS ON REACHED STATES END.** -/
theorem AtMg.five_at_terms (h : AtMg o Z D r Zp Np cF) {L : Laid}
    (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    (At.N Zp cF).indexNo < 197 ∧
      L.places[(At.N Zp cF).indexNo]? = some (At.N Zp cF).index ∧
      L.places[197]? = some (At.N Zp cF).w ∧
      (msgsOfChain Zp.made.proof.1)[(At.N Zp cF).indexNo]? =
        some ((Zp.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) ∧
      (msgsOfChain Zp.made.proof.1)[197]? =
        some Zp.p.chains.made.sized.proof.batch.shape.w := by
  obtain rfl : LFull = L := Option.some.inj (h.laid_codes_at_head.symm.trans hL)
  rw [h.msgs_at_head]
  exact h.five_at_head

/-- **W's number, as a term: the first place of W's seat in the list of seats: it is 197.** -/
theorem AtMg.nW_at_head (h : AtMg o Z D r Zp Np cF) {L : Laid}
    (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) :
    L.places.idxOf (At.N Zp cF).w = 197 := by
  obtain rfl : LFull = L := Option.some.inj (h.laid_codes_at_head.symm.trans hL)
  rw [h.seats_at.1]
  exact idx_written

end P5J

#print axioms P5J.AtMg.laid_codes_at_head
#print axioms P5J.AtMg.laid_at_head
#print axioms P5J.AtMg.msgs_at_head
#print axioms P5J.AtMg.told_at_head
#print axioms P5J.withTold_msgs_none
#print axioms P5J.AtMg.indexNo_at
#print axioms P5J.AtMg.msgs_end
#print axioms P5J.places_written
#print axioms P5J.places_rejects
#print axioms P5J.shapes_written
#print axioms P5J.shapes_rejects
#print axioms P5J.idx_written
#print axioms P5J.idx_rejects
#print axioms P5J.AtMg.five_at_head
#print axioms P5J.AtMg.five_at_terms
#print axioms P5J.AtMg.nW_at_head
