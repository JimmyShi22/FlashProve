-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/EntryAtBook.lean: kind K13, the members' batching: what the book of coins that the
frame's maker returns at the proof file's description holds for the kind's two parts, written out.
Under the library's head h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) and the hypothesis that the book
is the one that `bookWhole` (Honest/BookWhole.lean) returns at the head's description and the public
part's own three lists of sendings. Statements with their proofs; no definition. At the full size
and at the hash `OnBytes.secondHashFunction` alone.

  `k13_book_written`   under h, that book is the one that `bookWhole` returns at the library's
     written plan, about which the evaluations of AtFullSide/K14/ speak
  `k13_entry_at_book`   **what the book holds for the two parts**: no coin of their own; nothing
     carried; part 0 spends nothing; part 1 spends one block, `rawK13Entry`
     (AtFullSide/K14/RawMineAtK13.lean): 37 coins of the extension field, from number 8660 on, of
     the part at ⟨⟨1, some 0, 1, .K1⟩, 0⟩, under the name of a block of the index-mask message. The
     kind's place is written out: ⟨1, none, 3, .K13⟩ (`k13Place_whereOf`,
     Johnson/Desc/ProofFile/Honest/K13/LotKind.lean)
  `spentBy_of_mine`   the entries by which p spends of o, out of those that name p as their spender
  `k13_spentBy_owner`, `k13_spentBy_other`   the same in the terms of the condition `fresh` of
     `Good` (Honest/Side.lean) at an owner: of that part's coins the kind's part 1 spends just this
     block, and of no other part's any

What it is for. The kind's part 1 borrows the coins under which it sends its 37 scalars. That they
are still uniform when it spends them is the condition `fresh` at their owner, at part 1's address.
`k13_spentBy_owner` says which block that instance of the condition is about, so that it is not met
vacuously.

Limits.
  * The owner's condition `fresh` is not shown here.
  * That the owner is the part which sends the index-mask message is not a statement here. The
    book's maker takes it for that sender: it finds it by a search in the plan's sendings
    (`ownerOf`, Honest/BookEntries.lean; at the written plan: Honest/K1/Law/OwnerAtWritten.lean).
  * The facts on the written book are evaluations in Lean's kernel (AtFullSide/K14/).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K13.LendRowAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (AtMgA TS)
open ProofFile.Honest.K14 (planAlike_at_head)
open AtFullSide.K14 (rawDueAtK13 rawSpentEAtK13_part0 rawSpentEAtK13_part1 rawCarryAtK13
  rawMineAtK13_part1 rawK13Entry)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}

include h in
/-- **Under h: the book that `bookWhole` returns at the head's description and the public part's own
three lists of sendings is the one that it returns at the written plan.** -/
theorem k13_book_written
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk) :
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk := by
  have A := planAlike_at_head h
  have hs : Zp.made.proof = proofSendsFull :=
    VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
      (VerifiableInference.Desc.K1.pin1_atAll h)
  rw [hs] at hW
  rw [mergesByName_alike A.first, bookWhole_planAlike A]
  exact hW

include h in
/-- **What the book holds for the kind's two parts.** -/
theorem k13_entry_at_book
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk) :
    (∀ j, j < 2 → dueAt (Bk.rowsOf 0) ⟨⟨1, none, 3, .K13⟩, j⟩ = ⟨0, 0⟩) ∧
      (∀ j, carryE Bk ⟨⟨1, none, 3, .K13⟩, j⟩ = []) ∧
      spentE Bk ⟨⟨1, none, 3, .K13⟩, 0⟩ = [] ∧
      spentE Bk ⟨⟨1, none, 3, .K13⟩, 1⟩ = [rawK13Entry] := by
  have hB := k13_book_written h hW
  refine ⟨fun j hj => ?_, rawCarryAtK13 hB, rawSpentEAtK13_part0 hB, rawSpentEAtK13_part1 hB⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h0 | rfl
  · obtain rfl : j = 0 := Nat.lt_one_iff.1 h0
    exact (rawDueAtK13 hB).1
  · exact (rawDueAtK13 hB).2

/-- The entries by which p spends of o, out of all the entries that name p as their spender. -/
theorem spentBy_of_mine (B : ProverCoinCounts) (o p : Addr) :
    B.spentBy o p = (B.ahead.filter fun e => e.spender == p).filter fun e =>
      e.owner == o && e.once := by
  unfold ProverCoinCounts.spentBy
  rw [List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  cases e.owner == o <;> cases e.spender == p <;> cases e.once <;> rfl

include h in
/-- **Of the coins of the part that owns the block in the book, the kind's part 1 spends just the
one block.** So the condition `fresh` at that part, at the kind's address, is about 37 coins. -/
theorem k13_spentBy_owner
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk) :
    Bk.spentBy ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨⟨1, none, 3, .K13⟩, 1⟩ = [rawK13Entry] := by
  rw [spentBy_of_mine, rawMineAtK13_part1 (k13_book_written h hW)]
  rfl

include h in
/-- Of no other part's coins does it spend any. -/
theorem k13_spentBy_other
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk) {o : Addr}
    (ho : o ≠ ⟨⟨1, some 0, 1, .K1⟩, 0⟩) : Bk.spentBy o ⟨⟨1, none, 3, .K13⟩, 1⟩ = [] := by
  rw [spentBy_of_mine, rawMineAtK13_part1 (k13_book_written h hW)]
  have e : (rawK13Entry.owner == o) = false := beq_eq_false_iff_ne.2 fun q => ho q.symm
  refine List.filter_eq_nil_iff.2 fun a ha => ?_
  obtain rfl := List.mem_singleton.1 ha
  show ¬ ((rawK13Entry.owner == o && rawK13Entry.once) = true)
  rw [e, Bool.false_and]
  exact Bool.false_ne_true

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_book_written
#print axioms AtFullSide.K13.k13_entry_at_book
#print axioms AtFullSide.K13.spentBy_of_mine
#print axioms AtFullSide.K13.k13_spentBy_owner
#print axioms AtFullSide.K13.k13_spentBy_other
