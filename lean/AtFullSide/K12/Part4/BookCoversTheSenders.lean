-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/BookCoversTheSenders.lean: AT THE MAKER's WRITTEN BOOK THE TWO SENDERS OF THE
FIRST CHAIN WHOSE TREES THE LAST CHAIN's PROXIMITY TEST TAKES OVER HAVE THEIR COINS: at every run's
coins the cut of each sender's own count is there.

WHAT IT IS NOT.
  * hB, that the book is the one made of the written description, is a premise.
  * It says that a cut is there, not what the coins are, how they are drawn, or who else reads them.
  * At the written plans parGF and parWF and the written rides alone.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; three theorems.

  countsAtTheWrittenBook   the written book's counts at the two senders' addresses are the two
                           sendings' own counts: an evaluation in Lean's kernel
  countsAreNotSwapped      a control: the first sender's count is not the second sending's
  bookCoversTheSenders     **the statement**: the premises coverIndex and coverW of
                           firstArmsOfTheTables (AtFullSide/K12/Part4/FirstArmsJoined.lean)

KIN. The first two clauses of written_W (AtFullSide/K12/HeldAtHeadW.lean, another author's) are
countsAtTheWrittenBook; they are evaluated anew here so that this file does not stand over that one.

CALLED. Of other authors: rawBookRows_written (AtFullSide/K14/RawBookRowsWritten.lean);
rawWhole_is_raw (AtFullSide/K14/RawMineAtK13.lean); lentCut_isSome (K1/ScriptAtLaw.lean).
-/
import AtFullSide.K12.Part4.JobAtTheHead
import AtFullSide.K14.RawBookRowsWritten
import AtFullSide.K14.RawMineAtK13
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Part4
open VerifiableInference.Desc.K1 (parGF parWF)
open ProofFile.Honest.K12.AtProof (senderI senderW)
open AtFullSide.K14 (rawRowsFirstW rawBookRows_written rawWhole_is_raw)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
/-- **The written book's counts at the two senders' addresses are the two sendings' own.** An
evaluation in Lean's kernel. -/
theorem countsAtTheWrittenBook :
    dueAt rawRowsFirstW senderI = K1.dueR parGF writtenRideOfTheIndexMasks ∧
      dueAt rawRowsFirstW senderW = K1.dueR parWF writtenRideOfW := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the first sender's count is not the second sending's. An evaluation in Lean's kernel.
-/
theorem countsAreNotSwapped :
    decide (dueAt rawRowsFirstW senderI = K1.dueR parWF writtenRideOfW) = false := by
  decide +kernel

/-- **At the maker's book, at every run's coins, each of the two senders' own cuts is there.** -/
theorem bookCoversTheSenders {Bk : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) :
    (∀ k : Coins Bk, ∃ c, (k.look 0 senderI).2.cut ⟨0, 0⟩
        (K1.dueR parGF writtenRideOfTheIndexMasks) = some c) ∧
      ∀ k : Coins Bk, ∃ c, (k.look 0 senderW).2.cut ⟨0, 0⟩
        (K1.dueR parWF writtenRideOfW) = some c := by
  obtain ⟨rows, -, -⟩ := rawBookRows_written _ Bk (rawWhole_is_raw hB)
  have firstRows : Bk.rowsOf 0 = rawRowsFirstW := rows
  have covered : ∀ (a : Addr) (d : Due), dueAt rawRowsFirstW a = d → ∀ k : Coins Bk,
      ∃ c, K1.lentCut k 0 a d = some c := by
    intro a d count k
    have isThere : (K1.lentCut k 0 a d).isSome = true := by
      rw [K1.lentCut_isSome k 0 (Nat.zero_le 1) a d]
      unfold K1.bookCovers
      rw [firstRows, count]
      exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
    exact Option.isSome_iff_exists.1 isThere
  exact ⟨covered _ _ countsAtTheWrittenBook.1, covered _ _ countsAtTheWrittenBook.2⟩

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.countsAtTheWrittenBook
#print axioms AtFullSide.K12.Part4.countsAreNotSwapped
#print axioms AtFullSide.K12.Part4.bookCoversTheSenders
