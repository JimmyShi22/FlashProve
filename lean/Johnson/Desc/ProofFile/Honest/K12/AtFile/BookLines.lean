-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/BookLines.lean: the book's rows at the two sendings: each row covers
what the sending's part takes and holds no more: first at the written term `bookShort`, by the kernel, then
at the book that the maker returns at the written description.

  `rows_maker`   the maker's rows are `bookShort`'s
  `cover_two`, `cover_five`, `count_two`, `count_five`   the closed lines; `cover_bent`: control
  `covers_head`  the premises c2, c5, n2, n5 of `words_tied_U` and `acceptedS_head_U`

The premise hBW: the maker returns at the written description. `bookWhole_same_at_laid`
(Honest/K14/BookWholeAtHead.lean) carries it to the description at the head, that is hB there.

Limits. Public rows alone: nothing on coins. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LaysLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableShared

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (jobU jobOmega sendPlace sendingPart)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.K12.Light (written_at_head qAt_written planOf)

/-- The maker's rows are `bookShort`'s. -/
theorem rows_maker {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (ch : ℕ) : B.rowsOf ch = bookShort.rowsOf ch := by
  unfold bookWhole at hB
  obtain ⟨R, hR, hc⟩ := BookShared.ex_bindE hB
  obtain rfl := checked_ok hc
  obtain ⟨e1, e2, e3⟩ := AtFullSide.K14.rawBookRows_written _ R hR
  unfold ProverCoinCounts.rowsOf
  rw [e1, e2, e3]
  rfl

theorem cover_two : (realSized.all fun q =>
    takesCover bookShort ⟨sendPlace 2, 0⟩ (jobU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))) = true := by decide +kernel

theorem cover_five : (realSized.all fun q =>
    takesCover bookShort ⟨sendPlace 5, 0⟩ (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))) = true := by decide +kernel

/-- Control: the second sending's part takes more than the first's row has. -/
theorem cover_bent : (realSized.all fun q =>
    takesCover bookShort ⟨sendPlace 2, 0⟩ (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))) = false := by
  decide +kernel

theorem count_two : (realSized.all fun q =>
    decide ((dueAt (bookShort.rowsOf 1) ⟨sendPlace 2, 0⟩).e =
      (sendingPart (jobU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))).takes.e)) = true := by decide +kernel

theorem count_five : (realSized.all fun q =>
    decide ((dueAt (bookShort.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
      (sendingPart (jobOmega (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape))).takes.e)) = true := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The premises c2, c5, n2, n5 at the maker's book.** -/
theorem covers_head (h : P5J.AtMg o Z D r Zp Np cF) {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) :
    takesCover B ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true ∧
      takesCover B ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true ∧
      (dueAt (B.rowsOf 1) ⟨sendPlace 2, 0⟩).e = (sendingPart (jobU ⟨K1.qAt Zp Np, 0⟩)).takes.e ∧
      (dueAt (B.rowsOf 1) ⟨sendPlace 5, 0⟩).e =
        (sendingPart (jobOmega ⟨K1.qAt Zp Np, 0⟩)).takes.e := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have a2 := cover_two
  have a5 := cover_five
  have k2 := count_two
  have k5 := count_five
  rw [hx] at a2 a5 k2 k5
  simp only [Option.all_some, decide_eq_true_eq] at a2 a5 k2 k5
  have er := rows_maker hB 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold takesCover at a2 ⊢
    rw [er, qAt_written Wr Np]
    exact a2
  · unfold takesCover at a5 ⊢
    rw [er, qAt_written Wr Np]
    exact a5
  · rw [er, qAt_written Wr Np]
    exact k2
  · rw [er, qAt_written Wr Np]
    exact k5

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.rows_maker
#print axioms ProofFile.Honest.K12.AtFile.cover_two
#print axioms ProofFile.Honest.K12.AtFile.cover_five
#print axioms ProofFile.Honest.K12.AtFile.cover_bent
#print axioms ProofFile.Honest.K12.AtFile.count_two
#print axioms ProofFile.Honest.K12.AtFile.count_five
#print axioms ProofFile.Honest.K12.AtFile.covers_head
