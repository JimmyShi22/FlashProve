-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/TiesAtLaid.lean

What it proves. "One owner and one start" in the goals' scope, at the full size: whatever book of
random values the maker returns (bookWhole) at the proof file's own description, the library's
written sendings and the merges that it reads off the first chain: the test on the book's entries
that our laws on a proximity test's pair of parts take as a premise (tiesB,
Johnson/Desc/ProofFile/Honest/K12/AgreeBook.lean) says yes at the folded row's test's place, at two
members, and at the request's own test's place, at three. No premise on a label, none on the
lending. At any earlier hash.

Names.
  tiesB_of_ahead   the test reads of a book its entries alone.
  wants_first, seg_first, filter_off, ahead_at   at an address outside the first chain the written
      list's entries are those of its eight written pieces.
  ties_written     it says yes at the written list of entries, at the two places.
  ties_bite        it can say no there.
  ties_at_laid     the law.

By what. Evaluations in Lean's kernel: on the spenders' chains in the written list's two long pieces
(the second behind the library's splitOn_eq and slice_toNat?_eq, Johnson/Unfolds/, as in
AtFullSide/K14/RawLengthsWritten.lean), and at its eight written pieces (rawShortW,
AtFullSide/K14/RawEntriesKit.lean). Of the authors of the honest side of the linear claim's shared
rounds (K14): bookWhole_returns_written_ahead (AtFullSide/K14/BookWholeWritten.lean: at the
library's written description WP and its written sendings the maker returns a book whose entries are
rawAheadW); bookWhole_same_at_laid (Johnson/Desc/ProofFile/Honest/K14/BookWholeAtHead.lean: that
very book it returns at the description, in scope, where the description is laid).

Limits.
- The full size alone. The laws at every plan are ties_second and ties_shared
  (Johnson/Desc/ProofFile/Honest/K12/AtProof/MakerBook.lean, MakerBookU.lean), under named premises.
- Two of the four proximity tests' places. Not the last group's test's; at G_omega's test's place,
  where the fold sends its own fresh table, the test says no (ties_bite): another law is wanted
  there.
- At the library's written sendings: that a run's sendings are these is another law (the library's
  pins, Johnson/IMR/SendsPinned.lean). The merges are mergesByName's: "Which masked sumchecks are
  merges is guessed" (the head of Johnson/Desc/ProofFile/Honest/AtPure.lean).
- The limits of BookWholeWritten.lean stand: two of rawAheadW's ten pieces are their makers' terms.
- That a filling's book is this book is not shown here.
- The numbers of members, 2 and 3, are written. That a job has so many is a caller's step: at the
  folded row's test's own job it is made in TiesAtHeadU.lean in this folder.
- One limit is raised at four theorems (wants_first, seg_first, ties_written, ties_bite):
  maxRecDepth to 1000000, as in Johnson/AtFull/ProofPlan/WP.lean.
- The file lies in the side library because it imports a file of it.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AgreeBook
import Johnson.Desc.ProofFile.Honest.K14.BookWholeAtHead
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K14.RawEntriesKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain Place)
open ProofFile.Honest (ProverCoinCounts Ahead Addr bookWhole mergesByName spentE carryE)
open ProofFile.Honest.K12 (tiesB)
open AtFullSide.K14 (rawAheadW rawWantsW rawSegW rawShortW)
open Johnson.G (proofSendsFull)
open P5J (TS)

/-- tiesB reads of a book its entries alone. -/
theorem tiesB_of_ahead (B B' : ProverCoinCounts) (h : B.ahead = B'.ahead) (pl : Place) (n : ℕ) :
    tiesB B pl n = tiesB B' pl n := by
  unfold tiesB spentE carryE
  rw [h]

set_option maxRecDepth 1000000 in
/-- Every stretch that the maker lays at the written description is spent in the first chain. By an
evaluation in Lean's kernel. -/
theorem wants_first :
    ((rawWantsW.map (·.entry)).all fun e => e.spender.place.chain == 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Every carrying entry of the chain of segments there is handed to a part of the first chain. By
an evaluation in Lean's kernel, behind the library's equations for String.splitOn and toNat?. -/
theorem seg_first : (rawSegW.all fun e => e.spender.place.chain == 1) = true := by
  unfold rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- Of such a list no entry names an address outside the first chain. -/
theorem filter_off (l : List Ahead) (h : (l.all fun e => e.spender.place.chain == 1) = true)
    (a : Addr) (ha : a.place.chain ≠ 1) : l.filter (fun e => e.spender == a) = [] := by
  rw [List.filter_eq_nil_iff]
  intro e he h2
  have h1 : e.spender.place.chain = 1 := beq_iff_eq.1 (List.all_eq_true.1 h e he)
  rw [beq_iff_eq.1 h2] at h1
  exact ha h1

/-- **At an address outside the first chain the written list's entries are those of its eight
written pieces** (rawShortW, AtFullSide/K14/RawEntriesKit.lean), in their order. -/
theorem ahead_at (a : Addr) (ha : a.place.chain ≠ 1) :
    rawAheadW.filter (fun e => e.spender == a) = rawShortW.filter fun e => e.spender == a := by
  unfold rawAheadW rawShortW
  simp only [List.filter_append, filter_off _ wants_first a ha, filter_off _ seg_first a ha,
    List.nil_append, List.append_nil]

set_option maxRecDepth 1000000 in
/-- **At the written list of the book's entries (rawAheadW, AtFullSide/K14/RawAheadWritten.lean) the
test on the book's entries says yes at the folded row's test's place, at two members, and at the
request's own test's place, at three.** Two evaluations in Lean's kernel. -/
theorem ties_written :
    tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨2, none, 9, .K12⟩ 2 = true ∧
      tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨3, none, 2, .K12⟩ 3 = true := by
  unfold tiesB spentE carryE
  dsimp only
  rw [ahead_at ⟨⟨2, none, 9, .K12⟩, 0⟩ (by decide),
    ahead_at ⟨⟨2, none, 9, .K12⟩, 0 + 1⟩ (by decide),
    ahead_at ⟨⟨3, none, 2, .K12⟩, 0⟩ (by decide), ahead_at ⟨⟨3, none, 2, .K12⟩, 0 + 1⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluations can fail: at one member more each says no; and at G_omega's test's place, where
the fold sends its own fresh table, it says no at the two members that are carried there. -/
theorem ties_bite :
    tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨2, none, 9, .K12⟩ 3 = false ∧
      tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨3, none, 2, .K12⟩ 4 = false ∧
      tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨2, none, 10, .K12⟩ 2 = false := by
  unfold tiesB spentE carryE
  dsimp only
  rw [ahead_at ⟨⟨2, none, 9, .K12⟩, 0⟩ (by decide),
    ahead_at ⟨⟨2, none, 9, .K12⟩, 0 + 1⟩ (by decide),
    ahead_at ⟨⟨3, none, 2, .K12⟩, 0⟩ (by decide), ahead_at ⟨⟨3, none, 2, .K12⟩, 0 + 1⟩ (by decide),
    ahead_at ⟨⟨2, none, 10, .K12⟩, 0⟩ (by decide),
    ahead_at ⟨⟨2, none, 10, .K12⟩, 0 + 1⟩ (by decide)]
  decide +kernel

/-- **"One owner and one start" in the goals' scope, with no premise on a label and none on the
lending**: whatever book the maker returns at the proof file's own description, the library's
written sendings and the merges that it reads off the first chain: tiesB says yes at the two places.
At any earlier hash. -/
theorem ties_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {B : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok B) :
    tiesB B ⟨2, none, 9, .K12⟩ 2 = true ∧ tiesB B ⟨3, none, 2, .K12⟩ 3 = true := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = B :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  have e : ∀ (pl : Place) (n : ℕ), tiesB B₀ pl n =
      tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] } pl n :=
    fun pl n => tiesB_of_ahead B₀
      { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] } hA pl n
  exact ⟨(e _ _).trans ties_written.1, (e _ _).trans ties_written.2⟩

end AtFullSide.K12

#print axioms AtFullSide.K12.tiesB_of_ahead
#print axioms AtFullSide.K12.wants_first
#print axioms AtFullSide.K12.seg_first
#print axioms AtFullSide.K12.filter_off
#print axioms AtFullSide.K12.ahead_at
#print axioms AtFullSide.K12.ties_written
#print axioms AtFullSide.K12.ties_bite
#print axioms AtFullSide.K12.ties_at_laid
