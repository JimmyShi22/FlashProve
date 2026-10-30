-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/TiesOwnAtLaid.lean

What it proves. The fellow of TiesAtLaid.lean in this folder at the one proximity test of the proof
file whose first fold sends its own fresh table, the test on G_omega. Whatever book of random values
the maker returns (bookWhole) at the proof file's own description, the library's written sendings
and the merges that it reads off the first chain: the test on the book's entries that our law on
that test's pair of parts takes as a premise (tiesOB, agree_of_tiesO,
Johnson/Desc/ProofFile/Honest/K12/Own/AgreeOwn.lean) says yes at that test's place, at two members.
No premise on a label, none on the lending. At any earlier hash.

FIRST, WHAT IT IS NOT.
- A PUBLIC TEST ON THE BOOK's ENTRIES: a "true" counts nothing by itself.
- With agree_of_tiesO it gives that the two parts' readers agree at that book UNDER TWO PREMISES
  THAT STAY: that the lending returns (lendRow), and hrows.
- The full size alone. TiesAtLaid.lean's limits stand: the library's written sendings; the merges
  are mergesByName's; two of rawAheadW's ten pieces are their makers' terms; that a filling's book
  is this book is not shown.
- The number of members, 2, is written. That a job has so many is a caller's step.
- THE FOUR CONTROLS ALL FALL AT THE TEST's FIRST CLAUSE (at three members all three clauses fall
  together): its second and third clause have no control of their own here, and in the first the
  owner and the start are wrong together.
- It moves no count. Nothing on completeness, soundness or hiding.

Names.
  tiesOB_of_ahead   the test reads of a book its entries alone.
  tiesO_written     it says yes at the written list of entries, at G_omega's test's place.
  tiesO_bite        it can say no: there, at one member fewer and at one more; and at the two places
      where the table has come earlier.
  tiesO_at_laid     the law.

By what. ahead_at (TiesAtLaid.lean); evaluations in Lean's kernel at the written list's eight
written pieces (rawShortW, AtFullSide/K14/RawEntriesKit.lean); bookWhole_returns_written_ahead
(AtFullSide/K14/BookWholeWritten.lean) and bookWhole_same_at_laid
(Johnson/Desc/ProofFile/Honest/K14/BookWholeAtHead.lean), of the authors of the honest side of the
linear claim's shared rounds. The proofs are TiesAtLaid.lean's own, with the test's name and the
places turned. One limit is raised at two theorems: maxRecDepth to 1000000, as there.
The file lies in the side library because it imports a file of it.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtLaid
import Johnson.Desc.ProofFile.Honest.K12.Own.AgreeOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain Place)
open ProofFile.Honest (ProverCoinCounts Ahead Addr bookWhole mergesByName spentE carryE)
open ProofFile.Honest.K12.Own (tiesOB)
open AtFullSide.K14 (rawAheadW rawWantsW rawSegW rawShortW)
open Johnson.G (proofSendsFull)
open P5J (TS)

/-- tiesOB reads of a book its entries alone. -/
theorem tiesOB_of_ahead (B B' : ProverCoinCounts) (h : B.ahead = B'.ahead) (pl : Place) (n : ℕ) :
    tiesOB B pl n = tiesOB B' pl n := by
  unfold tiesOB carryE
  rw [h]

set_option maxRecDepth 1000000 in
/-- **At the written list of the book's entries the test says yes at G_omega's test's place, at two
members.** By an evaluation in Lean's kernel, behind ahead_at. -/
theorem tiesO_written :
    tiesOB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
      ⟨2, none, 10, .K12⟩ 2 = true := by
  unfold tiesOB carryE
  dsimp only
  rw [ahead_at ⟨⟨2, none, 10, .K12⟩, 0⟩ (by decide),
    ahead_at ⟨⟨2, none, 10, .K12⟩, 0 + 1⟩ (by decide)]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluation can fail: at one member fewer and at one more it says no; and at the two places
where the mask has come earlier it says no at their own numbers of members. -/
theorem tiesO_bite :
    tiesOB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨2, none, 10, .K12⟩ 1 = false ∧
      tiesOB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨2, none, 10, .K12⟩ 3 = false ∧
      tiesOB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨2, none, 9, .K12⟩ 2 = false ∧
      tiesOB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨3, none, 2, .K12⟩ 3 = false := by
  unfold tiesOB carryE
  dsimp only
  rw [ahead_at ⟨⟨2, none, 10, .K12⟩, 0⟩ (by decide),
    ahead_at ⟨⟨2, none, 10, .K12⟩, 0 + 1⟩ (by decide),
    ahead_at ⟨⟨2, none, 9, .K12⟩, 0⟩ (by decide),
    ahead_at ⟨⟨2, none, 9, .K12⟩, 0 + 1⟩ (by decide),
    ahead_at ⟨⟨3, none, 2, .K12⟩, 0⟩ (by decide), ahead_at ⟨⟨3, none, 2, .K12⟩, 0 + 1⟩ (by decide)]
  decide +kernel

/-- **In the goals' scope, with no premise on a label and none on the lending**: whatever book the
maker returns at the proof file's own description, the library's written sendings and the merges
that it reads off the first chain: tiesOB says yes at G_omega's test's place, at two members. At any
earlier hash. -/
theorem tiesO_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {B : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok B) :
    tiesOB B ⟨2, none, 10, .K12⟩ 2 = true := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = B :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  exact (tiesOB_of_ahead B₀
    { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] } hA _ _).trans
    tiesO_written

end AtFullSide.K12

#print axioms AtFullSide.K12.tiesOB_of_ahead
#print axioms AtFullSide.K12.tiesO_written
#print axioms AtFullSide.K12.tiesO_bite
#print axioms AtFullSide.K12.tiesO_at_laid
