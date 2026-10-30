-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/RunsAtLaidL.lean

What it proves. Which entries of the book of random values the two parts of the first chain's
proximity test spend and carry, by owner, start and count, as far as these bear on one owner: at
whatever book the maker returns (bookWhole) at the proof file's own description, the library's
written sendings and the merges that it reads off the first chain, in the goals' scope, at the full
size, at any earlier hash. The first part spends one entry, of the part at the code switch's finish,
from (0, 439), counting (0, 3); the second part spends none. They carry 185 and 186 entries. The
last carried to the first part, and the last two carried to the second, are that same owner's: (0,
0) counting (0, 439), and (0, 439) counting (0, 222): the entry of which the spent one is the head.

Names.
  spent_L_written     what the two parts spend, at the written list.
  carried_L_written   how many they carry, and the last of these.
  carried_L_bite      the entry in front of these has another owner.
  runs_L_at_laid      the law.

By what. Evaluations in Lean's kernel over the whole written list rawAheadW, behind the library's
splitOn_eq and slice_toNat?_eq (Johnson/Unfolds/), as in TiesAtLaidL.lean in this folder. Of the
authors of the honest side of the linear claim's shared rounds (K14):
bookWhole_returns_written_ahead (AtFullSide/K14/BookWholeWritten.lean); bookWhole_same_at_laid
(Johnson/Desc/ProofFile/Honest/K14/BookWholeAtHead.lean). The texts of spentE and carryE
(Johnson/Desc/ProofFile/Honest/Law/Rule/Cell.lean).

Limits.
- The full size alone. TiesAtLaid.lean's other limits stand: the library's written sendings; the
  merges that the maker reads off the first chain; two of rawAheadW's ten pieces are their makers'
  terms; the side library. That a filling's book is the maker's at these letters is a premise (hB).
- Of the other 184 carried entries nothing is said but their number and, of one, that its owner is
  another.
- One limit is raised at three theorems (spent_L_written, carried_L_written, carried_L_bite):
  maxRecDepth to 1000000.
- What it costs: on our machine Lake's whole call for this file alone took 1112 s. Its room was not
  measured; the three like lines of TiesAtLaidL.lean took 26.5 GiB resident: whoever builds this
  file should have that room.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (ProverCoinCounts bookWhole mergesByName spentE carryE)
open AtFullSide.K14 (rawAheadW rawSegW)
open Johnson.G (proofSendsFull)
open P5J (TS)

set_option maxRecDepth 1000000 in
/-- **At the written list of the book's entries the first part of the first chain's proximity test
spends one entry**: its owner is the part at the code switch's finish; it starts at (0, 439) and
counts (0, 3). The second part spends none. Evaluations in Lean's kernel over the whole written
list. -/
theorem spent_L_written :
    ((rawAheadW.filter fun e => e.spender == ⟨⟨1, none, 2, .K12⟩, 0⟩).filter (·.once)).map (fun e =>
        (e.owner, e.start, e.count)) =
        [(⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 439⟩, ⟨0, 3⟩)] ∧
      (rawAheadW.filter fun e => e.spender == ⟨⟨1, none, 2, .K12⟩, 1⟩).filter (·.once) = [] := by
  unfold rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **How many entries the two parts carry, and the last of them**: 185 and 186; the last carried to
the first part, and the last two carried to the second, are the same owner's: its run in front of
the spent one, and the run of which the spent entry is the head. Evaluations in Lean's kernel over
the whole written list. -/
theorem carried_L_written :
    ((rawAheadW.filter fun e => e.spender == ⟨⟨1, none, 2, .K12⟩, 0⟩).filter (!·.once)).length = 185
        ∧
      ((rawAheadW.filter fun e => e.spender == ⟨⟨1, none, 2, .K12⟩, 1⟩).filter (!·.once)).length =
          186 ∧
      (((rawAheadW.filter fun e => e.spender == ⟨⟨1, none, 2, .K12⟩, 0⟩).filter (!·.once)).drop
          184).map (fun e => (e.owner, e.start, e.count)) =
        [(⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 0⟩, ⟨0, 439⟩)] ∧
      (((rawAheadW.filter fun e => e.spender == ⟨⟨1, none, 2, .K12⟩, 1⟩).filter (!·.once)).drop
          184).map (fun e => (e.owner, e.start, e.count)) =
        [(⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 0⟩, ⟨0, 439⟩), (⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 439⟩, ⟨0, 222⟩)]
            := by
  unfold rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluations can fail: the same owner's entries are not all that is carried: the entry number
183 (from 0) carried to the first part has another owner. -/
theorem carried_L_bite :
    ((((rawAheadW.filter fun e => e.spender == ⟨⟨1, none, 2, .K12⟩, 0⟩).filter (!·.once))[183]?).map
        (·.owner) ==
      some ⟨⟨1, none, 1, .K2⟩, 0⟩) = false := by
  unfold rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **The same at whatever book the maker returns, in the goals' scope.** spentE and carryE: the
frame's readers of a book's entries at an address. -/
theorem runs_L_at_laid {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk) :
    (spentE Bk ⟨⟨1, none, 2, .K12⟩, 0⟩).map (fun e => (e.owner, e.start, e.count)) = [(⟨⟨1, none, 1,
        .K2⟩, 0⟩, ⟨0, 439⟩, ⟨0, 3⟩)] ∧
      spentE Bk ⟨⟨1, none, 2, .K12⟩, 1⟩ = [] ∧ (carryE Bk ⟨⟨1, none, 2, .K12⟩, 0⟩).length = 185 ∧
      (carryE Bk ⟨⟨1, none, 2, .K12⟩, 1⟩).length = 186 ∧
      ((carryE Bk ⟨⟨1, none, 2, .K12⟩, 0⟩).drop 184).map (fun e => (e.owner, e.start, e.count)) =
          [(⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 0⟩, ⟨0, 439⟩)] ∧
      ((carryE Bk ⟨⟨1, none, 2, .K12⟩, 1⟩).drop 184).map (fun e => (e.owner, e.start, e.count)) =
        [(⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 0⟩, ⟨0, 439⟩), (⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 439⟩, ⟨0, 222⟩)]
            := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  unfold spentE carryE
  rw [hA]
  exact ⟨spent_L_written.1, spent_L_written.2, carried_L_written.1, carried_L_written.2.1,
    carried_L_written.2.2.1, carried_L_written.2.2.2⟩

end AtFullSide.K12

#print axioms AtFullSide.K12.spent_L_written
#print axioms AtFullSide.K12.carried_L_written
#print axioms AtFullSide.K12.carried_L_bite
#print axioms AtFullSide.K12.runs_L_at_laid
