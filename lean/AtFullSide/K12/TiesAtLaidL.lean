-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/TiesAtLaidL.lean

What it proves. "One owner and one start" in the goals' scope, at the full size, at the first
chain's proximity test: whatever book of random values the maker returns (bookWhole) at the proof
file's own description, the library's written sendings and the merges that it reads off the first
chain: the test tiesB (Johnson/Desc/ProofFile/Honest/K12/AgreeBook.lean) says yes at that test's
place, at 185 members. No premise on a label, none on the lending. At any earlier hash.

Names.
  ties_written_L   the test says yes at the written list of entries.
  ties_bite_L      at 184 and at 186 members it says no.
  ties_at_laid_L   the law.

By what. Evaluations in Lean's kernel over the whole written list rawAheadW, behind the library's
splitOn_eq and slice_toNat?_eq (Johnson/Unfolds/), as in AtFullSide/K14/RawLengthsWritten.lean: the
place lies in the first chain, so ahead_at (TiesAtLaid.lean in this folder) does not serve.
tiesB_of_ahead (TiesAtLaid.lean). Of the authors of the honest side of the linear claim's shared
rounds (K14): bookWhole_returns_written_ahead (AtFullSide/K14/BookWholeWritten.lean);
bookWhole_same_at_laid (Johnson/Desc/ProofFile/Honest/K14/BookWholeAtHead.lean).

Limits.
- The full size alone. At another plan nothing here says that the maker lays the fresh table last
  among what the second part carries: "In the chain of segments the entries of q are in the order of
  sending, the fold's fresh table in its place: where it was sent, before its link's later sendings"
  (the head of Johnson/Desc/ProofFile/Honest/BookCarry.lean).
- The number of members, 185, is written. That a job at this place has so many is a caller's step,
  not made here.
- TiesAtLaid.lean's other limits stand: the library's written sendings; the merges that the maker
  reads off the first chain; two of rawAheadW's ten pieces are their makers' terms; the side
  library.
- tiesB compares, at the fresh table, the owner and the start's second number alone. The counts are
  not compared: by an evaluation outside this file the spent entry's is (0, 3), the carried one's
  (0, 222).
- One limit is raised at two theorems (ties_written_L, ties_bite_L): maxRecDepth to 1000000.
- What it costs: on our machine the file took 734 s to build, at 27,754,012 kB (26.5 GiB) resident:
  whoever builds this file must have that room.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain Place)
open ProofFile.Honest (ProverCoinCounts bookWhole mergesByName spentE carryE)
open ProofFile.Honest.K12 (tiesB)
open AtFullSide.K14 (rawAheadW rawSegW)
open Johnson.G (proofSendsFull)
open P5J (TS)

set_option maxRecDepth 1000000 in
/-- **At the written list of the book's entries the test on the book's entries says yes at the first
chain's proximity test's place, at 185 members.** An evaluation in Lean's kernel, behind the
library's equations for String.splitOn and toNat?. -/
theorem ties_written_L :
    tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
      ⟨1, none, 2, .K12⟩ 185 = true := by
  unfold tiesB spentE carryE
  dsimp only
  unfold rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluation can fail: at one member fewer and at one more it says no. -/
theorem ties_bite_L :
    tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨1, none, 2, .K12⟩ 184 = false ∧
      tiesB { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] }
        ⟨1, none, 2, .K12⟩ 186 = false := by
  unfold tiesB spentE carryE
  dsimp only
  unfold rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **"One owner and one start" in the goals' scope at the first chain's proximity test**: whatever
book the maker returns at the proof file's own description, the library's written sendings and the
merges that it reads off the first chain: tiesB says yes there at 185 members. At any earlier hash.
-/
theorem ties_at_laid_L {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {B : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok B) :
    tiesB B ⟨1, none, 2, .K12⟩ 185 = true := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = B :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  exact (tiesB_of_ahead B₀
    { first := [], shared := [], second := [], ahead := rawAheadW, cuts := [] } hA _ _).trans
    ties_written_L

end AtFullSide.K12

#print axioms AtFullSide.K12.ties_written_L
#print axioms AtFullSide.K12.ties_bite_L
#print axioms AtFullSide.K12.ties_at_laid_L
