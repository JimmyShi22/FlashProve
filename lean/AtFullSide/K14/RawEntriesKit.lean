-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawEntriesKit.lean: THE FOURTH, THE SIXTH AND THE NINTH OF THE BOOK's OWN ELEVEN
TESTS (ProverCoinCounts.clauses, Johnson/Desc/ProofFile/Honest/Frame.lean), EACH AS A TEST ON A LIST OF ENTRIES
AT THE LIBRARY's WRITTEN DESCRIPTION WP AND THE RAW BOOK's WRITTEN ROWS; EACH ACCEPTS THE EIGHT
WRITTEN PIECES OF rawAheadW (AtFullSide/K14/RawAheadWritten.lean); EACH ACCEPTS rawAheadW IF IT
ACCEPTS THE TWO MAKERS' TERMS. Four definitions; statements with their proofs.

  rawTest4, rawTest6, rawTest9   the three tests' texts, the list of entries an argument
  rawShortW       rawAheadW's eight written pieces in a row
  rawTest_short   all three accept these: an evaluation by Lean's kernel
  rawAll_whole    **the cut**: a test of the form "all" accepts rawAheadW if it accepts the two
                  makers' terms and the written pieces: by List.all_append
  rawTest4_whole, rawTest6_whole, rawTest9_whole   a test that accepts the stretches' entries and
                  rawSegW accepts rawAheadW: by rawAll_whole and rawTest_short
  rawTest_bite    THE THREE TESTS CAN FAIL: the first written fold's entry with a count of 100,017;
                  an entry with an owner in the first chain and a spender in the shared chain; the
                  split's coin with a spender outside the shared chain

No option is raised. The file lies in the side library because it imports files of it.

Limits. THAT A TEST ACCEPTS THE TWO MAKERS' TERMS IS NOT SHOWN HERE:
AtFullSide/K14/RawTest4Written.lean, RawTest6Written.lean and RawTest9Written.lean show it. A fact
on written values: WP's own limit and the written sendings' stand. The three bends are of one entry
each, and coarse: they show that a test can reject, not where it begins to. Nothing on the other
tests. Nothing on soundness, on completeness or on what is hidden; no property.
-/
import AtFullSide.K14.RawAheadWritten
import AtFullSide.K14.RawBookRowsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)

/-- The fourth test, "an entry's run is not within its owner's count", at the written rows. -/
def rawTest4 (l : List Ahead) : Bool :=
  l.all fun a =>
    decide (a.start.f + a.count.f ≤
      (dueAt (rawRowsFirstW ++ rawRowsSharedW ++ rawRowsSecondW) a.owner).f) &&
    decide (a.start.e + a.count.e ≤
      (dueAt (rawRowsFirstW ++ rawRowsSharedW ++ rawRowsSecondW) a.owner).e)

/-- The sixth test, "the shared chain is handed a coin of the first chain", at WP. -/
def rawTest6 (l : List Ahead) : Bool :=
  l.all fun a => !((WP.first.blocksInOrder.map (·.place)).contains a.owner.place &&
    (WP.shared.blocksInOrder.map (·.place)).contains a.spender.place)

/-- The ninth test, "a coin of the shared chain is spent outside it", at WP. -/
def rawTest9 (l : List Ahead) : Bool :=
  l.all fun a => !(a.once && (WP.shared.blocksInOrder.map (·.place)).contains a.owner.place &&
    !(WP.shared.blocksInOrder.map (·.place)).contains a.spender.place)

/-- rawAheadW's eight written pieces, in a row. -/
def rawShortW : List Ahead :=
  foldsFirstW ++ foldsSharedW ++ [] ++ [splitEntryWritten] ++ rawCarriesFoldedW ++
    rawCarriesOmegaW ++ rawCarriesWW ++ rawOwnCarryW

/-- All three accept the written pieces. -/
theorem rawTest_short :
    rawTest4 rawShortW = true ∧ rawTest6 rawShortW = true ∧ rawTest9 rawShortW = true := by
  decide +kernel

/-- A test of the form "all" accepts rawAheadW if it accepts the two makers' terms and the written
pieces. -/
theorem rawAll_whole (t : Ahead → Bool) (hw : (rawWantsW.map (·.entry)).all t = true)
    (hs : rawSegW.all t = true) (hr : rawShortW.all t = true) : rawAheadW.all t = true := by
  unfold rawShortW at hr
  unfold rawAheadW
  simp only [List.all_append, Bool.and_eq_true] at hr ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hr
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, h1⟩, h2⟩, h3⟩, h4⟩, hs⟩, h5⟩, h6⟩, h7⟩, h8⟩

/-- The fourth. CONDITIONAL: hw, hs. -/
theorem rawTest4_whole (hw : rawTest4 (rawWantsW.map (·.entry)) = true)
    (hs : rawTest4 rawSegW = true) : rawTest4 rawAheadW = true :=
  rawAll_whole _ hw hs rawTest_short.1

/-- The sixth. CONDITIONAL: hw, hs. -/
theorem rawTest6_whole (hw : rawTest6 (rawWantsW.map (·.entry)) = true)
    (hs : rawTest6 rawSegW = true) : rawTest6 rawAheadW = true :=
  rawAll_whole _ hw hs rawTest_short.2.1

/-- The ninth. CONDITIONAL: hw, hs. -/
theorem rawTest9_whole (hw : rawTest9 (rawWantsW.map (·.entry)) = true)
    (hs : rawTest9 rawSegW = true) : rawTest9 rawAheadW = true :=
  rawAll_whole _ hw hs rawTest_short.2.2

/-- **THE THREE TESTS CAN FAIL.** -/
theorem rawTest_bite :
    rawTest4 [{ foldsFirstHeadW with count := ⟨0, 100017⟩ }] = false ∧
      rawTest6 [⟨"x", ⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩,
        false⟩] = false ∧
      rawTest9 [{ splitEntryWritten with spender := ⟨⟨3, none, 2, .K12⟩, 0⟩ }] = false := by
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.rawTest_short
#print axioms AtFullSide.K14.rawAll_whole
#print axioms AtFullSide.K14.rawTest4_whole
#print axioms AtFullSide.K14.rawTest6_whole
#print axioms AtFullSide.K14.rawTest9_whole
#print axioms AtFullSide.K14.rawTest_bite
