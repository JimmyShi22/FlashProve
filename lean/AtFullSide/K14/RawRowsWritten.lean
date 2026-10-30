-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawRowsWritten.lean: AT THE WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean), THE LIBRARY's WRITTEN SENDINGS AND ANY MERGES: WHATEVER BOOK
bookRaw (Honest/BookWhole.lean) RETURNS THERE, ITS ROWS' ADDRESSES ARE 84 WRITTEN ONES, ALL
DIFFERENT: SO THE SECOND OF THE BOOK's OWN TESTS ("a part has two rows") ACCEPTS IT; AND THE TENTH
DOES. One definition (a list made of written lists); statements with their proofs. IMPLICATIONS:
that bookRaw returns there is not shown here; its return reads the merges, its rows and cuts do not.

  rawOwnFolds_written   the folds of the shared chain that send their own fresh table: one, at
                  ⟨⟨2, none, 10, K12⟩, 0⟩: an evaluation in Lean's kernel
  rawAddrsW       the 84 addresses: five maps of others' written lists and one literal, laid in a
                  row: of the first chain's 77 rows and its switches' one; of
                  the shared chain's two, its switches' two and the fold's one; of the second
                  chain's switches' one
  rawAddrs_nodup  they are all different. rawAddrs_bent: with the last one laid once more they are
                  not
  rawRows_addrs   **the addresses of W's rows are rawAddrsW**: by bookRaw_rows
                  (Honest/BookRawRows.lean) and seven equations at WP: rowsIn's three
                  (Honest/BookWritten/RowsFirst.lean, Small.lean), switchRows' three
                  (AtFullSide/K14/SwitchesWritten.lean), rawOwnFolds_written. The rows' counts are
                  not read: the fold's row's count hangs on a tail that is left open here
  clause2_written   **the second member of ProverCoinCounts.clauses at W is true**: by clause2_of_nodup
  clause10_written   **the tenth member of ProverCoinCounts.clauses at W is true**: by clause10_at_raw and the
                  library's wp_placesOk (Johnson/AtFull/ProofPlan/At/PlacesOk.lean): WP's test on
                  its places accepts

One option is raised, in front of rawOwnFolds_written: maxRecDepth to 1000000 (no lower number was
tried). The file stands in this side library because it imports AtFullSide/K14/SwitchesWritten.lean.
A word on names. In AtFullSide/K14/RawFactsWritten.lean the stem rawRows means the links' MASK ROWS
as owners (rawRowsW, rawRows_written); here, in rawRows_addrs, the raw BOOK's rows.
What is assumed. Nothing.
What is not claimed. THAT bookRaw RETURNS AT WP. The nine other tests. That the rows' counts are
right. THAT ANY DESCRIPTION BUT WP HAS THESE ROWS (WP.lean's own limit: its values were printed by
Lean's evaluator); the tenth test needs no written description: clause10_at_raw holds wherever the
test on the places accepts. THE SENDINGS' LABELS REST ON ONE PRINT (Johnson/G/SendsWritten.lean's
own limit): which sending is a switch is read off its label. Addresses: nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookRawRows
import Johnson.Desc.ProofFile.Honest.BookWritten.RowsFirst
import Johnson.AtFull.ProofPlan.At.PlacesOk
import AtFullSide.K14.SwitchesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

set_option maxRecDepth 1000000 in
/-- The folds of the shared chain that send their own fresh table: one. -/
theorem rawOwnFolds_written :
    (ownFreshIn WP.shared.blocksInOrder).map (·.fold) = [⟨⟨2, none, 10, .K12⟩, 0⟩] := by decide +kernel

/-- The 84 addresses of the raw book's rows, written. -/
def rawAddrsW : List Addr :=
  (bookRowsFirstW.map (·.1) ++ switchFirstW.map (·.1)) ++
    (rowsSharedW.map (·.1) ++ switchSharedW.map (·.1) ++ [⟨⟨2, none, 10, .K12⟩, 0⟩]) ++
    switchSecondW.map (·.1)

/-- They are 84, all different. -/
theorem rawAddrs_nodup : rawAddrsW.length = 84 ∧ rawAddrsW.Nodup := by decide

/-- With the last one laid once more they are not all different. -/
theorem rawAddrs_bent : ¬ (rawAddrsW ++ [(⟨⟨3, none, 2, .K12⟩, 1⟩ : Addr)]).Nodup := by decide

/-- **WHATEVER BOOK bookRaw RETURNS AT WP: THE ADDRESSES OF ITS ROWS.** -/
theorem rawRows_addrs (M : Merges) : ∀ W, bookRaw WP proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 M = .ok W →
    (W.first ++ W.shared ++ W.second).map (·.1) = rawAddrsW := by
  intro W hW
  obtain ⟨r0, r1, r2, s0, s1, s2, tail, h0, h1, h2, g0, g1, g2, -, e0, e1, e2, -⟩ :=
    bookRaw_rows hW
  obtain rfl : bookRowsFirstW = r0 := Except.ok.inj (rowsIn_first_written.symm.trans h0)
  obtain rfl : rowsSharedW = r1 := Except.ok.inj (rowsIn_shared_written.symm.trans h1)
  obtain rfl : [] = r2 := Except.ok.inj (rowsIn_second_written.symm.trans h2)
  obtain rfl : switchFirstW = s0 := Except.ok.inj (switchRows_first_written.symm.trans g0)
  obtain rfl : switchSharedW = s1 := Except.ok.inj (switchRows_shared_written.symm.trans g1)
  obtain rfl : switchSecondW = s2 := Except.ok.inj (switchRows_second_written.symm.trans g2)
  have ho : ((ownFreshIn WP.shared.blocksInOrder).map (·.row tail)).map (·.1) =
      [⟨⟨2, none, 10, .K12⟩, 0⟩] := by
    rw [List.map_map]
    exact rawOwnFolds_written
  rw [e0, e1, e2]
  simp only [List.map_append, ho, List.nil_append]
  rfl

/-- **THE SECOND TEST ACCEPTS WHATEVER BOOK bookRaw RETURNS AT WP.** -/
theorem clause2_written (M : Merges) : ∀ W, bookRaw WP proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 M = .ok W → ((W.clauses WP)[1]?).map (·.2) = some true := by
  intro W hW
  refine clause2_of_nodup WP ?_
  rw [rawRows_addrs M W hW]
  exact rawAddrs_nodup.2

/-- **THE TENTH TEST ACCEPTS WHATEVER BOOK bookRaw RETURNS AT WP.** -/
theorem clause10_written (M : Merges) : ∀ W, bookRaw WP proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 M = .ok W → ((W.clauses WP)[9]?).map (·.2) = some true :=
  fun _ hW => clause10_at_raw hW P2Law.ProofPlan.wp_placesOk

end AtFullSide.K14

#print axioms AtFullSide.K14.rawOwnFolds_written
#print axioms AtFullSide.K14.rawAddrs_nodup
#print axioms AtFullSide.K14.rawAddrs_bent
#print axioms AtFullSide.K14.rawRows_addrs
#print axioms AtFullSide.K14.clause2_written
#print axioms AtFullSide.K14.clause10_written
