-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawClausesWritten.lean: AT WHATEVER BOOK bookRaw RETURNS AT THE LIBRARY's WRITTEN
DESCRIPTION WP: THE VERDICT OF THE FIRST, THE THIRD, THE FOURTH, THE SIXTH AND THE NINTH MEMBER OF
THE FRAME's OWN LIST ProverCoinCounts.clauses (Johnson/Desc/ProofFile/Honest/Frame.lean) IS true. Statements
with their proofs; each a rewriting by clauses_verdicts (Honest/BookWordOf.lean) and a call of
clause1_written, clause3_written (AtFullSide/K14/RawBookRowsWritten.lean), clause4_written,
clause6_written or clause9_written (AtFullSide/K14/RawTest4Written.lean and its two sisters): so the
Bools that these show to be true are the list's own members', by Lean; no evaluation.

  clause1_in_clauses, clause3_in_clauses   at any merges
  clause4_in_clauses, clause6_in_clauses, clause9_in_clauses   at mergesByName's

The form is that of clause2_written and clause10_written (AtFullSide/K14/RawRowsWritten.lean).

Limits. IMPLICATIONS FROM "bookRaw RETURNS W". A fact on written values: WP's own limit and the
written sendings' stand. THE MERGES OF THE LAST THREE ARE mergesByName's, WHICH THE FRAME's OWN TEXT
CALLS A GUESS. FIVE OF ELEVEN MEMBERS. A member's name is not read. No option is raised; the file
lies in the side library because it imports files of it. Nothing on soundness, on completeness or on
what is hidden; no property.
-/
import AtFullSide.K14.RawTest4Written
import AtFullSide.K14.RawTest6Written
import AtFullSide.K14.RawTest9Written
import Johnson.Desc.ProofFile.Honest.BookWordOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- **THE FIRST MEMBER OF ProverCoinCounts.clauses SAYS true AT THE RAW BOOK.** CONDITIONAL: that bookRaw
returns W. -/
theorem clause1_in_clauses (M : Merges) (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      M = .ok W) :
    ((W.clauses WP)[0]?).map (·.2) = some true := by
  rw [← List.getElem?_map, clauses_verdicts]
  exact congrArg some (clause1_written M W h)

/-- **THE THIRD MEMBER OF ProverCoinCounts.clauses SAYS true AT THE RAW BOOK.** CONDITIONAL: that bookRaw
returns W. -/
theorem clause3_in_clauses (M : Merges) (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      M = .ok W) :
    ((W.clauses WP)[2]?).map (·.2) = some true := by
  rw [← List.getElem?_map, clauses_verdicts]
  exact congrArg some (clause3_written M W h)

/-- **THE FOURTH MEMBER OF ProverCoinCounts.clauses SAYS true AT THE RAW BOOK.** CONDITIONAL: that bookRaw
returns W. -/
theorem clause4_in_clauses (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    ((W.clauses WP)[3]?).map (·.2) = some true := by
  rw [← List.getElem?_map, clauses_verdicts]
  exact congrArg some (clause4_written W h)

/-- **THE SIXTH MEMBER OF ProverCoinCounts.clauses SAYS true AT THE RAW BOOK.** CONDITIONAL: that bookRaw
returns W. -/
theorem clause6_in_clauses (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    ((W.clauses WP)[5]?).map (·.2) = some true := by
  rw [← List.getElem?_map, clauses_verdicts]
  exact congrArg some (clause6_written W h)

/-- **THE NINTH MEMBER OF ProverCoinCounts.clauses SAYS true AT THE RAW BOOK.** CONDITIONAL: that bookRaw
returns W. -/
theorem clause9_in_clauses (W : ProverCoinCounts)
    (h : bookRaw WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok W) :
    ((W.clauses WP)[8]?).map (·.2) = some true := by
  rw [← List.getElem?_map, clauses_verdicts]
  exact congrArg some (clause9_written W h)

end AtFullSide.K14

#print axioms AtFullSide.K14.clause1_in_clauses
#print axioms AtFullSide.K14.clause3_in_clauses
#print axioms AtFullSide.K14.clause4_in_clauses
#print axioms AtFullSide.K14.clause6_in_clauses
#print axioms AtFullSide.K14.clause9_in_clauses
