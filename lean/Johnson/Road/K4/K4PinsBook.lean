-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsBook.lean: WHAT K4's TESTS READ OF THE TABLE's NUMBERS, AT THE WRITTEN VALUES.
The composed meaning's closed numbers `P5J.At.N Z cF` (Johnson/P5J/LettersAt.lean) are made of the
plan's seats and of WHAT THE FIRST CHAIN's SUB-PROTOCOLS TELL (`Numbers.withTold`,
Johnson/Desc/First/BookNumbers.lean): the index masks' message's number and the counts of trees and
of oracle messages in front of a place hang on the chain cF, of which `WrittenAt Z`
(Johnson/Road/K4/K4PlanTied.lean) says nothing. Where the cut of cF into sub-protocols is the
written one, they are closed terms. One definition, one Lean structure, five theorems: two by
Lean's kernel, three without an evaluation.

  `nW`: the numbers at the written values: the core off the written seats (`P5T.N0Full`), filled
    off the written cut's tellings (`toldCut`, Johnson/Desc/First/CutWritten.lean) at the table's
    own list of places.
  `told_written`: where `cutOf cF.blocksInOrder = cutFirstFull`, what cF's sub-protocols tell is `toldCut`
    (`told_at_written`, called).
  `N_written`: there, under `WrittenAt Z`, `P5J.At.N Z cF` is the written core with its rows laid,
    filled off `toldCut`.
  `BookAt N`: five fields of N are `nW`'s: sent, index, indexNo, msgsAt, treesAt.
  **`book_of_cut`**: `WrittenAt Z` and the written cut give `BookAt (P5J.At.N Z cF)`.
  `book_numbers`: BY THE KERNEL: the index masks' message sits at (1, 0) and bears the number 4; in
    front of K4's sub-protocol of group g, and behind it, 15 g + 5 oracle messages are told; behind
    it 6 g + 2 trees.
  `book_numbers_no`: A NEGATIVE TEST: with the first telling sub-protocol mute the number is not 4.

KIN: `P5T.NFull` (Johnson/P5T/FenceFull.lean) is `N0Full.withTold placesCut
toldCut`; `placesCut_is` makes the two lists of places one. That file wants some 11 GB to compile:
it is not imported here.

Limits. K04_law IS NOT PROVED BY THIS. `WrittenAt Z` AND THE WRITTEN CUT ARE PREMISES. Both are
conditions on the three public files alone: nothing that a prover sends is read. The written cut is
what the tenth row of the verifier's entry tests compares (`cutRow`,
Johnson/Desc/Ok/PlanWritten/CutTest.lean; `LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean: fourteen
rows in this tree); an earlier list of eight rows did not ask it. The written lists rest on prints
of Lean's evaluator (their files' heads). The full size alone.
-/
import Johnson.Road.K4.K4PlanTied
import Johnson.Desc.First.CutWritten
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.Desc.First (Numbers flatPlacesOf toldCut told_at_written possAt)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.PlanWritten (cutFirstFull)

/-- The table's numbers at the written values. -/
def nW : Numbers := P5T.N0Full.withTold (flatPlacesOf linksFull true) toldCut

variable {Z : ProofFile.Pub} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- Where the cut is the written one, what the chain's sub-protocols tell is the written list. -/
theorem told_written (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    P5J.At.told cF = toldCut := by
  rw [P5J.At.told_is]
  exact (told_at_written hc).2

/-- **There, under `WrittenAt Z`, the closed numbers are the written core with its rows laid, filled
off the written tellings.** -/
theorem N_written (W : WrittenAt Z)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    P5J.At.N Z cF =
      (P5T.N0Full.withRows (P5J.At.shape Z) (possAt cF.blocksInOrder P5J.At.links.length)
        P5J.At.links.length).withTold (flatPlacesOf linksFull true) toldCut := by
  unfold P5J.At.N
  rw [told_written hc, show P5T.numbersOf (P5J.At.pseats Z) = P5T.N0Full from numbersAt_written W]
  rfl

/-- **Five fields of N are the written numbers'.** -/
structure BookAt (N : Numbers) : Prop where
  sent : N.sent = nW.sent
  index : N.index = nW.index
  indexNo : N.indexNo = nW.indexNo
  msgsAt : N.msgsAt = nW.msgsAt
  treesAt : N.treesAt = nW.treesAt

/-- **The written values and the written cut give them.** -/
theorem book_of_cut (W : WrittenAt Z)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    BookAt (P5J.At.N Z cF) := by
  rw [N_written W hc]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 1000000 in
/-- By the kernel: the numbers that K4's tests read. -/
theorem book_numbers :
    (nW.index, nW.indexNo, (List.range 12).map fun g =>
      (nW.msgsAt (flatPlacesOf linksFull true)[28 * g + 4]?,
        nW.msgsAt (flatPlacesOf linksFull true)[28 * g + 4 + 1]?,
        nW.treesAt (flatPlacesOf linksFull true)[28 * g + 4 + 1]?)) =
      ((1, 0), 4, (List.range 12).map fun g => (15 * g + 5, 15 * g + 5, 6 * g + 2)) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with the first telling sub-protocol mute the number is another. -/
theorem book_numbers_no :
    (P5T.N0Full.withTold (flatPlacesOf linksFull true) (toldCut.set 2 [])).indexNo ≠ 4 := by
  decide +kernel

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.told_written
#print axioms OnBytes.Road.K4.N_written
#print axioms OnBytes.Road.K4.book_of_cut
#print axioms OnBytes.Road.K4.book_numbers
#print axioms OnBytes.Road.K4.book_numbers_no
