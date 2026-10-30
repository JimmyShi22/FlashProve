-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawSmallWritten.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean): THE SMALL
STEPS OF THE FRAME's MAKER OF THE RAW BOOK (bookRaw, Johnson/Desc/ProofFile/Honest/BookWhole.lean;
spendingBook, Honest/BookAll.lean) ARE WRITTEN VALUES: TWELVE EQUATIONS: THREE NUMBERS, ONE PAIR,
ONE RECORD, ONE ROW, ONE ENTRY AND FIVE SHORT LISTS OF ENTRIES. No premise. Seven left sides are, to
the letter, the left side of a conjunct of the frame's bookRaw_ahead or spendingBook_ahead
(Honest/BookSharedLaw.lean) at WP, at the written messages sentFirstW
(Honest/BookWritten/SentFirst.lean) and sentSharedW (Honest/BookWritten/Small.lean);
rawCarriesW_written, rawOwnCarry_written and rawSplit_written are a piece inside these laws' closing
equations; rawOwnFresh_written a piece of such a piece; rawOwnRow_written a piece of bookRaw_rows'
(Honest/BookRawRows.lean).

  rawFoldedAt_written   the round of the sending "the folded row": 1
  rawCarriesFoldedW, rawCarriesFolded_written   **the five entries that carry to the fold behind
                  it (two) and to the part behind that fold (three)**
  rawLastSwitch_written   the round of the last switch of the folded row's test: 39
  rawCarriesOmegaW, rawCarriesOmega_written   **the four entries that carry to the fold behind
                  that (two) and to the part behind it (two)**
  rawSecondFold_written   the second chain's first fold, and the part with a sending behind it
  rawTail_written   **the shared chain's mask code's tail: 152**
  rawOwnFresh_written   **the one fold of the shared chain that sends a fresh table of its own**:
                  its part, the part behind it, four rounds "FOLD round", one row. A weaker kin:
                  rawOwnFolds_written (AtFullSide/K14/RawRowsWritten.lean): that fold's part alone
  rawOwnRow_written   so its row in the book, with its count: 161
  foldsSharedW, foldEntries_shared_written   **the one entry by which a fold spends the shared
                  chain's fresh table that is sent ahead**
  rawSplit_written   the shared split's coin is splitEntryWritten
                  (Johnson/Desc/ProofFile/Honest/K14/SplitEntryWritten.lean)
  rawCarriesWW, rawCarriesW_written   **the seven entries that carry to the second chain's first
                  fold (three) and to the part behind it (four)**: at written messages alone
  rawOwnCarryW, rawOwnCarry_written   the one entry that carries the own fresh table
  rawSmall_short  the five lists that lie at the shared chain, in the order of the frame's
                  sharedAhead, with the two of rawCarriesWW that carry Omega's message, ARE the
                  written short list (writtenShort, Honest/K14/SharedAheadWritten.lean)
  rawSmall_bite   foldsAre (AtFullSide/K14/FoldsWritten.lean) rejects each of the three made lists
                  with its last entry dropped: BEHIND THE EQUATIONS: it shows that the test can
                  reject by length; no field is bent here

How the labels are read. testOf stands in the filter of rawLastSwitch_written: it is rewritten by
testOf_isK (AtFullSide/K14/SwitchesWritten.lean). isSwitch stands inside foldEntries: unfolded by
name and rewritten by the library's splitOn_eq (Johnson/Unfolds/SplitOn.lean). Then Lean's kernel
evaluates.

HOW THE WRITTEN VALUES CAME: they were printed by Lean's evaluator and laid into this file by a
program; THE EVALUATOR IS TRUSTED FOR NOTHING: each is held against its maker by Lean's kernel.

No option is raised. The file lies in the side library because it imports two files of it.

Limits. A fact on written values: WP's own limit stands (its values were printed off the goals'
stored full-size public files); so does the written sendings' (the labels and the two entries of
each sending rest on one print and on a test by Lean's evaluator; no theorem). NOTHING AT ANY OTHER
DESCRIPTION. THAT bookRaw OR bookWhole RETURNS IS NOT SAID; nothing on any test of the book's own.
WITHOUT A NEGATIVE LINE: the three numbers, the pair, the record, rawSplit_written,
rawOwnRow_written, rawCarriesW_written, rawOwnCarry_written and rawSmall_short. WHICH FOLD IS
"BEHIND" A SENDING IS THE MAKERS' OWN TAKING. Nothing on soundness, on completeness or on what is
hidden; no property.
-/
import AtFullSide.K14.FoldsWritten
import AtFullSide.K14.SwitchesWritten
import Johnson.Desc.ProofFile.Honest.BookWritten.SentFirst
import Johnson.Desc.ProofFile.Honest.BookSharedLaw
import Johnson.Desc.ProofFile.Honest.K14.SplitEntryWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The round of the sending "the folded row". -/
theorem rawFoldedAt_written :
    due? "the folded row's sending"
      ((BookShared.under sentSharedW "the folded row").head?.map (·.round)) = .ok 1 := by
  decide +kernel

/-- **The five entries that carry to the fold behind "the folded row", written.** -/
def rawCarriesFoldedW : List Ahead :=
  [⟨"message 0 of 2.-.2.0 to 2.-.9.0: carried", ⟨⟨2, none, 2, .K1⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 10808⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, false⟩,
   ⟨"message 1 of 2.-.5.0 to 2.-.9.0: carried", ⟨⟨2, none, 5, .K1⟩, 0⟩,
     ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, false⟩,
   ⟨"message 0 of 2.-.2.0 to 2.-.9.1: carried", ⟨⟨2, none, 2, .K1⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 10808⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false⟩,
   ⟨"message 1 of 2.-.5.0 to 2.-.9.1: carried", ⟨⟨2, none, 5, .K1⟩, 0⟩,
     ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false⟩,
   ⟨"message 1 of 2.-.2.0 to 2.-.9.1: carried", ⟨⟨2, none, 2, .K1⟩, 0⟩,
     ⟨0, 10808⟩, ⟨0, 167⟩, ⟨⟨2, none, 9, .K12⟩, 1⟩, false⟩]

/-- **THE EQUATION: THE ENTRIES THAT CARRY TO THE FOLD BEHIND "the folded row".** -/
theorem rawCarriesFolded_written :
    groupCarries (planOf WP.shared.blocksInOrder) 1
      ((BookShared.under sentSharedW "the folded row").filter (!·.fresh) ++
        (BookShared.under sentSharedW "Omega").filter (·.masks))
      ((BookShared.under sentSharedW "the folded row").find? (·.fresh)) = .ok rawCarriesFoldedW :=
  foldsAre_eq (by decide +kernel)

/-- The round of the last switch of the folded row's test. -/
theorem rawLastSwitch_written :
    due? "the folded row's test's last switch"
      ((((seedRounds WP.shared.blocksInOrder).zip proofSendsFull.2.1.sends).filter fun x =>
        testOf x.2.label == "the folded row's test").getLast?.map (·.1)) = .ok 39 := by
  rw [testOf_isK]
  decide +kernel

/-- **The four entries that carry to the fold behind that switch, written.** -/
def rawCarriesOmegaW : List Ahead :=
  [⟨"message 0 of 2.-.5.0 to 2.-.10.0: carried", ⟨⟨2, none, 5, .K1⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨2, none, 10, .K12⟩, 0⟩, false⟩,
   ⟨"message 1 of 2.-.5.0 to 2.-.10.0: carried", ⟨⟨2, none, 5, .K1⟩, 0⟩,
     ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 10, .K12⟩, 0⟩, false⟩,
   ⟨"message 0 of 2.-.5.0 to 2.-.10.1: carried", ⟨⟨2, none, 5, .K1⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false⟩,
   ⟨"message 1 of 2.-.5.0 to 2.-.10.1: carried", ⟨⟨2, none, 5, .K1⟩, 0⟩,
     ⟨0, 42853⟩, ⟨0, 216⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false⟩]

/-- **THE EQUATION: THE ENTRIES THAT CARRY TO THE FOLD BEHIND THE FOLDED ROW's TEST.** -/
theorem rawCarriesOmega_written :
    groupCarries (planOf WP.shared.blocksInOrder) 39 (BookShared.under sentSharedW "Omega") none =
      .ok rawCarriesOmegaW :=
  foldsAre_eq (by decide +kernel)

/-- The second chain's first fold, and the part that holds the first sending behind it. -/
theorem rawSecondFold_written :
    due? "the second chain's first fold, with a sending behind it"
      (behindFold (planOf WP.second.blocksInOrder) 0) =
        .ok (⟨⟨3, none, 2, .K12⟩, 0⟩, ⟨⟨3, none, 2, .K12⟩, 1⟩) := by
  decide +kernel

/-- **The shared chain's mask code's tail.** -/
theorem rawTail_written :
    due? "the shared chain's mask code" ((codesUnder proofSendsFull.2.1 "Omega").map (·.2.r)) =
      .ok 152 := by
  decide +kernel

/-- **The one fold of the shared chain that sends a fresh table of its own**: its part; the part
that holds the first sending behind it; its rounds "FOLD round"; the table's rows. -/
theorem rawOwnFresh_written :
    ownFreshIn WP.shared.blocksInOrder =
      [⟨⟨⟨2, none, 10, .K12⟩, 0⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, 4, 1⟩] := by
  decide +kernel

/-- Its row in the book, with its count. -/
theorem rawOwnRow_written :
    (ownFreshIn WP.shared.blocksInOrder).map (·.row 152) = [(⟨⟨2, none, 10, .K12⟩, 0⟩, ⟨0, 161⟩)] := by
  rw [rawOwnFresh_written]
  decide +kernel

/-- **The one entry by which a fold spends the shared chain's fresh table, written.** -/
def foldsSharedW : List Ahead :=
  [⟨"the fold's fresh mask to 2.-.9.0: fold", ⟨⟨2, none, 2, .K1⟩, 0⟩,
     ⟨0, 10808⟩, ⟨0, 15⟩, ⟨⟨2, none, 9, .K12⟩, 0⟩, true⟩]

/-- **THE EQUATION: foldEntries AT THE SHARED CHAIN.** -/
theorem foldEntries_shared_written :
    foldEntries (planOf WP.shared.blocksInOrder) [] proofSendsFull.2.1 = .ok foldsSharedW := by
  refine foldsAre_eq ?_
  unfold foldEntries isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- The shared split's coin. -/
theorem rawSplit_written :
    splitEntry WP.shared.blocksInOrder proofSendsFull.2.1 = some splitEntryWritten := by
  have h : (splitEntry WP.shared.blocksInOrder proofSendsFull.2.1).map aheadView =
      some (aheadView splitEntryWritten) := by decide +kernel
  cases hs : splitEntry WP.shared.blocksInOrder proofSendsFull.2.1 with
  | none =>
    rw [hs] at h
    cases h
  | some e =>
    rw [hs] at h
    exact congrArg some (aheadView_inj (Option.some.inj h))

/-- **The seven entries that carry to the second chain's first fold, written.** -/
def rawCarriesWW : List Ahead :=
  [⟨"message 4 of 1.0.1.0 to 3.-.2.0: carried", ⟨⟨1, some 0, 1, .K1⟩, 0⟩,
     ⟨25848, 8647⟩, ⟨0, 311⟩, ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
   ⟨"message 0 of 1.-.4.0 to 3.-.2.0: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 3882⟩, ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
   ⟨"message 0 of 2.-.5.0 to 3.-.2.0: carried", ⟨⟨2, none, 5, .K1⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨3, none, 2, .K12⟩, 0⟩, false⟩,
   ⟨"message 4 of 1.0.1.0 to 3.-.2.1: carried", ⟨⟨1, some 0, 1, .K1⟩, 0⟩,
     ⟨25848, 8647⟩, ⟨0, 311⟩, ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
   ⟨"message 0 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 3882⟩, ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
   ⟨"message 0 of 2.-.5.0 to 3.-.2.1: carried", ⟨⟨2, none, 5, .K1⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 42853⟩, ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩,
   ⟨"message 1 of 1.-.4.0 to 3.-.2.1: carried", ⟨⟨1, none, 4, .K1⟩, 0⟩,
     ⟨0, 3882⟩, ⟨0, 121⟩, ⟨⟨3, none, 2, .K12⟩, 1⟩, false⟩]

/-- **THE EQUATION: THE ENTRIES THAT CARRY TO THE SECOND CHAIN's FIRST FOLD**: at written
messages. -/
theorem rawCarriesW_written :
    carryPair ⟨⟨3, none, 2, .K12⟩, 0⟩ ⟨⟨3, none, 2, .K12⟩, 1⟩
      (sentFirstW.filter (·.masks) ++ (BookShared.under sentFirstW "W").filter (!·.fresh) ++
        (BookShared.under sentSharedW "Omega").filter (!·.masks))
      ((BookShared.under sentFirstW "W").find? (·.fresh)) = rawCarriesWW :=
  Except.ok.inj (foldsAre_eq (x := .ok _) (by decide +kernel))

/-- The one entry that carries the shared chain's own fresh table, written. -/
def rawOwnCarryW : List Ahead :=
  [⟨"message 0 of 2.-.10.0 to 2.-.10.1: carried", ⟨⟨2, none, 10, .K12⟩, 0⟩,
     ⟨0, 0⟩, ⟨0, 161⟩, ⟨⟨2, none, 10, .K12⟩, 1⟩, false⟩]

/-- The equation. -/
theorem rawOwnCarry_written : (ownFreshIn WP.shared.blocksInOrder).map (·.carry 152) = rawOwnCarryW := by
  rw [rawOwnFresh_written]
  exact Except.ok.inj (foldsAre_eq (x := .ok _) (by decide +kernel))

/-- **The pieces at the shared chain, in sharedAhead's order, are the written short list.** -/
theorem rawSmall_short :
    (foldsSharedW ++ [splitEntryWritten] ++ rawCarriesFoldedW ++ rawCarriesOmegaW ++
      (rawCarriesWW.filter fun e => e.owner == ⟨⟨2, none, 5, .K1⟩, 0⟩) ++
        rawOwnCarryW).map aheadView = writtenShort.map aheadView := by
  decide +kernel

/-- The test rejects each of the three made lists with its last entry dropped: behind the
equations. -/
theorem rawSmall_bite :
    foldsAre (groupCarries (planOf WP.shared.blocksInOrder) 1
        ((BookShared.under sentSharedW "the folded row").filter (!·.fresh) ++
          (BookShared.under sentSharedW "Omega").filter (·.masks))
        ((BookShared.under sentSharedW "the folded row").find? (·.fresh)))
        (rawCarriesFoldedW.map aheadView).dropLast = false ∧
      foldsAre (groupCarries (planOf WP.shared.blocksInOrder) 39 (BookShared.under sentSharedW "Omega") none)
        (rawCarriesOmegaW.map aheadView).dropLast = false ∧
      foldsAre (foldEntries (planOf WP.shared.blocksInOrder) [] proofSendsFull.2.1)
        (foldsSharedW.map aheadView).dropLast = false := by
  rw [rawCarriesFolded_written, rawCarriesOmega_written, foldEntries_shared_written]
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.rawFoldedAt_written
#print axioms AtFullSide.K14.rawCarriesFolded_written
#print axioms AtFullSide.K14.rawLastSwitch_written
#print axioms AtFullSide.K14.rawCarriesOmega_written
#print axioms AtFullSide.K14.rawSecondFold_written
#print axioms AtFullSide.K14.rawTail_written
#print axioms AtFullSide.K14.rawOwnFresh_written
#print axioms AtFullSide.K14.rawOwnRow_written
#print axioms AtFullSide.K14.foldEntries_shared_written
#print axioms AtFullSide.K14.rawSplit_written
#print axioms AtFullSide.K14.rawCarriesW_written
#print axioms AtFullSide.K14.rawOwnCarry_written
#print axioms AtFullSide.K14.rawSmall_short
#print axioms AtFullSide.K14.rawSmall_bite
