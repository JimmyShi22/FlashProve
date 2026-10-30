-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/SwitchesWritten.lean: AT THE LIBRARY's WRITTEN DESCRIPTION WP
(Johnson/AtFull/ProofPlan/WP.lean) AND ITS WRITTEN SENDINGS (Johnson/G/SendsWritten.lean): THE ROWS
OF THE THREE CHAINS' CODE SWITCHES (the frame's switchRows,
Johnson/Desc/ProofFile/Honest/BookSwitch.lean) ARE THREE SPELLED LISTS OF ONE, TWO AND ONE; AND AT
NONE OF THE THREE CHAINS HAVE A SWITCH's MAIN ROWS PLACES LEFT FREE, OR TOO FEW PLACES (its
mainRoomFault, Honest/BookSwitchRoom.lean there, yields none). No premise.

  testOfK, testOf_isK   a reader of a test's name off a label without String.splitOn; testOf is
                  that reader
  firstStageW, firstCodes_written   the two codes of a test's first stage at the written
                  sendings: the frame's firstCodes (Honest/BookWhole.lean) with the number 25 for
                  lastLink (lastLink_written, Honest/BookWritten/Small.lean)
  switchFirstW, switchSharedW, switchSecondW   the three spelled lists: A ROW ADDS UP ALL SWITCHES
                  OF ITS PART (the frame's mergeRows): no single switch's count is stated
  switch_test     the public test rowsAre (Small.lean) accepts each
  switchRows_first_written, switchRows_shared_written, switchRows_second_written
                  **the three equations**
  roomIsNone, roomIsNone_eq   a public test: mainRoomFault's answer is "none"; what its yes says
  mainRoom_test, mainRoomFault_written   **at each of the three chains' sendings mainRoomFault
                  yields none**
  switch_bite     THE TEST CAN FAIL: it rejects each list with one count greater by one, the shared
                  chain's also with its two rows swapped and with one dropped (behind the equations)
  mainRoom_bite   mainRoomFault CAN ANSWER OTHERWISE: where the second chain's test is laid a first
                  stage whose base code has the message length 1, it names that chain's first switch

How the labels are read. The kernel does not get past String.splitOn by itself. isSwitch is unfolded
by name and rewritten by the library's splitOn_eq (Johnson/Unfolds/SplitOn.lean). testOf stands
inside two recursions, where a rewriting finds nothing: by the frame's switchesDue_by and
mainRooms_by (Honest/BookSwitchBy.lean) each recursion is its form with the reader as an argument,
and that argument is rewritten by testOf_isK. lastLink stands inside firstCodes: firstCodes_written
takes it out. Then Lean's kernel evaluates.

HOW THE SPELLED LISTS CAME: they were printed by Lean's evaluator and laid into this file by a
program; THE EVALUATOR IS TRUSTED FOR NOTHING: each list is held against its maker by Lean's kernel.

NO OPTION IS RAISED. WHY THE FILE LIES IN THE SIDE LIBRARY: as far as seen, one of its evaluations,
switch_test, wants a larger stack than the main library's files are compiled with. Compiled with
that smaller stack, this text had one error, at switch_test (Lean's message could not be
printed); the four statements that hang on it fell with it; the other six went through,
mainRoomFault_written among them. Compiled with the stack that this side library's files get
(lakefile.toml: --tstack=131072) all eleven go through. Why (a reading, not shown): the first
chain's five switches lie behind its round 48,235, and the makers take a round's number off a walk
along all rounds in front of it.

Limits. A fact on written values: WP's own limit stands (its values were printed off the goals'
stored full-size public files); so does the written sendings' (the labels and the two entries of
each sending rest on one print and on a test by Lean's evaluator; no theorem): which sending is a
switch, and of which test, is read off its label. NOTHING AT ANY OTHER DESCRIPTION. THAT bookRaw OR
bookWhole RETURNS IS NOT SAID; nothing on any test of the book's own. THE ROWS ARE THE SWITCHES'
ALONE: the other sendings' rows are rowsIn's (Small.lean, RowsFirst.lean). testOf_isK,
firstCodes_written and roomIsNone_eq have no negative line. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookWritten.Small
import Johnson.Desc.ProofFile.Honest.BookSwitchBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The test's name in a switch's label, read without String.splitOn. -/
def testOfK (label : String) : String :=
  (if (", the code switch of stage " == "") = true then [label]
    else (Johnson.Unfolds.splitF
      (Johnson.Unfolds.splitBound label ", the code switch of stage " 0 0) label
      ", the code switch of stage " 0 0 0 []).getD []).headD ""

/-- The frame's reader is that reader. -/
theorem testOf_isK : testOf = testOfK := by
  funext label
  unfold testOf testOfK
  rw [Johnson.Unfolds.splitOn_eq]

/-- The two codes of a test's first stage at the written sendings: firstCodes' text with the number
25 for lastLink. -/
def firstStageW (t : String) : Option (OnBytes.Code × OnBytes.Code) :=
  if t == "the last group's test" then
    (some 25).bind fun l => codesUnder proofSendsFull.1 s!"link {l}, moment 0"
  else if t == "the folded row's test" then codesUnder proofSendsFull.2.1 "the folded row"
  else if t == "Omega's test" then codesUnder proofSendsFull.2.1 "Omega"
  else if t == "the own test" then codesUnder proofSendsFull.1 "W"
  else none

/-- The frame's firstCodes at the written sendings is that function. -/
theorem firstCodes_written : firstCodes proofSendsFull.1 proofSendsFull.2.1 = firstStageW := by
  funext t
  unfold firstCodes firstStageW
  rw [lastLink_written]

/-- **The one row of the first chain's switches, written.** -/
def switchFirstW : List (Addr × Due) := [(⟨⟨1, none, 2, .K12⟩, 1⟩, ⟨0, 38038⟩)]

/-- **The two rows of the shared chain's switches, written.** -/
def switchSharedW : List (Addr × Due) :=
  [(⟨⟨2, none, 9, .K12⟩, 1⟩, ⟨0, 8062⟩),
   (⟨⟨2, none, 10, .K12⟩, 1⟩, ⟨0, 6817⟩)]

/-- **The one row of the second chain's switches, written.** -/
def switchSecondW : List (Addr × Due) := [(⟨⟨3, none, 2, .K12⟩, 1⟩, ⟨0, 12778⟩)]

/-- The test accepts the three written lists. -/
theorem switch_test :
    rowsAre (switchRows WP.first.blocksInOrder proofSendsFull.1
        (firstCodes proofSendsFull.1 proofSendsFull.2.1))
        switchFirstW = true ∧
      rowsAre (switchRows WP.shared.blocksInOrder proofSendsFull.2.1
        (firstCodes proofSendsFull.1 proofSendsFull.2.1)) switchSharedW = true ∧
      rowsAre (switchRows WP.second.blocksInOrder proofSendsFull.2.2
        (firstCodes proofSendsFull.1 proofSendsFull.2.1)) switchSecondW = true := by
  rw [firstCodes_written]
  unfold switchRows isSwitch
  simp only [Johnson.Unfolds.splitOn_eq, switchesDue_by]
  rw [testOf_isK]
  decide +kernel

/-- **THE EQUATION: THE ROWS OF THE FIRST CHAIN's SWITCHES.** -/
theorem switchRows_first_written :
    switchRows WP.first.blocksInOrder proofSendsFull.1 (firstCodes proofSendsFull.1 proofSendsFull.2.1) =
      .ok switchFirstW :=
  rowsAre_eq switch_test.1

/-- **THE EQUATION: THE ROWS OF THE SHARED CHAIN's SWITCHES.** -/
theorem switchRows_shared_written :
    switchRows WP.shared.blocksInOrder proofSendsFull.2.1 (firstCodes proofSendsFull.1 proofSendsFull.2.1) =
      .ok switchSharedW :=
  rowsAre_eq switch_test.2.1

/-- **THE EQUATION: THE ROWS OF THE SECOND CHAIN's SWITCHES.** -/
theorem switchRows_second_written :
    switchRows WP.second.blocksInOrder proofSendsFull.2.2 (firstCodes proofSendsFull.1 proofSendsFull.2.1) =
      .ok switchSecondW :=
  rowsAre_eq switch_test.2.2

/-- A public test: mainRoomFault's answer is "none". -/
def roomIsNone (x : Except String (Option String)) : Bool :=
  match x with
  | .ok none => true
  | _ => false

/-- What its yes says. -/
theorem roomIsNone_eq {x : Except String (Option String)} (h : roomIsNone x = true) :
    x = .ok none := by
  match x, h with
  | .ok none, _ => rfl

/-- The test accepts at each of the three chains' sendings. -/
theorem mainRoom_test :
    ([proofSendsFull.1, proofSendsFull.2.1, proofSendsFull.2.2].all fun c =>
      roomIsNone (mainRoomFault c (firstCodes proofSendsFull.1 proofSendsFull.2.1))) = true := by
  rw [firstCodes_written]
  unfold mainRoomFault isSwitch
  simp only [Johnson.Unfolds.splitOn_eq, mainRooms_by]
  rw [testOf_isK]
  decide +kernel

/-- **AT NONE OF THE THREE CHAINS HAVE A SWITCH's MAIN ROWS PLACES LEFT FREE, OR TOO FEW
PLACES.** -/
theorem mainRoomFault_written :
    ∀ c ∈ [proofSendsFull.1, proofSendsFull.2.1, proofSendsFull.2.2],
      mainRoomFault c (firstCodes proofSendsFull.1 proofSendsFull.2.1) = .ok none :=
  fun c hc => roomIsNone_eq (List.all_eq_true.1 mainRoom_test c hc)

/-- **THE TEST CAN FAIL**: each list with its first count greater by one; the shared chain's also
with its two rows swapped and with its last row dropped. -/
theorem switch_bite :
    rowsAre (switchRows WP.first.blocksInOrder proofSendsFull.1
        (firstCodes proofSendsFull.1 proofSendsFull.2.1))
        [(⟨⟨1, none, 2, .K12⟩, 1⟩, ⟨0, 38039⟩)] = false ∧
      rowsAre (switchRows WP.shared.blocksInOrder proofSendsFull.2.1
        (firstCodes proofSendsFull.1 proofSendsFull.2.1))
        ((⟨⟨2, none, 9, .K12⟩, 1⟩, ⟨0, 8063⟩) :: switchSharedW.drop 1) = false ∧
      rowsAre (switchRows WP.shared.blocksInOrder proofSendsFull.2.1
        (firstCodes proofSendsFull.1 proofSendsFull.2.1)) switchSharedW.reverse = false ∧
      rowsAre (switchRows WP.shared.blocksInOrder proofSendsFull.2.1
        (firstCodes proofSendsFull.1 proofSendsFull.2.1)) switchSharedW.dropLast = false ∧
      rowsAre (switchRows WP.second.blocksInOrder proofSendsFull.2.2
        (firstCodes proofSendsFull.1 proofSendsFull.2.1))
        [(⟨⟨3, none, 2, .K12⟩, 1⟩, ⟨0, 12779⟩)] = false := by
  rw [switchRows_first_written, switchRows_shared_written, switchRows_second_written]
  decide +kernel

/-- **mainRoomFault CAN ANSWER OTHERWISE**: with a first stage whose base code has the message
length 1 laid for every test, it names the second chain's first switch. -/
theorem mainRoom_bite :
    mainRoomFault proofSendsFull.2.2 (fun _ => some (⟨0, 1, 0⟩, ⟨0, 1, 0⟩)) =
      .ok (some "the own test, the code switch of stage 1") := by
  unfold mainRoomFault isSwitch
  simp only [Johnson.Unfolds.splitOn_eq, mainRooms_by]
  rw [testOf_isK]
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.testOf_isK
#print axioms AtFullSide.K14.firstCodes_written
#print axioms AtFullSide.K14.switch_test
#print axioms AtFullSide.K14.switchRows_first_written
#print axioms AtFullSide.K14.switchRows_shared_written
#print axioms AtFullSide.K14.switchRows_second_written
#print axioms AtFullSide.K14.roomIsNone_eq
#print axioms AtFullSide.K14.mainRoom_test
#print axioms AtFullSide.K14.mainRoomFault_written
#print axioms AtFullSide.K14.switch_bite
#print axioms AtFullSide.K14.mainRoom_bite
