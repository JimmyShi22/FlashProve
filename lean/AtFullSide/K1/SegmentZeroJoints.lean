-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/SegmentZeroJoints.lean: THE JOINTS BETWEEN THE SENDER's SIDE AND THE BOOK's SIDE AT
THE FIRST SEGMENT, AT THE FULL SIZE's WRITTEN DATA: SO THAT K1's OWN maskStart
(Johnson/Desc/ProofFile/Honest/K1/MaskLaw.lean) AND A SPENDER's FIRST COIN STAND IN ONE LINE. 
Three joints between Johnson/Desc/ProofFile/Honest/K1/Law/RowOwnerAtWritten.lean
and AtFullSide/K1/SegmentZeroAtWritten.lean made by eye, not by Lean: the owner (⟨K1.parGF.place,
0⟩ there, a written address here) · the start (our maskStart there, another house's written base
here) · the two spellings of the written blocks. PUBLIC DATA ALONE: addresses and numbers: where a
run of coins begins, never what stands in it. Eleven theorems; NO DEFINITION. A TRIAL THAT COUNTS
IN NO COLUMN.
NO PROPERTY IS CLAIMED.

ownerJoint the written mask row's owner IS ⟨K1.parGF.place, 0⟩. startJoint, startZero its base's
count of the extension field IS our maskStart at the opening's written plan, the ride, message 0;
and that number is 0. rowOwnerAtWP (A1) AT THE OTHER SPELLING: the maker's ownerOf AT
WP.first.blocksInOrder, the written sendings and rawLater, under "link 0, moment 0" and isMaskRowMsg: its
owner is ⟨K1.parGF.place, 0⟩ and its base's count of the extension field is our maskStart at
message 0: one evaluation in Lean's kernel. SO (A1) STANDS AT BOTH SPELLINGS: rowOwnerW has it at
blocksOfRows cutFirstFull declProofFull.1. rowOwnerAtWP_bent the evaluation can fail: with message
1 for message 0 it rejects. rowOwnerAtWP_bites, rowFreeAtWP, rowBaseAtWP (A3), (A5) AND THE
CLOSED-NUMBER WORK, AT THIS SPELLING TOO: of the five messages number 0 alone has that start · the
maker's free entries are 8191 · ownerOf's base is the maker's maskStart at the plan's codes and
messages, number 0. rowBaseAtWP_bent rowBaseAtWP's three bent twins, as at the other spelling: the
number; THE OWNER, twice. SO EACH OF RowOwnerAtWritten.lean's SEVEN STATEMENTS THAT EVALUATE
ownerOf (rowBaseW · rowOwnerW · rowOwnerW_bites · rowFreeW's first half · rowBaseW_bent ·
rowBaseW_bent_owner · and, under the head, rowOwnerW_head's left side) HAS ITS LIKE HERE AT WP's
SPELLING, BUT FOR THE LAST: nothing here stands under the head. rowOwnerAtWP is an evaluation; THE
INSTANCE OF THE GENERAL LAW (rowOwnerW, by maskStart_book_e) STANDS AT THE OTHER SPELLING ALONE;
with rowBaseAtWP it could be had here by the same three lines. segmentZero_joined WHATEVER BOOK
bookWhole RETURNS AT WP: the three places' blocks, WITH THE OWNER AS ⟨K1.parGF.place, 0⟩ AND THE
FIRST COIN AS OUR maskStart … 0 + THE SEGMENT's OWN SCALARS IN FRONT (0 · 1930 · 2696).
k4RowOk_bent_rest FOUR BENT TWINS MORE OF k4RowOk: the count (766 for 765) · the number of the
merge's entry (1 for 0) · its count (2 for 1) · the parts' number (20 for 19): each is rejected.

THAT THE TWO SPELLINGS ARE ONE LIST IS NOT SHOWN HERE: WP.first.blocksInOrder =
blocksOfRows cutFirstFull declProofFull.1; and rawLater = declProofFull.2.2.
IF THEY ARE, THE SIX STATEMENTS HERE THAT EVALUATE ownerOf AT WP's SPELLING
SPEAK OF THE VERY TERM OF RowOwnerAtWritten.lean's SIX: rowOwnerAtWP is rowOwnerW's equation ·
rowOwnerAtWP_bites is rowOwnerW_bites' · rowFreeAtWP is rowFreeW's first half · rowBaseAtWP is
rowBaseW's · rowBaseAtWP_bent is rowBaseW_bent's with rowBaseW_bent_owner's two · rowOwnerAtWP_bent
has no like there (it follows from rowOwnerW_bites). No corollary is typed.





Limits. THE FULL SIZE ALONE. Evaluations in Lean's kernel (decide +kernel): no compiled code;
maxRecDepth is raised to 1000000 in front of them. The limits of the files called stand: that any
description but WP has these values is not said; the sendings are found by labels that rest on one
print; THE MERGES ARE A GUESS. Nothing on a run, or on what any coin is. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.SegmentZeroAtWritten
import Johnson.Desc.ProofFile.Honest.K1.Law.OwnerAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K1
open AtFullSide.K14
open VerifiableInference.Desc
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K1 (parGF)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The written mask row's owner is the opening's sender, by the plan's own place. -/
theorem ownerJoint : rowZeroW.owner = ⟨parGF.place, 0⟩ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Its base's count of the extension field is our maskStart at message 0. -/
theorem startJoint : rowZeroW.base.e = maskStart parGF (rideOf (firstFold K1.qFull)) 0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- That number is 0. -/
theorem startZero : maskStart parGF (rideOf (firstFold K1.qFull)) 0 = 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(A1) AT THE OTHER SPELLING OF THE WRITTEN BLOCKS.** -/
theorem rowOwnerAtWP : (ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      "link 0, moment 0" isMaskRowMsg).map (fun m => (m.owner, m.base.e)) =
    some ((⟨parGF.place, 0⟩ : Addr), maskStart parGF (rideOf (firstFold K1.qFull)) 0) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluation can fail: with message 1 for message 0 it rejects. -/
theorem rowOwnerAtWP_bent : decide ((ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      "link 0, moment 0" isMaskRowMsg).map (fun m => (m.owner, m.base.e)) =
    some ((⟨parGF.place, 0⟩ : Addr), maskStart parGF (rideOf (firstFold K1.qFull)) 1)) =
    false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- (A3) at this spelling: of the opening's messages number 0 alone has that start. -/
theorem rowOwnerAtWP_bites : ((List.range parGF.sent.size).filter fun n =>
    decide ((ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      "link 0, moment 0" isMaskRowMsg).map (·.base.e) =
      some (maskStart parGF (rideOf (firstFold K1.qFull)) n))) = [0] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- (A5) at this spelling: the maker's free entries. -/
theorem rowFreeAtWP : (ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      "link 0, moment 0" isMaskRowMsg).map (·.free) = some 8191 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The closed-number work at this spelling: ownerOf's base is the maker's maskStart at the plan's
codes, k = 8 (idle at number 0), the plan's messages, number 0. -/
theorem rowBaseAtWP : (ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      "link 0, moment 0" isMaskRowMsg).map (fun m => (m.owner, m.base)) =
    (_root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 0).map
      fun st => ((⟨parGF.place, 0⟩ : Addr), st) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- rowBaseAtWP's three bent twins, as at the other spelling: number 1 for number 0; THE OWNER BENT,
twice: another part of the opening's place; the place of the segment's next sending of the kind
K1. Each is rejected. -/
theorem rowBaseAtWP_bent :
    decide ((ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      "link 0, moment 0" isMaskRowMsg).map (fun m => (m.owner, m.base)) =
      (_root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 1).map
        fun st => ((⟨parGF.place, 0⟩ : Addr), st)) = false ∧
    decide ((ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      "link 0, moment 0" isMaskRowMsg).map (fun m => (m.owner, m.base)) =
      (_root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 0).map
        fun st => ((⟨parGF.place, 1⟩ : Addr), st)) = false ∧
    decide ((ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1 rawLater
      "link 0, moment 0" isMaskRowMsg).map (fun m => (m.owner, m.base)) =
      (_root_.ProofFile.Honest.maskStart parGF.codes 8 parGF.sent.toList 0).map
        fun st => ((⟨⟨1, some 0, 4, .K1⟩, 0⟩ : Addr), st)) = false := by
  decide +kernel

/-- **OUR maskStart AND EACH SPENDER's FIRST COIN IN ONE LINE.** -/
theorem segmentZero_joined {B : ProverCoinCounts} (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1
                  proofSendsFull.2.2 (mergesByName WP.first.blocksInOrder) = .ok B) :
    oneStretch (rowEntries B ⟨1, some 0, 2, .K3⟩ 135 0) =
        some (⟨parGF.place, 0⟩, maskStart parGF (rideOf (firstFold K1.qFull)) 0 + 0, 1930) ∧
      (∃ es₁, rowEntries B ⟨1, some 0, 3, .K4⟩ 19 0 =
          es₁ ++ [(⟨⟨⟨1, some 0, 3, .K4⟩, 18⟩, "ends", rawIdxW, 0, 1⟩ : Want).entry] ∧
        oneStretch es₁ =
          some (⟨parGF.place, 0⟩, maskStart parGF (rideOf (firstFold K1.qFull)) 0 + 1930, 765)) ∧
      oneStretch (rowEntries B ⟨1, some 0, 7, .K3⟩ 113 0) =
        some (⟨parGF.place, 0⟩, maskStart parGF (rideOf (firstFold K1.qFull)) 0 + 2696, 1363) := by
  have j : (⟨parGF.place, 0⟩ : Addr) = ⟨⟨1, some 0, 1, .K1⟩, 0⟩ := ownerJoint.symm
  rw [j, startZero]
  exact ⟨k3RowAt2 hB, k4MergeRowAt hB, k3RowAt7 hB⟩

set_option maxRecDepth 1000000 in
/-- Four bent twins more of k4RowOk: the count; the number and the count of the merge's entry; the
parts' number. -/
theorem k4RowOk_bent_rest :
    mergeRowOk ⟨1, some 0, 3, .K4⟩ 19 18 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 1930 766 0 1 = false ∧
    mergeRowOk ⟨1, some 0, 3, .K4⟩ 19 18 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 1930 765 1 1 = false ∧
    mergeRowOk ⟨1, some 0, 3, .K4⟩ 19 18 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 1930 765 0 2 = false ∧
    mergeRowOk ⟨1, some 0, 3, .K4⟩ 20 18 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 1930 765 0 1 = false := by
  decide +kernel

end AtFullSide.K1

#print axioms AtFullSide.K1.ownerJoint
#print axioms AtFullSide.K1.startJoint
#print axioms AtFullSide.K1.startZero
#print axioms AtFullSide.K1.rowOwnerAtWP
#print axioms AtFullSide.K1.rowOwnerAtWP_bent
#print axioms AtFullSide.K1.rowOwnerAtWP_bites
#print axioms AtFullSide.K1.rowFreeAtWP
#print axioms AtFullSide.K1.rowBaseAtWP
#print axioms AtFullSide.K1.rowBaseAtWP_bent
#print axioms AtFullSide.K1.segmentZero_joined
#print axioms AtFullSide.K1.k4RowOk_bent_rest
