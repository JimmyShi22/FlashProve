-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ShrSeats.lean: the closing of a segment (K10): closed tests, by Lean's kernel, at the written plan: the seat and the shape
that the plan gives a member of the closing's group are the seat and the shape of the message of the shared sending (the kind K1) that
stands at that place of the group's list. For the clause on seats and shapes of the field stand of `TieByShared`
(Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieByShared.lean), and for the count of the first segment's group.

A law on a reached state (Pay/SeatsAtStand.lean) speaks in the plan's terms (`seatK10`, `loAt`, `membersOf`). The laws on the first chain's
script speak of the seat `seatAtMember` (Honest/K1/Seated.lean): how the sending's own messages are laid into trees, behind as many trees as
the sub-protocols in front state.

  `shrSeatS`, `seatOfMsg_is`   the body of the library's `seatOfMsg` as a function of the codes and the messages announced; the tie, by unfolding
  `shrMemberTest e l pos sent b n`   the member at the place pos of segment l's list has the seat of message number n of the sending sent at
                     the chain's sub-protocol number b, and its shape. e: a number added to the tenant that is asked for: 0 in the test
  `shrPosLater`          the place of a later moment's message in the group's list: behind the opening's three (segment 0), or behind the code
                     switch's messages but the last
  **`shrLater_written`**   both later moments' messages, at all 25 segments      `shrLater_bent`   THE TEST CAN FAIL: at e = 1 it rejects everywhere
  **`shrOpen_written`**    the opening's first three messages, at segment 0       `shrOpen_bent`    the like
  `shrCount_zero`        the first segment's group has five members
  `shrMember_says`       what `shrMemberTest` says, as equations

Limits. Written values alone, at the full size. That the head's lists are the written ones is the library's. This file proves no property of
a prover or a protocol.
-/
import AtFullSide.K10.XchAtBookShared
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSeats
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.K1.Law.WordsAtPlace
import Johnson.Desc.K1.Law.LaterOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open OnBytes (Codes OracleNotice layTrees)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open VerifiableInference.Desc.First.Close (seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K1 (noL seatOfMsg)
open ProofFile.Honest.K2 (SwitchPlace switchSent)
open ProofFile.Honest.K2.Law (placesW)
open Johnson.G (codesFull2)

/-- The seat (tree, tenant) of message number j of a sending, behind nT trees: of the codes and the messages announced. -/
def shrSeatS (codes : Codes) (sent : Array OracleNotice) (nT j : Nat) : Nat × Nat :=
  (nT + ((layTrees codes sent).getD {}).tree.getD j 0, ((layTrees codes sent).getD {}).part.getD j 0)

/-- It is the library's term. -/
theorem seatOfMsg_is (P : VerifiableInference.Desc.K1.Par) (nT j : Nat) : seatOfMsg P nT j = shrSeatS P.codes P.sent nT j := rfl

/-- The test at one member. -/
def shrMemberTest (e l pos : Nat) (sent : Array OracleNotice) (b n : Nat) : Bool :=
  match (VerifiableInference.Desc.First.Close.membersOf (loAt l))[pos]? with
  | some i =>
    decide (seatK10 (loAt l) P5T.psFull l i =
      ((shrSeatS codesFull2 sent (treesTold toldFull b) n).1, (shrSeatS codesFull2 sent (treesTold toldFull b) n).2 + e)) &&
      decide (((loAt l).get i).1 = (sent.getD n default).shape)
  | none => false

/-- The place of the first later moment's message in segment l's list; none where the written places have no switch into l ≥ 1. -/
def shrPosLater (l : Nat) : Option Nat :=
  if l = 0 then some 3 else (placesW.find? (·.link == l)).map fun p => (switchSent p.sizes p.others).size - 1

/-- Both later moments, at segment l. -/
def shrLaterTest (e l : Nat) : Bool :=
  match shrPosLater l with
  | some c => shrMemberTest e l c (sentLater l 1) (noL l false) 0 && shrMemberTest e l (c + 1) (sentLater l 2) (noL l true) 0
  | none => false

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- **At all 25 segments the plan's seats and shapes of these two members are the later moments' messages'.** -/
theorem shrLater_written : ((List.range 25).all fun l => shrLaterTest 0 l) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem shrLater_bent : ((List.range 25).any fun l => shrLaterTest 1 l) = false := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- **At the first segment the plan's seats and shapes of the first three members are the opening's messages'.** -/
theorem shrOpen_written : ((List.range 3).all fun n => shrMemberTest 0 0 n sentOpen 2 n) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem shrOpen_bent : ((List.range 3).any fun n => shrMemberTest 1 0 n sentOpen 2 n) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The first segment's group has five members. -/
theorem shrCount_zero : (VerifiableInference.Desc.First.Close.membersOf (loAt 0)).length = 3 + 1 + 1 := by decide +kernel

/-- **What the test says at one member.** -/
theorem shrMember_says {l pos : Nat} {sent : Array OracleNotice} {b n : Nat} (h : shrMemberTest 0 l pos sent b n = true) :
    ∃ i, (VerifiableInference.Desc.First.Close.membersOf (loAt l))[pos]? = some i ∧
      seatK10 (loAt l) P5T.psFull l i = shrSeatS codesFull2 sent (treesTold toldFull b) n ∧
      ((loAt l).get i).1 = (sent.getD n default).shape := by
  unfold shrMemberTest at h
  cases hi : (VerifiableInference.Desc.First.Close.membersOf (loAt l))[pos]? with
  | none =>
    rw [hi] at h
    cases h
  | some i =>
    rw [hi] at h
    obtain ⟨a1, a2⟩ := Eq.mp (Bool.and_eq_true _ _) h
    exact ⟨i, rfl, of_decide_eq_true a1, of_decide_eq_true a2⟩

/-- What the test on the later moments says at one segment. -/
theorem shrLater_says {l : Nat} (hl : l < 25) :
    ∃ c, shrPosLater l = some c ∧ shrMemberTest 0 l c (sentLater l 1) (noL l false) 0 = true ∧
      shrMemberTest 0 l (c + 1) (sentLater l 2) (noL l true) 0 = true := by
  have h := List.all_eq_true.1 shrLater_written l (List.mem_range.2 hl)
  unfold shrLaterTest at h
  cases hc : shrPosLater l with
  | none =>
    rw [hc] at h
    cases h
  | some c =>
    rw [hc] at h
    obtain ⟨a1, a2⟩ := Eq.mp (Bool.and_eq_true _ _) h
    exact ⟨c, rfl, a1, a2⟩

end AtFullSide.K10

#print axioms AtFullSide.K10.seatOfMsg_is
#print axioms AtFullSide.K10.shrLater_written
#print axioms AtFullSide.K10.shrLater_bent
#print axioms AtFullSide.K10.shrOpen_written
#print axioms AtFullSide.K10.shrOpen_bent
#print axioms AtFullSide.K10.shrCount_zero
#print axioms AtFullSide.K10.shrMember_says
#print axioms AtFullSide.K10.shrLater_says
