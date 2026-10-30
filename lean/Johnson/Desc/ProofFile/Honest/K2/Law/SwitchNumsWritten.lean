-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SwitchNumsWritten.lean: THE SEATS AND NUMBERS OF THE SWITCHES'
MESSAGES (`switchSeatIn`, `switchNumIn`, Honest/K2/SwitchNums.lean) AT THE WRITTEN LISTS: THE
WRITTEN PLACES `placesW` AND THE WRITTEN PLAN's SEATS `P5T.seatsAllFull`: CLOSED FACTS, EACH AN
EVALUATION IN LEAN's KERNEL. Eight definitions, public tests and one list; lemmas; none of the
library's goals.

THE TESTS, each on a list of seats ps, a place p and a number n (or on all n below the number of p's
messages):
  `keptRole`       the role is that of a kept copy
  `seatOnce`       a seat stands in "link l, moment 0" at the place n, and just one
  `firstHolds`     the first holder of that seat's tree and tenant in ps has the seat's own key
  `firstNotKept`   the switch is message n's first sender just where the seat's role is no kept
                   copy's
  `ownNumOk`       where the seat's role is "own k", its number is `P5T.numOfPlan` ps l k
  `ownBack`        each message k of link l of the shape whose moment is 0 is the role of a first
                   sender's seat
  `allMsgs`        a test holds at every n below the number of p's messages
  `firstNums`      the numbers of the first senders of a list of places, in a row

THE FACTS, at each place of the written list:
  `seatOnceW` `firstHoldsW` `firstNotKeptW` `ownNumW` `ownBackW`   the five tests accept
  `sentMeetsW`     the written plan's sending in which the seats stand (`Johnson.G.proofSends0`, at
                   the seat's field send) has the place's messages whole; the codes are the written
                   plan's
  `ownBackW_bites` `ownBack` has matter and can fail: over the written places' links 46 messages
                   have moment 0; A CONTROL: at an empty list of seats it refuses the first written
                   place. By reading, stated by no fact here: the last place's link has no such
                   message: there the test is true for want of any
  `numsApartW`     **`numsApart` p accepts at the numbers `switchNumIn`**
  `firstNumsW`     **the first senders of all written places are 96, and their numbers are all
                   different**
  `numsApartW_can_fail`   CONTROLS: with the kept copies in, the numbers of all messages of all
                   written places are 98 different ones, and some repeat; then four that look at
                   `placesW.take 1` and no further: a constant numbering fails; a segment that is
                   not there fails (no seat is found, so every number is the one default: the
                   constant case over again); AT THE NEIGHBOUR's SEATS `numsApart` STILL ACCEPTS,
                   and `firstNotKept` says no: so `numsApartW` alone does not tell whose the numbers
                   are. That is what `sentMeetsW`, `firstNotKeptW` and `ownNumW` are there for; a
                   control shows it of `firstNotKept` alone

The number of written places is 25 (`placesW_count`, PlacesCount.lean of this folder).

WHAT IT IS NOT. Facts on written lists: no state, no run, no input; no lot of messages is laid.
`sentMeetsW` stays at the written sendings: that the public part's own sendings are these is not
said here.

NEAR. `sentW` (Johnson/Top/H0/K2Hands/FrontsFullTied.lean): what the code switch into a group
announces at the written shape: near, not called. `seatsOfLink`
(Johnson/Desc/First/Close/Law/SeatsOfLink.lean), `numsApartB`, `numsApart_full` (SeatsApart.lean
there): another kind's seats off the same list, and their numbers apart. `arrOf_is_num`
(Johnson/P5T/NumOfPlan.lean), `arrOf_key` (Johnson/P5T/ArrApart.lean): with `firstHoldsW` they give
`ownNumW`, and read `numsApartW` as "different keys"; not called. `AtMg.arr_is_num`,
`AtMg.num_apart` (Honest/K5/Law/NumsCover.lean, another group of authors'):
some seat with the key (0, l, k) has that number; the numbers of two own messages differ.

Limits. Evaluations, each with the option maxRecDepth raised for that one fact. The full size alone.
Five limbs of the two facts with controls look at `placesW.take 1` and no further. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.SwitchNums
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots
import Johnson.HB.LLHARD.MaskSeatWritten
import Johnson.G.SendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open P5T (PSeat Role seatsAllFull keyOf numOfPlan)
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- The role is that of a kept copy. -/
def keptRole : Role → Bool
  | .kept _ _ => true
  | _ => false

/-- A seat stands in "link l, moment 0" at the place n, and just one. -/
def seatOnce (ps : List PSeat) (l n : Nat) : Bool :=
  (switchSeatIn ps l n).isSome && (ps.countP fun q => q.seg == some (l, 0) && q.idx == n) == 1

/-- The first holder of the seat's tree and tenant has the seat's own key. -/
def firstHolds (ps : List PSeat) (l n : Nat) : Bool :=
  (switchSeatIn ps l n).any fun q =>
    (ps.find? fun x => x.j == q.j && x.t == q.t).map keyOf == some (keyOf q)

/-- The switch is the first sender just where the seat's role is no kept copy's. -/
def firstNotKept (ps : List PSeat) (p : SwitchPlace) (n : Nat) : Bool :=
  (switchSeatIn ps p.link n).any fun q => firstSender p n == !keptRole q.role

/-- Where the seat's role is "own k" its number is the plan's number of (l, k). -/
def ownNumOk (ps : List PSeat) (l n : Nat) : Bool :=
  match (switchSeatIn ps l n).map (·.role) with
  | some (Role.own k) => switchNumIn ps l n == numOfPlan ps l k
  | _ => true

/-- A test holds at every n below the number of the place's messages. -/
def allMsgs (p : SwitchPlace) (f : Nat → Bool) : Bool :=
  (List.range (switchSent p.sizes p.others).size).all f

/-- Each message of link p.link of the shape whose moment is 0 is the role of a first sender's seat.
-/
def ownBack (S : OnBytes.Params.ReqShape) (ps : List PSeat) (p : SwitchPlace) : Bool :=
  ((((S.link[p.link]?).map (·.messages)).getD []).zipIdx.filter fun x => x.1.moment == 0).all
    fun x => (List.range (switchSent p.sizes p.others).size).any fun n =>
      firstSender p n && ((switchSeatIn ps p.link n).map (·.role) == some (Role.own x.2))

/-- The numbers of the first senders of a list of places, in a row. -/
def firstNums (num : SwitchPlace → Nat → Nat) (l : List SwitchPlace) : List Nat :=
  l.flatMap fun p =>
    ((List.range (switchSent p.sizes p.others).size).filter (firstSender p)).map (num p)

set_option maxRecDepth 1000000 in
/-- A seat, and just one, at every message of every written place. -/
theorem seatOnceW : (placesW.all fun p => allMsgs p (seatOnce seatsAllFull p.link)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The first holder has the seat's own key. -/
theorem firstHoldsW : (placesW.all fun p => allMsgs p (firstHolds seatsAllFull p.link)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- First sender: just where the plan calls the member no kept copy. -/
theorem firstNotKeptW : (placesW.all fun p => allMsgs p (firstNotKept seatsAllFull p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written plan's sending has the place's messages whole; the codes are the plan's. -/
theorem sentMeetsW :
    (placesW.all fun p => (switchSeatIn seatsAllFull p.link 0).any fun q =>
        (Johnson.G.proofSends0.sends[q.send]?).any fun s =>
          decide (s.sent = (switchSent p.sizes p.others).toList)) = true ∧
      (placesW.all fun p => decide (p.sizes.codes = Johnson.G.proofSends0.codes)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test `numsApart` accepts at the seats' numbers.** -/
theorem numsApartW :
    (placesW.all fun p => numsApart p (switchNumIn seatsAllFull p.link)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Across the written places too.** -/
theorem firstNumsW :
    (firstNums (fun p => switchNumIn seatsAllFull p.link) placesW).length = 96 ∧
      (firstNums (fun p => switchNumIn seatsAllFull p.link) placesW).Nodup := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At an own message the number is the plan's number of the link's message. -/
theorem ownNumW : (placesW.all fun p => allMsgs p (ownNumOk seatsAllFull p.link)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each message of moment 0 of the link is a first sender's. -/
theorem ownBackW : (placesW.all (ownBack shapeFull seatsAllFull)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test has matter and can fail**: how many messages its `all` meets, summed place by place;
a control: handed `[]` for the seats it refuses `placesW.take 1`. -/
theorem ownBackW_bites :
    ((placesW.map fun p => ((((shapeFull.link[p.link]?).map (·.messages)).getD []).filter
        fun x => x.moment == 0).length).sum = 46) ∧
      ((placesW.take 1).all (ownBack shapeFull [])) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Controls.** With the kept copies in, the numbers are 98 different ones, and some repeat. At
the first written place: a constant numbering fails; a segment that is not there fails; at the
neighbour's seats `numsApart` still accepts, and `firstNotKept` says no. -/
theorem numsApartW_can_fail :
    ((placesW.flatMap fun p => (List.range (switchSent p.sizes p.others).size).map
        (switchNumIn seatsAllFull p.link)).eraseDups.length = 98) ∧
      ¬ (placesW.flatMap fun p => (List.range (switchSent p.sizes p.others).size).map
        (switchNumIn seatsAllFull p.link)).Nodup ∧
      ((placesW.take 1).all fun p => numsApart p fun _ => 0) = false ∧
      ((placesW.take 1).all fun p => numsApart p (switchNumIn seatsAllFull (p.link + 30))) = false ∧
      ((placesW.take 1).all fun p => numsApart p (switchNumIn seatsAllFull (p.link + 1))) = true ∧
      ((placesW.take 1).all fun p =>
        allMsgs p (firstNotKept seatsAllFull { p with link := p.link + 1 })) = false := by
  decide +kernel

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.keptRole
#print axioms ProofFile.Honest.K2.Law.seatOnce
#print axioms ProofFile.Honest.K2.Law.firstHolds
#print axioms ProofFile.Honest.K2.Law.firstNotKept
#print axioms ProofFile.Honest.K2.Law.ownNumOk
#print axioms ProofFile.Honest.K2.Law.allMsgs
#print axioms ProofFile.Honest.K2.Law.ownBack
#print axioms ProofFile.Honest.K2.Law.firstNums
#print axioms ProofFile.Honest.K2.Law.seatOnceW
#print axioms ProofFile.Honest.K2.Law.firstHoldsW
#print axioms ProofFile.Honest.K2.Law.firstNotKeptW
#print axioms ProofFile.Honest.K2.Law.sentMeetsW
#print axioms ProofFile.Honest.K2.Law.numsApartW
#print axioms ProofFile.Honest.K2.Law.firstNumsW
#print axioms ProofFile.Honest.K2.Law.ownNumW
#print axioms ProofFile.Honest.K2.Law.ownBackW
#print axioms ProofFile.Honest.K2.Law.ownBackW_bites
#print axioms ProofFile.Honest.K2.Law.numsApartW_can_fail
