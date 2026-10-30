-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/OwnData.lean: the honest side of the kind "the code switch" (K2):
THE DATA OF THE SWITCHES' OWN MESSAGES, AS A TERM, AND HOW IT IS JOINED TO ANOTHER LOT's DATA. It
defines part of the honest prover: it is for the frame's letter for the rows' data, which the kind's
lot takes as `D`; no file of this kind calls `withSwitchData`. Definitions with code; five
statements by unfolding. Its tests stand in Honest/K2/ToyOwnData.lean.

WHY. A segment's own messages of moment 0 hold the arrays "M mu" of its matrices. The first
segment's are sent at a place of the shared sending's kind; every later segment's are sent BY THE
SWITCH THAT LEADS INTO IT, behind the carrying message and the copies. What stands in them is one
function at all segments (`K1.firstData`, Honest/K1/FirstData.lean), which takes the seat as a
letter and says of the switches' sendings: at which number the own messages begin is this kind's to
say. Here it is said.

  `ownSeats`        for each place of the kind: the part's address, the segment into which the
                    switch leads, and the number of its first own message: 1 and the kept members
  `seatBy`, `switchSeat`   THE SEAT: the address of an own message of moment 0 in a switch's sending
                    ↦ the segment and the message's number in its list; nothing at every other
                    address: the carrying message, a copy, the fresh mask, another kind's sending
  `switchData`      THE DATA at these seats. It says that no challenge has been heard: the switch's
                    own sending's data is asked at no challenge (Honest/K2/Half.lean), and the lot's
                    closing refuses a filling that says otherwise (`ownLaid`, Honest/K2/AtPlan.lean)
  `withSwitchData`  a filling for the kind's lot and for the lot whose data is handed in, alike: at
                    a seat of a switch's own message `switchData`; at every other address the other
  `switchData_heard`, `with_own`, `with_else`   no challenge; what the joined filling hands out by
                    `RowData.at_`
  `with_own_lays`, `with_own_ready`   at a seat of a switch's own message its two public answers,
                    which the lot's public test asks, are `switchData`'s too

THE KEPT COPIES WANT NO DATA HERE: the half takes their rows off what the fold in front left
(Honest/K2/AtPlan.lean).

Limits. S, the sizes that `K1.firstData` reads, stays a letter. The seat is made of `switchPlaces`
and of the ground's own shape: that the planner's request, of which the places are made, is that
shape is not shown here. That the seat undoes the places' own addresses (`SwitchPlace.ownAddr`) and
agrees with the way back of Honest/K2/Seat.lean (`seatOf`) is tested at a toy, not proved. That the
layout lays into these messages no array but those that `K1.cellsVals` serves is not shown: the
lot's public test (`ownLaid`) says at a plan whether each array is laid. No entry is evaluated here.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.ProofFile.Honest.K1.FirstData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes.HonestTrace (Sz)

variable {Xi : Type}

/-- For each place of the kind: the part's address; the segment into which the switch leads; the
number, in the switch's sending, of that segment's first own message. -/
def ownSeats (Z : Pub) (G : Ground) : List (Addr × Nat × Nat) :=
  (switchPlaces Z G).map fun p => (⟨p.place, 0⟩, p.link, 1 + p.sizes.kept.length)

/-- **The seat**, of a request's shape and such a list. -/
def seatBy (s : OnBytes.Params.ReqShape) (l : List (Addr × Nat × Nat)) (a : MsgAddr) :
    Option (Nat × Nat) :=
  l.findSome? fun x => K1.momentSeat s x.1 x.2.1 0 x.2.2 a

/-- **THE SEAT of the switches' own messages**, at a plan's public data. -/
def switchSeat (Z : Pub) (G : Ground) : MsgAddr → Option (Nat × Nat) :=
  seatBy G.first.shape (ownSeats Z G)

/-- **THE DATA OF THE SWITCHES' OWN MESSAGES.** -/
def switchData (S : Sz) (Z : Pub) (G : Ground) : RowData :=
  K1.firstData S G.first.codes G.first.shape G.first.layout (switchSeat Z G) fun _ => 0

/-- **That data, joined to another lot's.** D: the other lot's data. -/
def withSwitchData (S : Sz) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    RowDataOf Xi :=
  let seat := switchSeat Z G
  let own := switchData S Z G
  fun x => RowData.join (fun a => (seat a).isSome) own (D Z G x)

/-- It says that no challenge has been heard. -/
theorem switchData_heard (S : Sz) (Z : Pub) (G : Ground) (a : MsgAddr) :
    (switchData S Z G).heardAt a = 0 := rfl

/-- At a seat of a switch's own message the joined filling hands out `switchData`'s. -/
theorem with_own (S : Sz) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi)
    (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat)
    (h : (switchSeat Z G a).isSome = true) :
    (withSwitchData S D Z G x).at_ R hd a r j = (switchData S Z G).at_ R hd a r j := by
  unfold withSwitchData RowData.at_ RowData.join
  simp only [h, if_true]

/-- There it lays what `switchData` lays. -/
theorem with_own_lays (S : Sz) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi)
    (a : MsgAddr) (h : (switchSeat Z G a).isSome = true) :
    (withSwitchData S D Z G x).lays a = (switchData S Z G).lays a := by
  unfold withSwitchData RowData.join
  simp only [h, if_true]

/-- There it is ready where `switchData` is. -/
theorem with_own_ready (S : Sz) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi)
    (hd : List Fmt.Drawn) (a : MsgAddr) (h : (switchSeat Z G a).isSome = true) :
    (withSwitchData S D Z G x).readyAt hd a = (switchData S Z G).readyAt hd a := by
  unfold RowData.readyAt RowData.heardOk withSwitchData RowData.join
  simp only [h, if_true]

/-- At every other address the other lot's. -/
theorem with_else (S : Sz) (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi)
    (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat)
    (h : (switchSeat Z G a).isSome = false) :
    (withSwitchData S D Z G x).at_ R hd a r j = (D Z G x).at_ R hd a r j := by
  unfold withSwitchData RowData.at_ RowData.join
  simp only [h, Bool.false_eq_true, if_false]

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.switchData_heard
#print axioms ProofFile.Honest.K2.with_own
#print axioms ProofFile.Honest.K2.with_own_lays
#print axioms ProofFile.Honest.K2.with_own_ready
#print axioms ProofFile.Honest.K2.with_else
#print axioms ProofFile.Honest.K2.ownSeats
#print axioms ProofFile.Honest.K2.seatBy
#print axioms ProofFile.Honest.K2.switchSeat
#print axioms ProofFile.Honest.K2.switchData
#print axioms ProofFile.Honest.K2.withSwitchData
