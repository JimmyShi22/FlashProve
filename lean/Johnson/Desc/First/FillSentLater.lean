-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/FillSentLater.lean: A LAYER OF THE FILLING OF THE TABLE OF JOINTS' MEANING: ONE
PUBLIC ITEM MORE THROUGH THE DOOR (`Pub.more`, Johnson/Desc/First/Borders.lean): (some m,
"frame.sentIs1"): THE TEST OF "frame.sentIs" (`sentIsB`, Johnson/Desc/First/FillSent.lean) ONCE
MORE, AT THE LONGER LIST OF A SEGMENT's OWN MESSAGES THAT STANDS BEHIND THE SEGMENT's SECOND
SENDING. One text, two names. Small; no Mathlib. A file BESIDE FillSent.lean: it turns nothing of
it.

Why. "frame.sentIs" is dropped at the segment's second sending, where the open segment's frame's
list own grows. A sub-protocol behind that sending which reads a message's number through the frame
(`ReqFrame.whereIs`) wants the like sentence at the longer list.

  `laterOf d more`: the data d with more m appended to own m; born, kept and trees as they are.
  `secondNos shape base1 m`: the numbers of the second sending's messages: base1 m, base1 m + 1, …,
    as many as the segment has messages of moment 1. base1 m: how many oracle messages are sent in
    front of that sending. BY A READING of `ReqFrame.later` (OnBytes/Iop/Req.lean).
  `base1At N links ps m`: the table of joints' own number `N.msgsAt` at the place of that sending.
  `sentData1At shape N links ps built`: THE DATA AS A TERM OFF THE PUBLIC PARAMETERS.
  `sent1More`: THE ROWS: MADE at piece 4 + o of the segment (the second sending), ASKED AND DROPPED
    at 6 + o; o: the shift of the segment's sort. Between them stands one sub-protocol, at 5 + o.
  `pubSent1`, `fillSent1`: the layer's half with code; the layer. `fillSent1_pub`, `_more`, `_at`
    (by the definition); `fillSent1_else`: what it leaves.
  `sent1Fit_small`, `sent1Fit_full`: the table's test `pubFit` at this filling alone, at two written
    lists of segments, is true; `sent1Fit_negative`: with the maker's row struck it is false.
WHAT A TRUE TEST GIVES: FillSent.lean's `five_of_sentIs`, `whereIs_of_sentIs`, at the longer data.

OBJECT: no sub-protocol's text: the reader `S.link?` of the verifier's state. USER: the
sub-protocol at piece 6 + o, where the table asks for the item. LETTERS: the data.

Limits. THE TEST HAS NOT RUN AT THE LONGER LIST, but for one print: behind the second sending of
segment 0 of one honest small proof own is 0, 1, 2, 5: what `secondNos` gives at base1 = 5 and one
message of moment 1. IF "frame.sentIs" HOLDS IN FRONT, THE SECOND SENDING MAKES THE ITEM AT ITS OWN
NUMBERS (Johnson/Desc/K1/Law/SentIsAtReads.lean). IT IS NOT SHOWN THAT THE SUB-PROTOCOL AT 5 + o
KEEPS IT. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED BY THIS. Nothing on soundness.
-/
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillSent
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)

/-- The data with more m appended to own m. -/
def laterOf (d : SentData) (more : Nat → Array Nat) : SentData :=
  { d with own := fun m => d.own m ++ more m }

/-- The numbers of the second sending's messages. base1 m: how many oracle messages are sent in
front of it. BY A READING. -/
def secondNos (shape : Params.ReqShape) (base1 : Nat → Nat) (m : Nat) : Array Nat :=
  (Array.range (((shape.link[m]?.map (·.messages)).getD []).filter fun x =>
    x.moment == 1).length).map (· + base1 m)

/-- How many oracle messages are sent in front of segment m's second sending. -/
def base1At (N : Numbers) (links : List ModelPart) (ps : List Place) (m : Nat) : Nat :=
  N.msgsAt (ps.find? fun p => p.link == some m && p.piece == 4 + ((links[m]?).map shift).getD 0)

/-- **The data as a term off the public parameters.** -/
def sentData1At (shape : Params.ReqShape) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (built : Array Stages.LinkH) : SentData :=
  laterOf (sentDataAt shape N links ps built) (secondNos shape (base1At N links ps))

/-! ## The rows -/

def sent1Name (m : Nat) : MoreName := (some m, "frame.sentIs1")

/-- **The door's filling.** -/
def sent1More : More where
  rows links p :=
    match p.link with
    | some m =>
      match links[m]? with
      | none => {}
      | some sub =>
        let o := shift sub
        if p.piece == 4 + o then { makes := [sent1Name m] }
        else if p.piece == 6 + o then { asks := [sent1Name m], drops := [sent1Name m] }
        else {}
    | none => {}

/-! ## The layer -/

/-- Is the item this layer's? -/
def sent1Item : Pub → Bool
  | .more (some _) name => name == "frame.sentIs1"
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubSent1 {P : Type} (d : SentData) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .more (some m) name =>
      if name == "frame.sentIs1" then sentIsB d m a.2 else f (.more (some m) name) a
    | q => f q a

/-- **The layer.** -/
def fillSent1 {P W : Type} (d : SentData) (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubSent1 d Mg.pub, more := Mg.more.merge sent1More }

section
variable {P W : Type} (d : SentData) (Mg : Meaning P W)

theorem fillSent1_pub : (fillSent1 d Mg).pub = pubSent1 d Mg.pub := rfl

theorem fillSent1_more : (fillSent1 d Mg).more = Mg.more.merge sent1More := rfl

theorem fillSent1_at (m : Nat) (a : P × S) :
    (fillSent1 d Mg).pub (moreItem (sent1Name m)) a = sentIsB d m a.2 := rfl

/-- Every other item is handed on. -/
theorem fillSent1_else (q : Pub) (h : sent1Item q = false) (a : P × S) :
    (fillSent1 d Mg).pub q a = Mg.pub q a := by
  show pubSent1 d Mg.pub q a = Mg.pub q a
  unfold pubSent1
  split
  · rename_i m name
    simp only [sent1Item] at h
    rw [if_neg (by simp [h])]
  · rfl

end

/-! ## The table's test at this filling alone -/

set_option maxRecDepth 100000 in
theorem sent1Fit_small : pubFit sent1More segsSmall (flatPlacesOf segsSmall true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem sent1Fit_full : pubFit sent1More segsFull (flatPlacesOf segsFull true) = true := by
  decide +kernel

/-- The filling with the maker's row struck. -/
def sent1MoreNoMaker : More where
  rows links p := { sent1More.rows links p with makes := [] }

set_option maxRecDepth 100000 in
/-- **A negative test**: without a maker the table's test is false. -/
theorem sent1Fit_negative :
    pubFit sent1MoreNoMaker segsSmall (flatPlacesOf segsSmall true) = false := by
  decide +kernel

end VerifiableInference.Desc.First.FillSent

#print axioms VerifiableInference.Desc.First.FillSent.fillSent1_else
#print axioms VerifiableInference.Desc.First.FillSent.sent1Fit_small
#print axioms VerifiableInference.Desc.First.FillSent.sent1Fit_full
#print axioms VerifiableInference.Desc.First.FillSent.sent1Fit_negative
