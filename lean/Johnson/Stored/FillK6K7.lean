-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Stored/FillK6K7.lean: THE OUTPUT HEAD'S AND THE REPLY'S FILES' LAYER OF THE FILLING OF THE
TABLE OF JOINTS: two public items of the table, each with its test on the record, laid into a
Meaning over whatever is there. No Mathlib. A file beside the table
(Johnson/Desc/First/Borders.lean): it turns nothing of it. In the form of that table's files' own
layer.

Why. Meaning.pub is a letter: what each public item says of the record. It is filled in layers: each
kind's layer lays its own items and hands every other item on.

What is said. THE LAYER'S DATA: h: the head's shape; iU3: the number of the reads' array (the two
letters of the head's seat, Johnson/Stored/HeadSeatAt.lean: seatAt h iU3); mH: the number of the
head's segment.
  tokenHeardB h iU3 s: a token is heard, and it is below the vocabulary's size.
  lookHeadB h iU3 s: where the lookup on the calls is heard, every slot that its last claim names is
      filled in the ledger.
  k6k7Item mH: is the item one of this layer's?
  pubK6K7 h iU3 mH f: THE LAYER'S HALF WITH CODE: tokenSmall; look m AT THE HEAD'S SEGMENT ALONE
      (that item is laid by sort of segment: at every other segment it is handed on). Every other
      item is handed on to f.
  fillK6K7 h iU3 mH Mg: the layer: pub is that half over what was there; every other field as it
      was.
  fillK6K7_pub (by the make), _tokenSmall, _look: what it lays, at every Meaning. fillK6K7_else:
      what it leaves.

Limits. (1) Nothing says here who makes or keeps the two. (2) tokenSmall is laid in the words of the
table ("a token IS heard, and it is below V"): stronger than "the token that was
heard, if any, is below V". (3) A THIRD ITEM THAT WAS BOOKED FOR THIS LAYER, THE DOOR'S
"K6.readersAgree", IS NOT LAID: no law of any kind is known to ask it; in these kinds' own ties it
is in hand through the condition behind the block. (4) Neither Bool has run on a walk. (5) Nothing
on soundness.

-/
import Johnson.Stored.HeadSeatAt
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open VerifiableInference.Desc.First (S Pub Meaning)

/-- A token is heard, and it is below the vocabulary's size. -/
def tokenHeardB (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s : S) : Bool :=
  match Reply.token (seatAt h iU3).toSeat s with
  | some y => Decidable.decide (y < h.V)
  | none => false

/-- Where the lookup on the calls is heard: every slot that its last claim names is filled in the
ledger. -/
def lookHeadB (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s : S) : Bool :=
  match s.lookHeard? with
  | some gk => gk.cEnd.slots.toList.all fun x =>
      ((seatAt h iU3).ledger s).gotF.getD x.1 false
  | none => true

/-- Is the item one of this layer's? -/
def k6k7Item (mH : Nat) : Pub → Bool
  | .tokenSmall => true
  | .look m => m == mH
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubK6K7 {P : Type} (h : OnBytes.Model.Head.Shape) (iU3 mH : Nat) (f : Pub → P × S → Bool) :
    Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .tokenSmall => tokenHeardB h iU3 a.2
    | .look m => if m == mH then lookHeadB h iU3 a.2 else f (.look m) a
    | q => f q a

/-- **The layer.** -/
def fillK6K7 {P Wt : Type} (h : OnBytes.Model.Head.Shape) (iU3 mH : Nat) (Mg : Meaning P Wt) :
    Meaning P Wt :=
  { Mg with pub := pubK6K7 h iU3 mH Mg.pub }

section
variable {P Wt : Type} (h : OnBytes.Model.Head.Shape) (iU3 mH : Nat) (Mg : Meaning P Wt)

/-- The layer's pub is its half with code, by the make. -/
theorem fillK6K7_pub : (fillK6K7 h iU3 mH Mg).pub = pubK6K7 h iU3 mH Mg.pub := rfl

theorem fillK6K7_tokenSmall (a : P × S) :
    (fillK6K7 h iU3 mH Mg).pub .tokenSmall a = tokenHeardB h iU3 a.2 := rfl

theorem fillK6K7_look (a : P × S) :
    (fillK6K7 h iU3 mH Mg).pub (.look mH) a = lookHeadB h iU3 a.2 := by
  show (if mH == mH then lookHeadB h iU3 a.2 else Mg.pub (.look mH) a) = _
  simp

/-- Every other item is handed on. -/
theorem fillK6K7_else (q : Pub) (hq : k6k7Item mH q = false) (a : P × S) :
    (fillK6K7 h iU3 mH Mg).pub q a = Mg.pub q a := by
  cases q with
  | tokenSmall => simp [k6k7Item] at hq
  | look m =>
    show (if m == mH then lookHeadB h iU3 a.2 else Mg.pub (.look m) a) = _
    have h' : (m == mH) = false := hq
    rw [h']
    rfl
  | _ => rfl

end

end VerifiableInference.Desc.Kinds.Head

#print axioms VerifiableInference.Desc.Kinds.Head.fillK6K7_look
#print axioms VerifiableInference.Desc.Kinds.Head.fillK6K7_else
