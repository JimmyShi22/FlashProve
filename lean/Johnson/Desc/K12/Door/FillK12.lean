-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/FillK12.lean: **the proximity test's layer of the table's filling**: four
named public items, each with its test on the record, laid into a `Meaning` over whatever is there;
after the form of the table's files' own layer (Johnson/Desc/First/FillKeeper.lean). No Mathlib.
It turns nothing of the table of joints.
  `K12Data`: the layer's data: ft: the number of the chain's first tree; L: the plan's lists (the
    messages' (tree, part); the trees' shapes: Johnson/Desc/K12/Door/DoorBools.lean: `laidOfChain`);
    M: the plan's messages' shapes (Johnson/Desc/K12/Door/MsgShapes.lean: `msgsOfChain`).
  `k12Item`: is the item one of this layer's?
  `pubK12 d f`: the layer's half with code: "K12.bookInOrder", "K12.seatsCarried" are `atFirstBook
    d.ft`, `atFirstSeats d.L` (DoorBools.lean: the texts as they have run on the table's walk);
    "K12.msgShapes" is `atFirstShapes d.M` (MsgShapes.lean: it has not run); "K12.bookFits" is
    `atFirstFits` (DoorBools.lean: it has not run on the table's walk); every other item is handed
    on to the function that it is given.
  `fillK12 d Mg`: the layer: `pub` is that half over what was there; `more` is what was there merged
    with `k12More` (Door.lean: who asks which) and `shapesMore`; every other field as it was.
  `fillK12_pub` | `fillK12_more` (by the make) · `_book` | `_seats` | `_shapes` | `_fits`: what it
    lays, at every `Meaning` · `fillK12_else`: what it leaves.
Limits. (1) d is a letter: nothing ties L or M to a plan here. (2) Nothing says here who makes or
keeps the four. (3) Nothing on soundness.


-/
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open VerifiableInference.Desc.First (S Pub Meaning More)

/-- The layer's data. -/
structure K12Data where
  ft : Nat
  L : Laid
  M : List OnBytes.OracleShape

/-- Is the item one of this layer's? -/
def k12Item : Pub → Bool
  | .more none name =>
    name == "K12.bookInOrder" || name == "K12.seatsCarried" || name == "K12.msgShapes" ||
      name == "K12.bookFits"
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubK12 {P : Type} (d : K12Data) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .more none name =>
      if name == "K12.bookInOrder" then atFirstBook d.ft a.2
      else if name == "K12.seatsCarried" then atFirstSeats d.L a.2
      else if name == "K12.msgShapes" then atFirstShapes d.M a.2
      else if name == "K12.bookFits" then atFirstFits a.2
      else f q a
    | q => f q a

/-- **The proximity test's layer.** -/
def fillK12 {P W : Type} (d : K12Data) (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubK12 d Mg.pub, more := Mg.more.merge (k12More.merge shapesMore) }

section
variable {P W : Type} (d : K12Data) (Mg : Meaning P W)

/-- The layer's `pub` is its half with code, by the make. -/
theorem fillK12_pub : (fillK12 d Mg).pub = pubK12 d Mg.pub := rfl

theorem fillK12_more : (fillK12 d Mg).more = Mg.more.merge (k12More.merge shapesMore) := rfl

theorem fillK12_book (a : P × S) :
    (fillK12 d Mg).pub (First.moreItem nBook) a = atFirstBook d.ft a.2 := rfl

theorem fillK12_seats (a : P × S) :
    (fillK12 d Mg).pub (First.moreItem nSeats) a = atFirstSeats d.L a.2 := rfl

theorem fillK12_shapes (a : P × S) :
    (fillK12 d Mg).pub (First.moreItem nShapes) a = atFirstShapes d.M a.2 := rfl

theorem fillK12_fits (a : P × S) :
    (fillK12 d Mg).pub (First.moreItem nFits) a = atFirstFits a.2 := rfl

/-- Every other item is handed on. -/
theorem fillK12_else (q : Pub) (h : k12Item q = false) (a : P × S) :
    (fillK12 d Mg).pub q a = Mg.pub q a := by
  show pubK12 d Mg.pub q a = Mg.pub q a
  unfold pubK12
  split
  · rename_i name
    simp only [k12Item, Bool.or_eq_false_iff] at h
    rw [if_neg (by simp [h.1.1.1]), if_neg (by simp [h.1.1.2]), if_neg (by simp [h.1.2]),
      if_neg (by simp [h.2])]
  · rfl

end

end VerifiableInference.Desc.K12.Door

#print axioms VerifiableInference.Desc.K12.Door.fillK12_book
#print axioms VerifiableInference.Desc.K12.Door.fillK12_seats
#print axioms VerifiableInference.Desc.K12.Door.fillK12_shapes
#print axioms VerifiableInference.Desc.K12.Door.fillK12_fits
#print axioms VerifiableInference.Desc.K12.Door.fillK12_else
