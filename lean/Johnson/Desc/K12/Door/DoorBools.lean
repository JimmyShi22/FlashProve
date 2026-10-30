-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/DoorBools.lean: **TWO BOOLS ON THE PUBLIC RECORD THAT THE PROXIMITY TEST's LAW
AT THE FIRST CHAIN's FINISH FINDS LACKING IN THE PROMISE, AND A THIRD FOR THE LAST CHAIN's DOOR**,
for the door of the table of joints (`Pub.more`, Johnson/Desc/First/Borders.lean).
Definitions with code; no theorem. WRITTEN OVER READERS (the book; the count of
roots): so that one text can be filled at the first chain's record and at the shared chain's.
  `laidOf codes sends`: THE PLAN's SIDE: for a chain's sendings in the order of sending: the list of
    (tree, part), one for each oracle message in the order of their numbers, and the list of the
    trees' shapes: by the verifier's own layout (`layTrees`), the trees counted on from sending to
    sending. Nothing where a sending cannot be laid.
  `bookInOrderB ft B roots` ("K12.bookInOrder"): the record counts as many roots as the book has
    trees, and the tree at the place z bears the number ft + z. TRUE OF THE EMPTY BOOK at 0 roots.
  `seatsCarriedB L B` ("K12.seatsCarried"): OF WHAT THE RECORD HOLDS SO FAR: the book's places are a
    prefix of the plan's list of (tree, part), and the shapes of the book's trees are a prefix of
    the plan's list of shapes. TRUE OF THE EMPTY BOOK.
  `atFirst…`: the two at the first chain's state.
  `atFirstFits` ("K12.bookFits"): `bookFitsB`
    (Johnson/Desc/Sound/BookTests.lean) at the first chain's book: every place names a tree that is
    there, and that tree's part at that number is the message. TRUE OF THE EMPTY BOOK. It has not
    run on the table's walk.


The two have run on the table's honest walk, at every border, both stored sizes (evaluated, not
proved; on other versions of this text, from which by report no sign of the two differs).

-/
import Johnson.Desc.First.State
import Johnson.G.Sends
import Johnson.Desc.Sound.BookTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (S)

/-- The plan's side: the messages' (tree, part), and the trees' shapes. -/
structure Laid where
  places : List (Nat × Nat) := []
  shapes : List TreeShape := []
  deriving Repr

/-- A chain's sendings, laid one behind the other. -/
def laidOf (codes : Codes) : List (List OracleNotice) → Option Laid
  | [] => some {}
  | sent :: rest =>
    (layTrees codes sent.toArray).bind fun L =>
      (laidOf codes rest).map fun R =>
        { places := ((List.range sent.length).map fun i => (L.tree.getD i 0, L.part.getD i 0)) ++
            R.places.map fun x => (L.shapes.size + x.1, x.2)
          shapes := L.shapes.toList ++ R.shapes }

/-- The planner's list for a chain, in the order of the sendings' entries. -/
def laidOfChain (c : Johnson.G.ChainSends) : Option Laid :=
  laidOf c.codes ((c.sends.mergeSort fun a b => a.entry ≤ b.entry).map (·.sent))

/-- "K12.bookInOrder". -/
def bookInOrderB (ft : Nat) (B : TreeBook) (roots : Nat) : Bool :=
  roots == B.trees.size &&
    (List.range B.trees.size).all fun z => (B.trees[z]?).all fun T => T.number == ft + z

/-- "K12.seatsCarried". -/
def seatsCarriedB (L : Laid) (B : TreeBook) : Bool :=
  B.place.toList == L.places.take B.place.size && decide (B.place.size ≤ L.places.length) &&
    B.trees.toList.map (·.shape) == L.shapes.take B.trees.size &&
    decide (B.trees.size ≤ L.shapes.length)

/-! ## At the first chain's state -/

def atFirstBook (ft : Nat) (s : S) : Bool := bookInOrderB ft s.book s.roots

def atFirstSeats (L : Laid) (s : S) : Bool := seatsCarriedB L s.book

/-- "K12.bookFits". -/
def atFirstFits (s : S) : Bool := Sound.bookFitsB s.book

end VerifiableInference.Desc.K12.Door
