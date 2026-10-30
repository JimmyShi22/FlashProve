-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/DoorIs.lean: **THE DOOR's BOOLS, AS THEY HAVE RUN, ARE THE TREE's OWN TEXTS.**
Johnson/Desc/K12/Door/DoorBools.lean went to the table's walk as a root of its own, with a structure
`Laid` and two
tests of its own. The laws stand over the tree's forms: `bookStepB`
(Johnson/Desc/Sound/BookInOrder.lean) and `Laid` | `seatsPrefixB`
(Johnson/Desc/K12/Coin/BookRides.lean). THE TREE's FORMS STAY. Here: the two pairs are one text.
  `toTree`: the root's `Laid` as the tree's.
  `bookInOrder_is`, `seatsCarried_is`: by unfolding alone.
So what the walk has printed of the root's Bools is printed of the tree's.
  `laidFrom_is`, `laidOf_is`: the two makers of the plan's lists (`Door.laidOf`: the later sendings'
    trees shifted by a map; `Coin.laidOf`: a base handed on) give one list.

-/
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.K12.Coin.BookRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open OnBytes

/-- The root's record as the tree's. -/
def toTree (L : Laid) : Coin.Laid := ⟨L.places, L.shapes⟩

theorem bookInOrder_is (ft : Nat) (B : TreeBook) (roots : Nat) :
    bookInOrderB ft B roots = Sound.bookStepB ft B roots := rfl

theorem seatsCarried_is (L : Laid) (B : TreeBook) :
    seatsCarriedB L B = Coin.seatsPrefixB (toTree L) B := rfl

/-- The root's record with its trees counted from base on. -/
def shifted (base : Nat) (L : Laid) : Coin.Laid :=
  ⟨L.places.map fun x => (base + x.1, x.2), L.shapes⟩

/-- **The two makers give one list**, from any base on. -/
theorem laidFrom_is (codes : Codes) : ∀ (sends : List (List OracleNotice)) (base : Nat),
    Coin.laidFrom codes base (sends.map (·.toArray)) = (laidOf codes sends).map (shifted base)
  | [], base => rfl
  | sent :: rest, base => by
    show ((layTrees codes sent.toArray).bind fun lay =>
        (Coin.laidFrom codes (base + lay.shapes.size) (rest.map (·.toArray))).map fun R =>
          ({ places := Coin.placesOf base sent.toArray.size lay ++ R.places
             shapes := lay.shapes.toList ++ R.shapes } : Coin.Laid)) =
      ((layTrees codes sent.toArray).bind fun L =>
        (laidOf codes rest).map fun R =>
          ({ places := ((List.range sent.length).map fun i =>
                (L.tree.getD i 0, L.part.getD i 0)) ++
                R.places.map fun x => (L.shapes.size + x.1, x.2)
             shapes := L.shapes.toList ++ R.shapes } : Laid)).map (shifted base)
    cases hl : layTrees codes sent.toArray with
    | none => rfl
    | some lay =>
      simp only [Option.bind_some]
      rw [laidFrom_is codes rest (base + lay.shapes.size)]
      cases laidOf codes rest with
      | none => rfl
      | some R =>
        simp only [Option.map_some, shifted, Coin.placesOf, List.map_append, List.map_map,
          List.size_toArray]
        congr 2
        congr 1
        refine List.map_congr_left fun x _ => ?_
        simp [Function.comp, Nat.add_assoc]

theorem laidOf_is (codes : Codes) (sends : List (List OracleNotice)) :
    Coin.laidOf codes (sends.map (·.toArray)) = (laidOf codes sends).map toTree := by
  unfold Coin.laidOf
  rw [laidFrom_is codes sends 0]
  congr 1
  funext L
  simp [shifted, toTree]

end VerifiableInference.Desc.K12.Door

#print axioms VerifiableInference.Desc.K12.Door.laidOf_is
#print axioms VerifiableInference.Desc.K12.Door.bookInOrder_is
#print axioms VerifiableInference.Desc.K12.Door.seatsCarried_is
