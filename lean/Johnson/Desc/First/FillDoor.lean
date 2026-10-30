-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/FillDoor.lean: THE DOOR'S LAYER OF THE FIRST TABLE'S FILLING: one named public
item, "K13.doorFirst", with its test on the record, laid into a `Meaning` over whatever is there;
after the form of the table's own layer (Johnson/Desc/First/FillKeeper.lean). Small. It
turns none of the table's own rows.

Main names (namespace `VerifiableInference.Desc.First`).
  `nDoor` := (none, "K13.doorFirst"). `doorMore`: the filling's rows: MADE behind the links by the
    block at a place of kind K1 (W's sending with the own group behind it: where the table's own
    `evalLaid` is made); asked and dropped by no row; not open at the start.
  `doorItem`; **`pubDoor f`**: THE HALF WITH CODE: the named item is `Last.doorFirstB`
    (Johnson/Desc/Last/DoorTexts.lean); every other item is handed on. **`fillDoor Mg`**: `pub` is
    that half over what was there; `more` is merged with `doorMore`; every other field as it was.
    `fillDoor_pub`, `_more`, `_door` (by the make); `fillDoor_else`.

Limits. (1) WHO EARNS IT: the block at that place owes: its yes gives `doorFirstB` behind; the
blocks behind it (the chain's end) owe that they keep it: NOT TYPED. Three of the six are invariants
of the whole chain (tidy; the book fits; the weights): the earner needs them in front: tidy rides in
`inOrder` at another file's layer; the weights as "K13.weightsOk"
(Johnson/Desc/First/FillWeights.lean); that the book fits rides nowhere yet. (2) The table's test on
the rows (`pubFit`) has not been run at the merged filling: if more than one place behind the links
has the kind K1 it rings. (3) A clash of names is silent in `pub`. (4) `pubP` is left as it was. (5)
That the item is open at the last border is a premise wherever it is spent. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.Last.DoorTexts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc.Last (doorFirstB)

/-- The item's name. -/
def nDoor : MoreName := (none, "K13.doorFirst")

/-- **The filling's rows**: made behind the links by the block at W's sending's place (the place
at which the table's own `evalLaid` is made: there the own group is laid); asked and dropped by no
row of the first chain. -/
def doorMore : More where
  rows := fun _ p =>
    if p.chain != 1 || p.link.isSome then {}
    else match p.kind with
      | .K1 => { makes := [nDoor] }
      | _ => {}
  start := []

/-- Is the item this layer's? -/
def doorItem : Pub → Bool
  | .more none name => name == "K13.doorFirst"
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubDoor {P : Type} (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .more none name => if name == "K13.doorFirst" then doorFirstB a.2 else f q a
    | q => f q a

/-- **The door's layer.** -/
def fillDoor {P W : Type} (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubDoor Mg.pub, more := Mg.more.merge doorMore }

section
variable {P W : Type} (Mg : Meaning P W)

theorem fillDoor_pub : (fillDoor Mg).pub = pubDoor Mg.pub := rfl

theorem fillDoor_more : (fillDoor Mg).more = Mg.more.merge doorMore := rfl

theorem fillDoor_door (a : P × S) : (fillDoor Mg).pub (moreItem nDoor) a = doorFirstB a.2 := rfl

/-- Every other item is handed on. -/
theorem fillDoor_else (q : Pub) (h : doorItem q = false) (a : P × S) :
    (fillDoor Mg).pub q a = Mg.pub q a := by
  show pubDoor Mg.pub q a = Mg.pub q a
  unfold pubDoor
  split
  · rename_i name
    simp only [doorItem] at h
    rw [if_neg (by simp [h])]
  · rfl

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.fillDoor_pub
#print axioms VerifiableInference.Desc.First.fillDoor_more
#print axioms VerifiableInference.Desc.First.fillDoor_door
#print axioms VerifiableInference.Desc.First.fillDoor_else
