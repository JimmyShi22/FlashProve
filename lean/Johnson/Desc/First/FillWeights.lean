-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/FillWeights.lean: THE WEIGHTS' LAYER OF THE FIRST TABLE'S FILLING: one named
public item, "K13.weightsOk", with its test on the record, laid into a `Meaning` over whatever is
there; after the form of the layer of Johnson/Desc/First/FillKeeper.lean. Small.
It turns nothing of the table of joints.

Why. The weights' "ok" comes through the door (`Pub.more`, `More`:
Johnson/Desc/First/Borders.lean) as an invariant: open at the chain's start, asked by no row of the
first chain, dropped by nobody: so it stands at the chain's last border, and that border's promise
rides to the last chain.

Main names (namespace `VerifiableInference.Desc.First`).
  `nWeights` := (none, "K13.weightsOk"). `weightsMore`: the filling's rows: every row empty; start
    := [`nWeights`].
  `weightsItem`: is the item this layer's? **`pubWeights f`**: THE LAYER'S HALF WITH CODE: the named
    item is `weightsB` (Johnson/Desc/First/Pend/WeightsB.lean); every other item is handed on to the
    function that it is given.
  **`fillWeights Mg`**: the layer: `pub` is that half over what was there; `more` is what was there
    merged with `weightsMore`; every other field as it was. `fillWeights_pub`, `fillWeights_more`
    (by the make); `fillWeights_weights`: what it lays, at every `Meaning`; `fillWeights_else`: what
    it leaves. **`fillWeights_start`**: at every first record (`IsStart`) the item holds: in the
    shape in which `onAt_start` asks it.

Limits. (1) Nothing says here who keeps the item: every block of the first chain owes that its yes
keeps `weightsB` (two write the rows' weights: the step that lays a pending row; K13's batching;
every other must leave `S.rows`). What lies of that: Johnson/Desc/Last/ShapeWeights.lean. (2) The
item is true for nothing where no row lies. (3) A CLASH OF NAMES IS SILENT: `pubWeights` takes the
name over whatever was there, and a later layer with the same name takes it from `weightsB`; a
second filling that lays the name into its own start rings nowhere. (4) "It stands at the last
border" is true of THIS layer's rows: another filling's row may drop the name, and the table's test
on the rows lets that by; that the item is in the last open set at the merged filling is typed
nowhere. (5) `pubP` is left as it was: with the item open, `Mg.pubP` at the item is asked at every
border and at the start; nothing here says that it holds. (6) The layer turns none of the table's
own rows; it does lengthen every border's open set by one. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.BordersStart
import Johnson.Desc.First.Pend.WeightsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- The item's name. -/
def nWeights : MoreName := (none, "K13.weightsOk")

/-- **The filling's rows**: no row asks, makes or drops the item; it is open at the chain's
start. -/
def weightsMore : More where
  rows := fun _ _ => {}
  start := [nWeights]

/-- Is the item this layer's? -/
def weightsItem : Pub → Bool
  | .more none name => name == "K13.weightsOk"
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubWeights {P : Type} (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .more none name => if name == "K13.weightsOk" then weightsB a.2 else f q a
    | q => f q a

/-- **The weights' layer.** -/
def fillWeights {P W : Type} (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubWeights Mg.pub, more := Mg.more.merge weightsMore }

section
variable {P W : Type} (Mg : Meaning P W)

/-- The layer's `pub` is its half with code, by the make. -/
theorem fillWeights_pub : (fillWeights Mg).pub = pubWeights Mg.pub := rfl

theorem fillWeights_more : (fillWeights Mg).more = Mg.more.merge weightsMore := rfl

theorem fillWeights_weights (a : P × S) :
    (fillWeights Mg).pub (moreItem nWeights) a = weightsB a.2 := rfl

/-- Every other item is handed on. -/
theorem fillWeights_else (q : Pub) (h : weightsItem q = false) (a : P × S) :
    (fillWeights Mg).pub q a = Mg.pub q a := by
  show pubWeights Mg.pub q a = Mg.pub q a
  unfold pubWeights
  split
  · rename_i name
    simp only [weightsItem] at h
    rw [if_neg (by simp [h])]
  · rfl

/-- **At a first record the item holds**: what the promise at the first border
(`onAt_start`, Johnson/Desc/First/BordersStart.lean) asks of an item that is open at the start. -/
theorem fillWeights_start {codes : OnBytes.Codes} {req : Array UInt32} (a : P × S)
    (h : IsStart codes req a.2) : (fillWeights Mg).pub (moreItem nWeights) a = true := by
  show weightsB a.2 = true
  rcases h with ⟨c, hs⟩ | hs <;> rw [hs] <;> rfl

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.fillWeights_pub
#print axioms VerifiableInference.Desc.First.fillWeights_more
#print axioms VerifiableInference.Desc.First.fillWeights_weights
#print axioms VerifiableInference.Desc.First.fillWeights_else
#print axioms VerifiableInference.Desc.First.fillWeights_start
