-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/FillOwnSits.lean: A LAYER OF THE FIRST TABLE'S FILLING: one named public item,
"K13.ownSits", with its test on the state, laid into a `Meaning` over whatever is there. After the
form of the layer for "K13.ownTwo" (Johnson/Desc/First/FillOwnTwo.lean, which is not
in this library). Small. It turns none of the table's own rows.
THE ITEM IS OPEN FROM THE CHAIN'S START, AND NO ROW MAKES IT.
Why not at the place of kind K1 behind the links: a tie at that block whose row lists the items
that come there (Johnson/Desc/K13/Law/AtTableW.lean) has no member where
another layer's row makes an item more. The test says yes wherever nothing is handed yet, so it can
ride from the start; the block at W's sending earns it as an item that rides.

Main names (namespace `VerifiableInference.Desc.First`).
  `nSits` := (none, "K13.ownSits"). `sitsMore`: OPEN AT THE START; made, asked and dropped by no
    row.
  `sitsItem`; **`pubSits V f`**: THE HALF WITH CODE: the named item is `Last.ownSitsB V`
    (Johnson/Desc/Last/OwnSits.lean); every other item is handed on. **`fillOwnSits V Mg`**: `pub`
    is that half over what was there; `more` is merged with `sitsMore`; every other field as it was.
    `fillOwnSits_pub`, `_more`, `_sits` (by the make); `fillOwnSits_else`.
  **`FillsOwnSits Mg V`**: the one premise on a meaning under a letter: at the named item it says
    `ownSitsB V`. `fillsOwnSits_at`: the layer meets it.

Limits. (1) WHO EARNS IT: every block owes that the test says yes behind its yes. THE BLOCK AT W's
SENDING: `ownSitsB_atM4` (Johnson/ToldDescR/OwnSitsLast.lean), where no split's message is needed,
under `FrontM4` in front and `BehindM4` behind. (2) The table's test on the rows (`pubFit`) has not
been run at the merged filling. (3) A clash of names is silent in `pub`.
(4) `pubP` is left as it was. (5) That the item is open at the last border is a premise wherever it
is spent (payable by `pubSets_last_of_start`, Johnson/Desc/First/BordersKept.lean). Nothing on
soundness.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.Last.OwnSits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc.Last (OwnSeats ownSitsB)

def nSits : MoreName := (none, "K13.ownSits")

/-- **The filling**: open at the chain's start; made, asked and dropped by no row of the first
chain. -/
def sitsMore : More where
  start := [nSits]

def sitsItem : Pub → Bool
  | .more none name => name == "K13.ownSits"
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubSits {P : Type} (V : OwnSeats) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .more none name => if name == "K13.ownSits" then ownSitsB V a.2 else f q a
    | q => f q a

/-- **The layer.** -/
def fillOwnSits {P W : Type} (V : OwnSeats) (Mg : Meaning P W) : Meaning P W :=
  { Mg with pub := pubSits V Mg.pub, more := Mg.more.merge sitsMore }

/-- **The premise on a meaning under a letter.** -/
structure FillsOwnSits {P W : Type} (Mg : Meaning P W) (V : OwnSeats) : Prop where
  sits : ∀ a, Mg.pub (moreItem nSits) a = ownSitsB V a.2

section
variable {P W : Type} (V : OwnSeats) (Mg : Meaning P W)

theorem fillOwnSits_pub : (fillOwnSits V Mg).pub = pubSits V Mg.pub := rfl

theorem fillOwnSits_more : (fillOwnSits V Mg).more = Mg.more.merge sitsMore := rfl

theorem fillOwnSits_sits (a : P × S) : (fillOwnSits V Mg).pub (moreItem nSits) a = ownSitsB V a.2 :=
  rfl

theorem fillsOwnSits_at : FillsOwnSits (fillOwnSits V Mg) V := ⟨fun _ => rfl⟩

/-- Every other item is handed on. -/
theorem fillOwnSits_else (q : Pub) (h : sitsItem q = false) (a : P × S) :
    (fillOwnSits V Mg).pub q a = Mg.pub q a := by
  show pubSits V Mg.pub q a = Mg.pub q a
  unfold pubSits
  split
  · rename_i name
    simp only [sitsItem] at h
    rw [if_neg (by simp [h])]
  · rfl

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.fillOwnSits_sits
#print axioms VerifiableInference.Desc.First.fillsOwnSits_at
#print axioms VerifiableInference.Desc.First.fillOwnSits_else
