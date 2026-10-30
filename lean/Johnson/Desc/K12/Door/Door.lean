-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/Door.lean: **THE PROXIMITY TEST's FILLING OF THE DOOR** of the table of joints
(`First.More`, Johnson/Desc/First/Borders.lean), in this form:
three named public items, no turn of the table.
  "K12.bookInOrder" · "K12.seatsCarried": seg := none; OPEN AT THE CHAIN's START; dropped by nobody;
    asked by the proximity test's row at the finish.


  "K12.bookFits": seg := none; OPEN AT THE CHAIN's START; dropped by nobody;
    asked by no row of the first chain's table: its asker is the last chain's door.
  `k12More`: the rows. `k12Pub ft L`: the three Bools by name
    (Johnson/Desc/K12/Door/DoorBools.lean); none at any
    other name: whoever merges fillings lays it in front of its own `Meaning.pub`.
Behind the last segment the table's rows go by the block's kind (`backRow`): so do these: at the
first chain's places (chain 1) outside the links alone; at every other place the row is empty.
No theorem.

-/
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open VerifiableInference.Desc.First (S More MoreRow MoreName Pub)

def nBook : MoreName := (none, "K12.bookInOrder")
def nSeats : MoreName := (none, "K12.seatsCarried")
def nFits : MoreName := (none, "K12.bookFits")

/-- **The filling's rows.** -/
def k12More : More where
  rows := fun _ p =>
    if p.chain != 1 || p.link.isSome then {}
    else match p.kind with
      | .K12 => { asks := [nBook, nSeats] }
      | _ => {}
  start := [nBook, nSeats, nFits]

/-- **The filling's Bools**, by name. -/
def k12Pub {P : Type} (ft : Nat) (L : Laid) : Pub → P × S → Option Bool
  | .more none "K12.bookInOrder", a => some (atFirstBook ft a.2)
  | .more none "K12.seatsCarried", a => some (atFirstSeats L a.2)
  | .more none "K12.bookFits", a => some (atFirstFits a.2)
  | _, _ => none

end VerifiableInference.Desc.K12.Door
