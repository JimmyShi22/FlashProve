-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3RoundsNames.lean: THE LOT OF THE KIND "LOOKUP": THE WRITTEN NAMES OF THE
FIFTY PLACES IN THE TABLE OF LISTS (`Johnson.AtFull.Rounds.listAt`,
Johnson/AtFull/Rounds/ListAt.lean), AND THAT A SORT's PLACES BEAR ONE LIST. Definitions and closed
facts by the kernel, all light.
  `spotW i d`: the name of the written cut's row at the lookup's place: "G3:2", "A3:7", "H:3".
  `repW s d`: one name for each of the eight sorts.
  `spot_in_table`: at all fifty places the row of `cutFirstFull` bears that name.
    `spot_in_table_control`: with calls and digits exchanged: at none.
  `lists_same`: **the table's runs at a place's name are those at its sort's name.** It covers "H:8"
    against "G0:7": three sorts of digits share one list.
Limits. Written values on both sides. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Table
import Johnson.AtFull.Rounds.ListAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots.K3

/-- The name of the written cut's row at the lookup's place. -/
def spotW (i : Nat) (d : Bool) : String :=
  if i == 24 then (if d then "H:8" else "H:3")
  else (if i % 2 == 1 then "A" else "G") ++ toString (i / 2) ++ (if d then ":7" else ":2")

/-- One name for each sort. -/
def repW (s : Nat) (d : Bool) : String :=
  match s with
  | 0 => spotW 0 d
  | 1 => spotW 1 d
  | 3 => spotW 24 d
  | _ => spotW 2 d

def spotB (f : Bool → Bool) (i : Nat) (d : Bool) : Bool :=
  (tableAt i d).any fun row => row.1 == spotW i (f d)

set_option maxRecDepth 1000000 in
theorem spot_in_table :
    ((List.range 25).all fun i => [false, true].all fun d => spotB id i d) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with calls and digits exchanged: at none. -/
theorem spot_in_table_control :
    ((List.range 25).any fun i => [false, true].any fun d => spotB not i d) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem lists_same_full :
    ((List.range 25).all fun i => [false, true].all fun d =>
      Johnson.AtFull.Rounds.runsAt (spotW i d) ==
        Johnson.AtFull.Rounds.runsAt (repW (sortOf i) d)) = true := by
  decide +kernel

/-- **A SORT's PLACES BEAR ONE LIST.** -/
theorem lists_same {i : Nat} (hi : i < 25) (d : Bool) :
    Johnson.AtFull.Rounds.listAt (spotW i d) =
      Johnson.AtFull.Rounds.listAt (repW (sortOf i) d) := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 lists_same_full i (List.mem_range.2 hi)) d
    (by cases d <;> simp)
  unfold Johnson.AtFull.Rounds.listAt
  rw [beq_iff_eq.1 h]

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.spot_in_table
#print axioms Johnson.AtFull.Lots.K3.spot_in_table_control
#print axioms Johnson.AtFull.Lots.K3.lists_same_full
#print axioms Johnson.AtFull.Lots.K3.lists_same
