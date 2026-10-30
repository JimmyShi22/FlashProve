-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Fill/PubP1.lean: one layer of the filling of the table of joints
(Johnson/Desc/First/Borders.lean): its half with code. Definitions with code, and small theorems. No
Mathlib beneath.

What the layer says, of public items: `hasRow m` alone. It lays no name at the door.

Main names:
  `PubData`: the planner's numbers that the test reads: the committed table's layout; the shape of a
    row on it; a segment's number of claims.
  `pubP1`: the layer's test over whatever says the other items. `p1Item`: which items are its own.
  `pubP1_hasRow`, `pubP1_else`.

Limits. The test has run on no verifier's state by its authors' hand. Nothing on soundness.

-/
import Johnson.Desc.First.Borders
import Johnson.Top.H0.Walk.FrameRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillP1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place KindName)
open Johnson.Desc.First.Walk.Law (hasRow)

/-- The numbers of the plan that the layer's tests read. -/
structure PubData where
  /-- the layout of the table of weights -/
  lay : WsLay
  /-- the shape of a row on that table -/
  lin : Params.LinShape
  /-- a segment's number of claims on the weights -/
  ncl : Nat → Nat

/-- Is the item one of this layer's? -/
def p1Item : Pub → Bool
  | .hasRow _ => true
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubP1 {P : Type} (d : PubData) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .hasRow m => hasRow d.lay (d.ncl m) d.lin a.2
    | q => f q a

section
variable {P : Type} (d : PubData) (f : Pub → P × S → Bool)

theorem pubP1_hasRow (m : Nat) (a : P × S) :
    pubP1 d f (.hasRow m) a = hasRow d.lay (d.ncl m) d.lin a.2 := rfl

/-- Every other item is handed on. -/
theorem pubP1_else (q : Pub) (h : p1Item q = false) (a : P × S) : pubP1 d f q a = f q a := by
  cases q with
  | hasRow m => simp [p1Item] at h
  | _ => rfl

end

end VerifiableInference.Desc.First.FillP1
