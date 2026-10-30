-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysWOk.lean: what the layout of the committed matrix of weights leaves in a unit
and in its index groups, as three definitions.

The verifier's layout (WsLay.place, add, build in OnBytes/Model/Weights.lean) gives each index group
of a unit some column bits and leaves the rest of the group's index to the rows. The files that say
what a claim's factors are worth on the columns and on the rows read a few facts on the numbers that
the layout writes into a group and a unit. This file states these facts.

Only definitions.
 - GrpOK: a group's numbers fit each other.
 - Runs: the groups' first column bits follow each other.
 - UnitOK: a unit's groups, its number of column bits and its number of rows.

What is not claimed. That the units of a layout which the verifier builds have these properties is
not shown here: it is the matter of Johnson/Road/FormsKeysWLay.lean. The program does not import
this file.
-/
import Johnson.Road.FormsKeysWm

set_option autoImplicit false

namespace OnBytes.Road

open OnBytes.Model (WsGrp WsUnit clog2)

/-- A group's numbers fit each other. Class 'E': the size is o 2^z; at most z bits go to the
columns; what is left to the rows is the size divided by two to the number of these bits. Class 'A':
all bits of the index go to the columns, or none; one value is left to the rows in the first case if
there is a bit at all, and the whole index otherwise. -/
def GrpOK (g : WsGrp) : Prop :=
  (g.cls = 'E' ∧ g.R = g.o * 2 ^ g.z ∧ g.t ≤ g.z ∧ g.left = g.R / 2 ^ g.t) ∨
    (g.cls = 'A' ∧ (g.t = clog2 g.R ∨ g.t = 0) ∧ g.left = if 0 < g.t then 1 else g.R)

/-- The groups' column bits follow each other from bit cb on: each group's first column bit is the
bit after the last one of the group before. -/
def Runs : List WsGrp → ℕ → Prop
  | [], _ => True
  | g :: r, cb => g.cb0 = cb ∧ Runs r (cb + g.t)

/-- A unit of a layout with lk column bits: each group's numbers fit; the groups' column bits follow
each other from bit 0 on; ncb counts them, and they are at most lk; the unit has one row for each
digit and each tuple of what the groups leave to the rows. -/
structure UnitOK (lk : ℕ) (u : WsUnit) : Prop where
  /-- each group's numbers fit each other -/
  grp : ∀ g ∈ u.g, GrpOK g
  /-- the groups' column bits follow each other from bit 0 on -/
  runs : Runs u.g 0
  /-- the number of column bits that the groups take -/
  ncb : u.ncb = (u.g.map (·.t)).sum
  /-- they are at most lk -/
  le : u.ncb ≤ lk
  /-- the number of the unit's rows -/
  rows : u.rows = u.nlw * (u.g.map (·.left)).prod

end OnBytes.Road
