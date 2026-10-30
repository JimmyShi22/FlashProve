-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/KeptTypes.lean: the types of what a lookup's row of parts may pass
on from move to move, so that its tables need not be made anew at every move. Three definitions of
types and one value; no function on them; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a lookup's two sides are its keys and its table; each
side has a product tree over its leaves (Honest/K3/JobsFast.lean, under "How indices and points
lie").

Why. Honest/K3/JobsFast.lean keeps nothing from one call to the next: every move makes its side's
leaves and tree anew. `keepPart` (Honest/SumKeep.lean; not imported) is a masked sumcheck's part
that passes a kept state on.
Whoever seats a lookup's row in a chain must name the type of the row's own state; this file holds
these types alone, so that little is imported with them.

What is defined.
  `Store`: the tables of one lookup at its shift and its alpha: all levels of both sides' product
    trees, the bits, and the table side's factors. Meant to be made once for each lookup, behind the
    round that samples alpha.
  `Kept`: the kept state of one stage: the tables of its sumcheck with the variables of the rounds
    in front bound, the bits that are still free, how many rounds are bound, the stage's point; at a
    stage without a variable: its values.
  `RowOwn`: a row's own state: a store or none, a stage's kept state or none.
  `rowOwn₀`: its value in front of a row and behind it: none, none.

Imported. OnBytes/Base.lean alone, for the type of the field's elements, `OnBytes.E`.

Users. Honest/K3/JobsKeep.lean and the files on the sorts of stage; Honest/K3/StoreMake.lean;
Honest/K3/RowKeep.lean, the row beside `lookRow` (Honest/K3/Row.lean). Meant also for a filling of
the honest prover that seats that row.

Limits. Types alone: nothing here says what a store or a kept state holds at a run, nor that it is
what Honest/K3/JobsFast.lean makes. No field is tested. Room, reckoned and not measured: all levels
of a tree over 2 ^ 24 leaves are 2 ^ 25 elements of three words each.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)

/-- The tables of one lookup at its shift and its alpha. -/
structure Store where
  /-- part i, then m: the level with m variables of the part's key tree, 2 ^ m entries; at m := the
  part's number of bits: the leaves -/
  keyLvls : Array (Array (Array E))
  /-- l: the table side's level number l, 2 ^ (mu + l) entries; at l := d: the leaves -/
  tabLvls : Array (Array E)
  /-- the bits, by the leaf's number -/
  bitTab : Array E
  /-- alpha - 1 - row, by the leaf's number -/
  facTab : Array E

/-- The kept state of one stage of a lookup's row. -/
structure Kept where
  /-- the bits that are still free, in rising order -/
  free : List Nat
  /-- the stage's tables on the free bits -/
  tabs : List (Array E)
  /-- how many rounds are bound -/
  bound : Nat
  /-- the point of the stage's equality weights -/
  z : Array E
  /-- at a stage without a variable: its values; at the tie's first step also the face's public
  factor at the shift and alpha, which hangs on the run -/
  vals : List E

/-- A row's own state: the lookup's store, or none; the stage's kept state, or none. -/
abbrev RowOwn : Type := Option Store × Option Kept

/-- Its value in front of a row, and behind it. -/
def rowOwn₀ : RowOwn := (none, none)

end ProofFile.Honest.K3
