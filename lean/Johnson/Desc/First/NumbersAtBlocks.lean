-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/NumbersAtBlocks.lean: THE TABLE's NUMBERS, CLOSED OVER THE DESCRIPTION's OWN
BLOCKS. Small; no Mathlib. A file BESIDE the table of joints: it turns nothing of it.

Why. Four fields of `Numbers` are not the plan's seats: `treesAt`, `msgsAt` and `indexNo` (off what
the blocks tell) and `rowsAt` (where each class of rows stands). Each has a term over letters
(`Numbers.withTold`, Johnson/Desc/First/BookNumbers.lean; `Numbers.withRows`,
Johnson/Desc/First/RowsAtPlan.lean). Here the letters are read off a list of blocks: so that, given
the seats' numbers, the request's shape, the segments' sorts and the first chain's blocks, nothing
is left to choose.

What is said. `blockPlaces bs`, `toldOf bs`: each block's place; what each block tells in its own
`Block.oracles`. `possAt bs n m`: the positions that the declared rounds of the switch into group m
draw (the block of the kind K2 at segment m; at no segment: group n); 0 where there is none.
`Numbers.atBlocks N s links bs`: N with the four fields so laid. Four small lemmas (rfl) say which
term each field is.

Limits. (1) That the blocks' places are the table's own list is a test beside
(`blockPlaces bs == flatPlaces ...`). (2) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.BookNumbers
import Johnson.Desc.First.RowsAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

section
variable {St Cl : Type}

/-- Each block's place. -/
def blockPlaces (bs : List (Block St Cl)) : List Place := bs.map (·.place)

/-- What each block tells. -/
def toldOf (bs : List (Block St Cl)) : List (List Oracle) := bs.map fun b => b.oracles.flatten

/-- The positions that the switch into group m draws. n: the number of segments. -/
def possAt (bs : List (Block St Cl)) (n m : Nat) : Nat :=
  ((bs.find? fun b => b.place.kind == .K2 && b.place.link.getD n == m).map possOf).getD 0

/-- **The numbers, closed over the blocks.** -/
def Numbers.atBlocks (N : Numbers) (s : Params.ReqShape) (links : List ModelPart)
    (bs : List (Block St Cl)) : Numbers :=
  (N.withRows s (possAt bs links.length) links.length).withTold (blockPlaces bs) (toldOf bs)

variable (N : Numbers) (s : Params.ReqShape) (links : List ModelPart) (bs : List (Block St Cl))

theorem atBlocks_rowsAt : (N.atBlocks s links bs).rowsAt =
    rowsAtPlan s (possAt bs links.length) N links.length := rfl

theorem atBlocks_treesAt (p : Option Place) : (N.atBlocks s links bs).treesAt p =
    treesTold (toldOf bs) (borderOf (blockPlaces bs) p) := rfl

theorem atBlocks_msgsAt (p : Option Place) : (N.atBlocks s links bs).msgsAt p =
    msgsTold (toldOf bs) (borderOf (blockPlaces bs) p) := rfl

theorem atBlocks_seats : (N.atBlocks s links bs).sent = N.sent ∧
    (N.atBlocks s links bs).keptOf = N.keptOf ∧ (N.atBlocks s links bs).groupAt = N.groupAt ∧
    (N.atBlocks s links bs).index = N.index ∧ (N.atBlocks s links bs).w = N.w :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.atBlocks_seats
