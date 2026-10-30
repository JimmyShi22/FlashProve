-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/State.lean: the state that a key file's first chain carries. Definitions only, all
computable; nothing is proved here.

The blocks of a sending, of the batching of the rows on the table and of a proximity test decide on
the statement, the book of trees and the number of roots received (`Desc.Plain.DState`). A key
file's first chain carries these, some numbers that its blocks hand to each other, and a record of
the chain's maker (what its lookups need), which is a type variable here.

Main names.
  PlainState: the statement with the book of trees and the roots received.
  ChainState: the first chain's state. `chainStart`: its first value.
  ChainState.noneWaits, ChainState.debt: the count of rows that the round before has announced.
  rowOfLinClaim, firstOf: what the later chains take of the first chain's last state.

Limits. Nothing here says which block writes which field: that is the blocks' text
(Johnson/Desc/Key/One.lean, Johnson/Desc/Key/Link.lean). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import Johnson.Desc.First.Base.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params

/-- The statement with the book of trees and the roots received. -/
abbrev PlainState : Type := _root_.Desc.Plain.DState Unit

/-- **The first chain's state.** -/
structure ChainState (β : Type) where
  /-- the record of the chain's maker -/
  base : β
  /-- the statement, the book of trees, the roots received -/
  d : PlainState
  /-- the rows that the entry of the round before counts, until they have been compared -/
  owed : Option Nat := none
  /-- the numbers of the oracle messages of the last sending -/
  sent : Array Nat := #[]
  /-- the number of the index-mask message (`noId`, the verifier program's "no number", until it is
  sent) -/
  idx : Nat := noId
  /-- the number of the group of the proximity test on the ranges -/
  grp : Nat := noId
  /-- the number of the mask of that test's first fold, where masks ride with a sending -/
  rider : Option Nat := none
  /-- the lookups are through: the chain has come to the batching of the rows on the table -/
  atEnd : Bool := false
  /-- the rows on the table -/
  pile : List TensorRow := []
  /-- what the sending of W announces -/
  msgW : Array OracleNotice := #[]
  /-- the numbers of the oracle messages sent with W -/
  ids : Array Nat := #[]
  /-- the linear claim's first part; behind the sending of W with the own group -/
  lin : Option LinFirst := none

variable {β : Type}

/-- The first state: the codes; no oracle message, no group, no tree (as the verifier program's
`Key.startOf`). -/
def chainStart (codes : Codes) (b : β) : ChainState β :=
  { base := b
    d := { st := { codes := codes }, book := { trees := #[], place := #[] }, roots := 0,
           opened := [], loc := () } }

/-- No count of rows waits. A count of 0 rows is none. -/
def ChainState.noneWaits (s : ChainState β) : Bool := s.owed.all (· == 0)

/-- The count of rows that waits, as a block of a sending takes it. -/
def ChainState.debt (s : ChainState β) : Option Nat := s.owed.filter (· != 0)

/-- A claim of the test on the table, read back as a row on the table. -/
def rowOfLinClaim (c : LinClaim) : TensorRow :=
  { g := c.g, psi := c.psi, masks := c.masks.toList.map fun m => (⟨m.oracle, m.index⟩, m.coeff)
    target := c.target }

/-- Of the chain's last state: the statement, the book of trees, the roots received and the rows on
the table; behind the batching these are the one row that the claim gives. In front of it: the pile
as it lies: whoever calls this asks that the batching is through (the third chain's start,
Johnson/Desc/Key/Desc.lean, refuses where the state has no claim). -/
def firstOf (s : ChainState β) : Statement × TreeBook × Nat × List TensorRow :=
  (s.d.st, s.d.book, s.d.roots,
    match s.lin with
    | some l => [rowOfLinClaim l.claim]
    | none => s.pile)

end VerifiableInference.Desc.Key
