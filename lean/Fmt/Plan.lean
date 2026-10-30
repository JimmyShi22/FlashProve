-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Plan.lean: the plan of a chain, as data.

In standard terms: a chain is the non-interactive form of one interactive protocol (Fiat-Shamir;
Fmt/Rules4.lean). Its plan is the schedule of its rounds: an entry says, among its eleven numbers,
how many bytes of the prover's message enter the round's hash query, how many bits of proof of work
are asked, and how many field elements, positions and matrix entries are drawn for the verifier's
message. An entry under the name RECORD is no round (`Plan.rounds`, Fmt/Rules4.lean).

Definitions only, but for one theorem (`Kind.ofNat?_num`): no rule on bytes, no hash. No Mathlib.
The format's sections on the first query, on a round's query, on drawing, on trees and on a chain in
a file all speak of one object, the chain's plan. Here it is a value that computes, so that these
sections' files speak of one type.

Main names:
  `Kind`, `Kind.num`, `Kind.ofNat?`.
  `Entry` (its fields, in the page's order: see the record).
  `Plan`: the plan's head (the field; the bytes of a leaf's salt, of a nonce in a file, of a listed
    position; the answers to each out-of-domain sample; whether a sum-check's message leaves out the
    coefficient that the check fixes) and its entries. The head's second word (the hash, always 1)
    and its last (the number of entries) are no fields: they follow.
  `Shape` (its fields: see the record).

Limits: the kind of a round is no field of an entry: by the page it follows from the round's name,
through a list that is part of the format and that the edition at hand does not give (its ruling
for the three toy runs: the head of Fmt/Rules4.lean, under 4, (c)). This file does not
say how a plan is spelled in bytes (Fmt/Rules4.lean). It does not say which plans are plans of a
protocol. It says nothing on bounds on the numbers, but for the brackets in the docstrings of
`count` and `saved`: each rule's file says what it refuses.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules1

namespace Fmt

/-- What the verifier's message of a round consists of. -/
inductive Kind where
  /-- elements of the extension field -/
  | elems
  /-- the element that joins a hiding polynomial to a claim -/
  | join
  /-- the seeds of out-of-domain samples -/
  | seeds
  /-- positions, then an element of the extension field if the entry has one -/
  | positions
  /-- entries of a matrix over -1, 0, 1 -/
  | entries
  /-- a sealing: a digest that later chains build on -/
  | sealed
  /-- nothing -/
  | nothing
  deriving DecidableEq, Repr, Inhabited

/-- the kind's number -/
def Kind.num : Kind → Nat
  | .elems => 1
  | .join => 2
  | .seeds => 3
  | .positions => 4
  | .entries => 5
  | .sealed => 6
  | .nothing => 7

/-- the kind of a number; none for a number that is no kind's -/
def Kind.ofNat? : Nat → Option Kind
  | 1 => some .elems
  | 2 => some .join
  | 3 => some .seeds
  | 4 => some .positions
  | 5 => some .entries
  | 6 => some .sealed
  | 7 => some .nothing
  | _ => none

theorem Kind.ofNat?_num (k : Kind) : Kind.ofNat? k.num = some k := by cases k <;> rfl

/-- An entry of a plan: the round's name and eleven numbers. -/
structure Entry where
  /-- the round's name -/
  name    : String
  /-- how many rounds in a row are like this one (1 in every plan of a chain) -/
  count   : Nat := 1
  /-- the bits of proof of work -/
  work    : Nat := 0
  /-- the bytes of the prover's message that enter the query -/
  msg     : Nat := 0
  /-- the roots among them -/
  roots   : Nat := 0
  /-- the sample answers among them -/
  answers : Nat := 0
  /-- the elements of the extension field that are drawn -/
  drawE   : Nat := 0
  /-- how many of these must not be 0 -/
  drawNZ  : Nat := 0
  /-- the positions that are drawn -/
  poss    : Nat := 0
  /-- positions are drawn below 2 ^ logN -/
  logN    : Nat := 0
  /-- the matrix entries that are drawn -/
  trits   : Nat := 0
  /-- for a round that batches rows: how many -/
  rows    : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The plan of a chain. -/
structure Plan where
  field   : Fld
  /-- the bytes of a leaf's salt -/
  salt    : Nat
  /-- the bytes of a nonce in a file -/
  nonce   : Nat
  /-- the bytes of a listed position (0: none is listed) -/
  posB    : Nat
  /-- the answers to each out-of-domain sample -/
  samples : Nat
  /-- whether a sum-check's message leaves out the coefficient that the check fixes (0 or 1) -/
  saved   : Nat
  entries : List Entry

/-- What an opening's bytes and a leaf's hash call need to know of a tree. -/
structure Shape where
  /-- the depth: main rows have length 2 ^ a (main rows: Fmt/Rules7.lean) -/
  a      : Nat
  /-- a column is a list of W elements of the base field -/
  W      : Nat
  /-- a stored tree (made once, read by many runs), or one that is made in a run -/
  stored : Bool := false
  /-- the tree's number -/
  tree   : Nat
  deriving DecidableEq, Repr, Inhabited

end Fmt
