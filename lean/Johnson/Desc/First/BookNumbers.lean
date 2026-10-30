-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/BookNumbers.lean: THE TABLE's THREE NUMBERS ON THE BOOK, FILLED OFF WHAT THE
CHAIN's BLOCKS TELL. Definitions alone; no Mathlib. A file BESIDE the table of joints: it turns
nothing of it.

Why. `Numbers.treesAt`, `Numbers.msgsAt` and `Numbers.indexNo` (Johnson/Desc/First/Borders.lean) are
letters with defaults that are false of an honest record. Here they are filled, so that the tests
`bookFit` (BookFit.lean) and `fenceFit` (FenceFit.lean) and the promise's clause `bookAt` can be
evaluated at a real chain.

What is said. told: for each block of the chain, in order, the oracles beneath the roots that it
sends. `borderOf`: the number of the border in front of the block at a place; none: the chain's
last border. `msgNoOf`: the number, among the statement's oracle messages, of the message at a
tenant (tree, part): the tenants of the trees in front, and the part. `Numbers.withTold`: the three
numbers so filled; every other field as it was.

Limits. (1) Off THE DESCRIPTION's OWN TELLING: that a plan's numbers are these is another test.
(2) `borderOf` finds a place by its first standing in the list: it is meant for a list in which each
place stands once (a test that runs). (3) That `bookFit` says yes at this filling is shown by
evaluation alone.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.BookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- The number of the border in front of the block at a place; none: the chain's last border. -/
def borderOf (ps : List Place) : Option Place → Nat
  | none => ps.length
  | some p => ps.idxOf p

/-- The number of the message at a tenant (tree, part), counted through the trees told. -/
def msgNoOf (told : List (List Oracle)) (x : Nat × Nat) : Nat :=
  ((told.flatten.take x.1).map fun o => o.tenants.length).sum + x.2

/-- **The three numbers on the book, off what the blocks tell.** -/
def Numbers.withTold (N : Numbers) (ps : List Place) (told : List (List Oracle)) : Numbers :=
  { N with
    treesAt := fun p => treesTold told (borderOf ps p)
    msgsAt := fun p => msgsTold told (borderOf ps p)
    indexNo := msgNoOf told N.index }

end VerifiableInference.Desc.First
