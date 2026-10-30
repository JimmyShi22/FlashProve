-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkRun.lean: what a run of a block that has taken some rounds of a view leaves.

A block is a step of the program's verifier. A run of it goes from one context to another (`Ctx`:
among other things the channel, the statement and the book of trees). A view is what a decision is
given: the rounds and a list of opened columns (OnBytes/Slice/README.md, "More terms"). A run is
taken apart call by call (OnBytes/Iop/GroundLaws.lean). Some runs inside a proximity test only take
rounds of the view: they leave the statement, the book of trees and the opened columns as they are.
This file has one record for that.

Main definition: `RanRounds`.
-/
import OnBytes.Iop.GroundLaws

set_option autoImplicit false

namespace OnBytes.Slice

/-- What is known after a run from the context c to c' that has only taken k rounds of a view. Two
fields say what c' holds and do not compare it with c: `pending` and `dry`. `rest` is a parameter
that the record does not tie to c: the theorems that give the record suppose that the rounds not yet
closed in c are the k taken and then `rest`, and that c is no dry run (OnBytes/Slice/BlkFold.lean:
`foldRounds_sem`). Nothing is said on the notes of intermediate values or on the channel's record
of the round closed last. -/
structure RanRounds (k : Nat) (rest : List Fmt.RoundView) (c c' : Ctx) : Prop where
  /-- the view's rounds that are not yet closed are `rest` -/
  pending : c'.ch.pending = rest
  /-- c' is no dry run (`Blk.rounds` makes a dry run: every value is zero, and the block only
  describes its rounds) -/
  dry : c'.ch.dry = false
  /-- the statement that the blocks pass along is unchanged -/
  st : c'.st = c.st
  /-- the book of trees is unchanged -/
  book : c'.book = c.book
  /-- the name of the first named test that has failed, if any, is unchanged -/
  failed : c'.failed = c.failed
  /-- the view's opened columns that are not yet read are unchanged -/
  opened : c'.ch.opened = c.ch.opened
  /-- of the plan's entries (`Fmt.Entry`: one for each round not yet closed) the first k are gone -/
  entries : c'.ch.entries = c.ch.entries.drop k
  /-- the number of roots received is unchanged -/
  roots : c'.ch.roots = c.ch.roots
  /-- the number of the first tree that this chain sends is unchanged -/
  firstTree : c'.ch.firstTree = c.ch.firstTree
  /-- the number of answers to a sample is unchanged -/
  samples : c'.ch.samples = c.ch.samples

end OnBytes.Slice
