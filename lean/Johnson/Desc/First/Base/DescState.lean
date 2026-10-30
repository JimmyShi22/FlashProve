-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Base/DescState.lean: the state that a description's decision carries along a hash
chain.

A decision on a chain is a fold of pure steps over the chain's view. A step gets the parameters, the
state and its own rounds, and returns the next state or refuses. Nothing passes from one step to the
next except the fields of DState. The state is coarse: two of its fields are the program's records
Statement and TreeBook (OnBytes/Iop/Ground.lean), carried whole. They hold more than any one step or
test reads, and most of what they hold is the same for every proof at a plan.

This file holds definitions only; no theorem is stated.

Main names:
  GPar: what a function of the file Ground.lean of this directory reads of a chain's parameters: the
    number of answers to a sample and the number of the chain's first own tree. Every chain has
    these two.
  Par (it extends GPar): what the steps of the shared chain read and never write: the shape of the
    test on the stored table, the table's key and the plan's entries for the chain's rounds. The key
    does not follow from the plan: it is made of the table's name and record.
  Loc: the values that the shared chain's steps name as they go: the shared point; the two groups'
    numbers; for each of the two sendings the messages' numbers, the elements drawn and the answers
    received; where the folded row is; the number of the mask message that was sent with it; the
    positions; the numbers of Omega and of the split's mask message; the second point; the share.
  DState L: the state, general in a chain's own named values L (for the shared chain: Loc): the
    statement, the book of trees, the number of roots received so far, the view's opened columns
    that are not yet read, and L. Of the program's context it leaves out the bookkeeping of rounds,
    the notes and the mark of a failed test: a step gets its rounds as an argument and refuses at
    once.
  Loc.first, start: the named values and the state before round 0.

Johnson/Desc/Shared/State.lean holds other records of the same short names, in the namespace
Desc.Shared, without GPar. No theorem ties the two files.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Plain
open OnBytes OnBytes.Params

/-- What a ground function reads of a chain's parameters: general: no chain's own shapes. -/
structure GPar where
  /-- the answers to each out-of-domain sample -/
  samples : Nat
  /-- the number of the first tree that this chain sends -/
  firstTree : Nat

/-- What a step of the shared chain reads and none writes. -/
structure Par extends GPar where
  /-- the shape of the test on the table -/
  S : LinShape
  /-- the table's key -/
  key : TableKey
  /-- the plan's entries of the chain's rounds -/
  entries : List Fmt.Entry

/-- The chain's named values. A value stands at its first form until its step has written it. -/
structure Loc where
  /-- the shared point: written by step 0 -/
  psi : List E
  /-- the group of G_u; the group of Omega: step 0 -/
  gU : Nat
  gO : Nat
  /-- the numbers of the messages that went out with G_u, G_u first: step 1 -/
  idsU : Array Nat
  /-- the elements drawn behind them; the answers received, in order: step 1 -/
  sdU : List E
  anU : List E
  /-- where the folded row is: step 1 -/
  u : FoldedRow
  /-- the mask of the first fold of the test on G_u's group, if it went out with G_u: step 1 -/
  mask : Option Nat
  /-- the positions drawn: step 2 -/
  pos : Positions
  /-- the numbers of the messages that went out with Omega, Omega first: step 3 -/
  idsO : Array Nat
  sdO : List E
  anO : List E
  /-- the number of Omega; of the split's mask message: step 3 -/
  omega : Nat
  split : Nat
  /-- the point on the rows of the matrix: step 4 -/
  zeta : List E
  /-- the share that the prover names at the split: step 5 -/
  share : E

/-- The state that is carried. L: the chain's own named values. -/
structure DState (L : Type) where
  st : Statement
  book : TreeBook
  /-- the roots received so far on this chain -/
  roots : Nat
  /-- the view's opened columns that are not yet read, in the file's order -/
  opened : List (Nat × Nat × List UInt64)
  loc : L

/-- The named values in front of round 0. -/
def Loc.first : Loc :=
  { psi := [], gU := noId, gO := noId, idsU := #[], sdU := [], anU := [],
    u := { oracle := noId, lay := {} }, mask := none,
    pos := { logN := 0, draws := #[], all := #[] },
    idsO := #[], sdO := [], anO := [], omega := noId, split := noId, zeta := [], share := zeroE }

/-- The state in front of round 0: the codes; no message, no group, no tree. -/
def start (codes : Codes) (opened : List (Nat × Nat × List UInt64)) : DState Loc :=
  { st := { codes := codes, oracles := #[], groups := #[] }, book := { trees := #[], place := #[] },
    roots := 0, opened := opened, loc := Loc.first }

end Desc.Plain
