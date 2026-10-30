-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/State.lean: the state that the decision on the shared hash chain carries from
step to step.

A proof file holds three hash chains. The files of this directory define the verifier's decision on
the middle one, the shared chain, as plain functions. Fold.lean tells how the pieces fit, what has
been run, what the decision relies on and what it does not check. This file holds definitions only;
no theorem is stated.

Words used in this directory:
  the program: the Lean verifier program whose sources are under OnBytes/.
  view (Fmt.View): a chain as a decision sees it: the rounds, each with the items that the prover
    sent and the values that were drawn, and the opened columns.
  plan, entry (Fmt.Entry): the plan is the public list of a chain's rounds. Its entry for a round
    gives the round's name and how many values of each kind the round draws.
  planner, sizes: the planner is the part of the program that computes the codes, the shapes and the
    plans from the public files (OnBytes/Params/). The sizes are its results for the test on the
    stored table (Params.LinSized).
  ground function, ground call: one of the seven functions through which the steps change the
    statement and the book of trees (Ground.lean).
  oracle message, group, row, mask, ledger, tree, book of trees: as in OnBytes/Iop/Ground.lean.
  G_u, Omega: the oracle message that holds the folded row of the stored table (FoldedRow,
    OnBytes/Iop/Foldeq.lean), and the oracle message Omega of the test on the table (LinShape.omega,
    OnBytes/Params/Items.lean).

The decision is a fold of pure steps. A step gets the parameters, the state and its own rounds, and
returns the next state or refuses. Nothing passes from one step to the next except the fields of
DState. The state is coarse: two of its fields are the program's records Statement and TreeBook,
carried whole, and they hold more than any one step or test reads.

Main names:
  Par: what the steps read and never write: the shape of the test on the stored table, the table's
    key, the number of answers to a sample, the number of the chain's first own tree, and the plan's
    entries for the chain's rounds. The key does not follow from the plan: it holds the table's
    record and the seeds that belong to the table's name.
  Loc: the values that the shared chain's steps name as they go: the shared point; the two groups'
    numbers; for each of the two sendings the messages' numbers, the elements drawn and the answers
    received; where the folded row is; the number of the mask message that was sent with it; the
    positions; the numbers of Omega and of the split's mask message; the second point; the share.
  DState L: the carried state: the statement and the book of trees, the number of roots received so
    far, the view's opened columns that have not been read yet, and the chain's own named values, of
    type L (here Loc). Of the program's context it leaves out the bookkeeping of rounds, the notes
    and the mark of a failed test: a step gets its rounds as an argument and refuses at once.
  Loc.first, start: the named values and the state before round 0.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.
What this comment says of the code rests on reading and is not machine-checked.


-/
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Shared
open OnBytes OnBytes.Params

/-- The parameters: what the steps read and never write. -/
structure Par where
  /-- the shape of the test on the stored table -/
  S : LinShape
  /-- the table's key -/
  key : TableKey
  /-- the number of answers to each out-of-domain sample -/
  samples : Nat
  /-- the number of the first tree that this chain sends -/
  firstTree : Nat
  /-- the plan's entries for the chain's rounds, in order -/
  entries : List Fmt.Entry

/-- The values that the shared chain's steps name. Each keeps its value from Loc.first until its
step writes it. -/
structure Loc where
  /-- the shared point (written by step0) -/
  psi : List E
  /-- the number of G_u's group, and of Omega's group (step0) -/
  gU : Nat
  gO : Nat
  /-- the numbers of the oracle messages that were sent together with G_u, G_u first (step1) -/
  idsU : Array Nat
  /-- the elements drawn after that sending, and the answers received, in order (step1) -/
  sdU : List E
  anU : List E
  /-- where the folded row is (step1) -/
  u : FoldedRow
  /-- the mask message of the first fold of the test on G_u's group, if it was sent with G_u (step1)
  -/
  mask : Option Nat
  /-- the positions drawn (step2) -/
  pos : Positions
  /-- the numbers of the oracle messages that were sent together with Omega, Omega first; sdO and
  anO are the elements drawn and the answers received, as for G_u (step3) -/
  idsO : Array Nat
  sdO : List E
  anO : List E
  /-- the number of Omega, and of the split's mask message (step3) -/
  omega : Nat
  split : Nat
  /-- the point on the rows of the matrix (step4) -/
  zeta : List E
  /-- the share that the prover sends at the split (step5) -/
  share : E

/-- The carried state. L is the type of the chain's own named values. -/
structure DState (L : Type) where
  st : Statement
  book : TreeBook
  /-- how many roots have been received so far on this chain -/
  roots : Nat
  /-- the view's opened columns that have not been read yet, in the file's order -/
  opened : List (Nat × Nat × List UInt64)
  loc : L

/-- The named values before round 0. -/
def Loc.first : Loc :=
  { psi := [], gU := noId, gO := noId, idsU := #[], sdU := [], anU := [],
    u := { oracle := noId, lay := {} }, mask := none,
    pos := { logN := 0, draws := #[], all := #[] },
    idsO := #[], sdO := [], anO := [], omega := noId, split := noId, zeta := [], share := zeroE }

/-- The state before round 0: the codes, and no oracle message, group or tree. -/
def start (codes : Codes) (opened : List (Nat × Nat × List UInt64)) : DState Loc :=
  { st := { codes := codes, oracles := #[], groups := #[] }, book := { trees := #[], place := #[] },
    roots := 0, opened := opened, loc := Loc.first }

end Desc.Shared
