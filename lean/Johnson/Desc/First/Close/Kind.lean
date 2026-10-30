-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Kind.lean: the closing of a link (kind K10) as a kind of block
(Johnson/Desc/Block.lean): from the numbers of a place to the block there. Definitions alone.

  `Par`      the numbers of a place: no entry and no declared round.
  `entries`  ROUNDS: the 2 + k entries, as a function of these numbers.
  `Rec`      the part of the carried record that the kind reads and writes.
  `kind`     the block: its rounds; what it opens: nothing; the tests on the plan alone; its
             decision: `closeFrame` (Johnson/Desc/First/Close/Closing.lean) at `entries`.
A wider record takes it by `Block.lift`.

What the general step asks in front of the decision (`Block.step`, under the name "the rounds": each
round shows just the items that its entry cuts, and drew what its entry says) the decision asks
again: K10.items, K10.draws, K10.one, and the rounds' side of K10.stretch.
What the decision asks of an entry (K10.name, K10.nonzero, K10.entry, K10.norows, and the entries'
side of K10.stretch) holds of `entries` at every Par: these guards bite only at a caller that hands
closeFrame other entries.
CLAIMS: none. BEHIND THE BATCHING: none. SENDS: as Closing.lean's head says (lean/GAPS.md).

-/
import Johnson.Desc.Block
import Johnson.Desc.First.Close.Closing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes

/-- The numbers of a place of the kind. -/
structure Par where
  /-- the link, from 0 -/
  link : Nat
  /-- the block's number inside the link -/
  piece : Nat
  /-- the row variables of the link's group: main rows; mask rows -/
  k : Nat
  h : Nat
  /-- how many rows "BAT" batches -/
  rows : Nat
  /-- the bits of proof of work: of "BAT" and "FOLD epsilon"; of a "FOLD round" -/
  workField : Nat
  workClose : Nat
  /-- the trees that hold the group's messages and the fold's mask: their numbers in the chain's
  order of sending: all must have been sent before "BAT"'s draw -/
  sent : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- ROUNDS. An element has 24 bytes. -/
def entries (P : Par) : List Fmt.Entry :=
  { name := "BAT", work := P.workField, drawE := 1, rows := P.rows } ::
  { name := "FOLD epsilon", work := P.workField, msg := 24, drawE := 1 } ::
  List.replicate P.k { name := "FOLD round", work := P.workClose, msg := 48, drawE := 1 }

/-- What the kind reads and writes of the carried record: the rows owed; the walk's frame; the
statement. -/
structure Rec where
  owed : Option Nat
  frame : ReqFrame
  st : Statement

/-- **The kind.** -/
def kind {Cl : Type} : Kind Par Rec Cl := fun P =>
  { name := s!"the closing of link {P.link}"
    place := { chain := 1, link := some P.link, piece := P.piece, kind := .K10 }
    planOk := decide (1 ≤ P.k) && decide (P.h ≤ P.k)
    rounds := (entries P).map fun e => { entry := e }
    oracles := (entries P).map fun _ => []
    before := P.sent.map fun n => (1, n)
    decide := fun s rs _ =>
      (closeFrame s.owed s.frame s.st (entries P) rs).map fun x => ⟨none, x.1, x.2⟩
    claims := []
    after := [] }

end VerifiableInference.Desc.First.Close
