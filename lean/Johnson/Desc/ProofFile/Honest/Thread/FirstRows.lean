-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstRows.lean: the first chain's table of joints, read
forward. It gives three parameters of the first chain's `Thread` (Honest/Thread/Thr.lean: `ι`,
`start`, `row`), from the library's own table (Johnson/Desc/First/Borders.lean: `Item`, `start`,
`rowOf`). No table changes: the forward rows are this folder's. Definitions and `#guard` lines;
no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

A row read forward. The library's table gives, for each sub-protocol, the items that it closes
(ins), opens (outs) and reads (ctx). Read forward that is: what holds before it (`asks`: ins and
ctx), what has to be proved after it (`owes`: outs and ctx), and what is open no more (`shuts`:
ins).

  `turn`   the one adjustment: where a forward row owes more than the table's row opens
  `rowAt`, `rows`   the forward row at a place; at a border's number, along a list of places

The one adjustment that changes a list. The sending of the stored table W (no segment, piece 4, kind
K1) owes `wrow` too: the rows on W hold. Read forward it follows there from the one claim on the
weights and from how W is computed, and the second chain's start needs it at this chain's end. The
design's other adjustments change what an item says or who proves it, not a list.

What the lines check, by evaluation, at a list of three segments (layers, attention, head) and at
the full size's 25. The table's own test passes (`readsOpen`). The forward rows pass this folder's
(`fwdFit`: whatever a row asks or shuts is open before it). At every border the forward open set is
the table's own, item for item and in the same order, except for `wrow`. At the chain's end exactly
six items are open.

Limits.
  * Lists alone: nothing is said on what an item says.
  * The full size's list of segments is written out here; it is the definition of `P5J.fullLinks`
    (Johnson/P5J/MeansQ.lean), which this file does not import.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstRows
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item rowOf start openSets readsOpen flatPlaces)

/-- **The one adjustment**: at the sending of W, `wrow` is owed too. -/
def turn (p : Place) (f : FwdRow Item) : FwdRow Item :=
  if p.link.isNone && p.kind == .K1 && p.piece == 4 then { f with owes := f.owes ++ [.wrow] }
  else f

/-- The forward row of the sub-protocol at a place. `links`: the segments' sorts. -/
def rowAt (links : List ModelPart) (p : Place) : FwdRow Item :=
  turn p (FwdRow.of (rowOf links p).ins (rowOf links p).outs (rowOf links p).ctx)

/-- The forward row after border number `b`, along a list of places; an empty row beyond it. -/
def rows (links : List ModelPart) (ps : List Place) (b : Nat) : FwdRow Item :=
  ((ps[b]?).map (rowAt links)).getD {}

/-- All forward open sets along a list of places: one more than there are places. For the tests:
`fwdOpen` computes each anew. -/
def opens (links : List ModelPart) : List Place → List Item → List (List Item)
  | [], O => [O]
  | p :: ps, O => O :: opens links ps (fwdStep O (rowAt links p))

/-! ## At three segments -/

def three : List ModelPart := [.layers, .attention, .head]
def ps₃ : List Place := flatPlaces true three true

#guard readsOpen three ps₃ (start three)
#guard fwdFit (start three) (rows three ps₃) ps₃.length
-- `opens` is `fwdOpen`, border by border
#guard (List.range (ps₃.length + 1)).all fun b =>
  (opens three ps₃ (start three))[b]? == some (fwdOpen (start three) (rows three ps₃) b)
-- the forward open sets are the table's own, except for wrow
#guard (opens three ps₃ (start three)).map (·.filter (· != .wrow)) ==
  openSets three ps₃ (start three)
-- wrow is open at some border, and at the last
#guard ((opens three ps₃ (start three)).getLast?.map (·.contains .wrow)) == some true
-- at the chain's end exactly these six are open
#guard ((opens three ps₃ (start three)).getLast?.map fun O =>
  O.length == 6 && [Item.unmarked, .pinW, .pileOne, .pinI, .pinV, .wrow].all O.contains) ==
    some true

/-! ## At the full size -/

def full : List ModelPart := (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]
def psF : List Place := flatPlaces true full true

#guard psF.length == 358
#guard readsOpen full psF (start full)
#guard (opens full psF (start full)).map (·.filter (· != .wrow)) == openSets full psF (start full)
-- whatever a forward row asks or shuts is open before it
#guard ((opens full psF (start full)).zip psF).all fun x =>
  ((rowAt full x.2).asks ++ (rowAt full x.2).shuts).all x.1.contains
#guard ((opens full psF (start full)).getLast?.map fun O =>
  O.length == 6 && [Item.unmarked, .pinW, .pileOne, .pinI, .pinV, .wrow].all O.contains) ==
    some true

end ProofFile.Honest.FirstRows
