-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/SentTerms.lean: THE DATA OF THE PUBLIC ITEMS "frame.sentIs" AND "ledger.treesAre"
(`SentData`, Johnson/Desc/First/FillSent.lean) AS A TERM OFF THE PUBLIC PARAMETERS. Definitions with
code and one small theorem. No Mathlib.

  `baseAt N links ps m`: how many oracle messages are sent in front of segment m's first sending:
    the table of joints' own number `N.msgsAt` at the place of that sub-protocol (piece 1 of the
    segment; piece 2 at the head's), found in the list of places ps.
  `looksOf Fp`: what is read of the arrays of a segment's starting ledger, off the planned ledger
    Fp: rows, columns; of each virtual row the first column, and as many weights as the array has
    columns.
  `treesAt built m`: `looksOf` at the planned ledger of segment m's structure of public parameters.
  **`sentDataAt shape N links ps built`**: THE TERM: `sentDataOf shape (baseAt …) (treesAt built)`.
  `looks_startFork`: the arrays of `startFork X ns` (Johnson/Desc/First/Walk/FirstQuiet.lean: the
    ledger that the quiet step which opens a segment lays) have the looks `looksOf X.Fp`.

WHY `N.msgsAt`. The promise of the table of joints asks at every border that the statement in the
verifier's state has `N.msgsAt` oracle messages (`bookAt`, Johnson/Desc/First/Borders.lean). So
inside the promise in front of the segment's first sending `baseAt` IS the statement's own count.

OBJECT: none. USER: meant: the composed meaning's data. LETTERS: shape, N, links, ps, built.

Limits. NOTHING IS EVALUATED HERE. By a run on one honest proof of each of two sizes both items'
tests are true at the statement's own counts (0, 7, 14, 22, 29, …) and at `startFork`'s looks, in
their spans, at all 5 and all 25 segments, and 183 and 903 negative tests are false; THAT `N.msgsAt`
GIVES THESE COUNTS AT THE REAL NUMBERS HAS NOT BEEN RUN THROUGH THIS TERM. The head's segment is
opened by another text than `startFork`'s caller: there the looks are by that run alone. K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED BY THIS. Nothing on soundness.
-/
import Johnson.Desc.First.FillSent
import Johnson.Desc.First.Walk.FirstQuiet
import OnBytes.Model.StagesLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillSent
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero)

/-- How many oracle messages are sent in front of segment m's first sending. -/
def baseAt (N : Numbers) (links : List ModelPart) (ps : List Place) (m : Nat) : Nat :=
  N.msgsAt (ps.find? fun p => p.link == some m && p.piece == 1 + ((links[m]?).map shift).getD 0)

/-- What is read of the arrays of a starting ledger, off the planned ledger. -/
def looksOf (Fp : Fork) : List TreeLook :=
  Fp.trees.toList.map fun T => (T.R, T.K, T.rows.toList.map fun r => (r.L0, T.K))

/-- The looks of segment m's starting ledger. -/
def treesAt (built : Array Stages.LinkH) (m : Nat) : List TreeLook :=
  ((built[m]?).map fun X => looksOf X.Fp).getD []

/-- **The term.** -/
def sentDataAt (shape : Params.ReqShape) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (built : Array Stages.LinkH) : SentData :=
  sentDataOf shape (baseAt N links ps) (treesAt built)

/-- The starting ledger's arrays have these looks. -/
theorem looks_startFork (X : LinkPub) (ns : Nat) :
    (startFork X ns).trees.toList.map treeLook = looksOf X.Fp := by
  show ((X.Fp.trees.map fun T =>
    { T with rows := T.rows.map fun r => { r with L := Array.replicate T.K zeroE } }).toList.map
      treeLook) = _
  unfold looksOf
  rw [Array.toList_map, List.map_map]
  refine List.map_congr_left fun T _ => ?_
  show (T.R, T.K, ((T.rows.map fun r => { r with L := Array.replicate T.K zeroE }).toList.map
    fun r => (r.L0, r.L.size))) = _
  rw [Array.toList_map, List.map_map]
  refine congrArg (fun z => (T.R, T.K, z)) (List.map_congr_left fun r _ => ?_)
  show (r.L0, (Array.replicate T.K zeroE).size) = _
  rw [Array.size_replicate]

end VerifiableInference.Desc.First.FillSent

#print axioms VerifiableInference.Desc.First.FillSent.looks_startFork
