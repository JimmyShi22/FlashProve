-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/LastRows.lean: the second chain's table of joints, read
forward: three parameters of the second chain's `Thread` (Honest/Thread/Thr.lean: `ι`, `start`,
`row`), from the library's own table (Johnson/Desc/Last/BordersLast.lean: `ItemL`, `startLast`,
`rowL`). No table changes: the forward rows are this folder's. Definitions and `#guard` lines;
no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

What the lines check: one of the table's own tests passes (`readsOpenL`: what a row closes or reads
is open before it); the forward rows pass this folder's test; at every border the forward open set
is the table's own; after the last sub-protocol nothing is open.

Limits.
  * Lists alone: nothing on what an item says.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.Last.BordersLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.LastRows
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Last (ItemL rowL startLast openSetsL readsOpenL lastPlaces)

/-- The forward row of the sub-protocol at a place. -/
def rowAt (p : Place) : FwdRow ItemL := FwdRow.of (rowL p).ins (rowL p).outs (rowL p).ctx

/-- The forward row after border number b; an empty row beyond the list. -/
def rows (b : Nat) : FwdRow ItemL := ((lastPlaces[b]?).map rowAt).getD {}

#guard readsOpenL lastPlaces startLast
#guard fwdFit startLast rows lastPlaces.length
#guard (List.range (lastPlaces.length + 1)).map (fwdOpen startLast rows) ==
  openSetsL lastPlaces startLast
#guard fwdOpen startLast rows 1 == [.pinI, .pinV, .pinO, .rows]
#guard fwdOpen startLast rows lastPlaces.length == []

end ProofFile.Honest.LastRows
