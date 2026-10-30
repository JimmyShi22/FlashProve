-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SharedRows.lean: the shared chain's table of joints, read
forward. It gives three parameters of the shared chain's `Thread` (Honest/Thread/Thr.lean: `ι`,
`start`, `row`), from the library's own table (Johnson/Desc/Shared/BordersShared.lean: `ItemS`,
`startS`, `rowS`). No table changes: the forward rows are this folder's. Definitions and `#guard`
lines; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

The one adjustment. The slot's own items are left out (`ItemS.own`): the shared chain's prover's
sides are given no instance and no state of the first chain, by type: so its invariant can state
nothing on them. What is left of the row of "LIN point": it shuts the stored table's pin and owes
three propositions on u and Omega. The own items (the rows (Eval) and (Dot) among them) have to be
proved at the second chain's start.

What the lines check, by evaluation, at both shapes (with the round "SPLIT" and without): the
table's own test passes; the forward rows pass this folder's; at every border the forward open set
is the table's own without the own items, item for item and in the same order; at the chain's start
the stored table's pin alone is open, at its end Omega's pin alone.

Limits.
  * Lists alone: nothing is said on what an item says.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.Shared.BordersShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SharedRows
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (ItemS rowS openSetsS readsOpenS sharedPlaces)

/-- A list without the slot's own items. -/
def shared (l : List ItemS) : List ItemS := l.filter fun i => !i.own

/-- The table's own open set at the chain's start. (By its full name: inside this file's namespace
the short name is another constant's.) -/
abbrev startT : List ItemS := VerifiableInference.Desc.Shared.startS

/-- What is open at the chain's start. -/
def start : List ItemS := shared startT

/-- The forward row of the sub-protocol at a place. `split`: the two messages differ in code. -/
def rowAt (split : Bool) (p : Place) : FwdRow ItemS :=
  FwdRow.of (shared (rowS split p).ins) (shared (rowS split p).outs) (shared (rowS split p).ctx)

/-- The forward row after border number b; an empty row beyond the list. -/
def rows (split : Bool) (b : Nat) : FwdRow ItemS :=
  (((sharedPlaces split)[b]?).map (rowAt split)).getD {}

#guard start == [.pinT]
#guard [true, false].all fun sp => readsOpenS sp (sharedPlaces sp) startT
#guard [true, false].all fun sp => fwdFit start (rows sp) (sharedPlaces sp).length
-- the forward open sets are the table's own without the own items
#guard [true, false].all fun sp =>
  (List.range ((sharedPlaces sp).length + 1)).map (fwdOpen start (rows sp)) ==
    (openSetsS sp (sharedPlaces sp) startT).map shared
-- after "LIN point": three propositions on u and Omega
#guard fwdOpen start (rows true) 2 == [.omU, .nearU, .recRow]
-- at the chain's end
#guard [true, false].all fun sp =>
  fwdOpen start (rows sp) (sharedPlaces sp).length == [.pin .oOmega]

end ProofFile.Honest.SharedRows
