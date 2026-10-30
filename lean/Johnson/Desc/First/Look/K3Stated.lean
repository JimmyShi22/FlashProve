-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Stated.lean: the block at a lookup's address, whole, WITH EVERY RUN OF
CLAIMS THAT THE PROTOCOL'S ORDER LISTS AT IT STATED. One definition, with code. No theorem.

Why. A link's order of claims (Johnson/Desc/First/Driver/Chain.lean: `orderOf`) is laid whole, and
the plan's test at the link (`orderOk`, Johnson/Desc/Block.lean) asks that every run which it lists
is stated by the block at that number, and that no block states another. At a lookup's two places
the order lists "objects" and "guests"; at the lookup on the calls of an attention link and of the
head's link also "planes".

Main names:
  `theStated claim readers X codes shape a`: **the block**: `theWhole` with its runs on ("objects",
    "guests": Johnson/Desc/First/Look/K3Lookup.lean); at the calls' piece of a link i at which
    `readers i` gives the calling kind's readers: "planes" behind them (`withCaller`,
    Johnson/Desc/First/Look/K3Runs.lean).

Limits: readers is a letter: WHICH links have a caller that hands readers in, and that these read
what they are meant to read, is the callers' files' and the seat's: a link at which readers gives
nothing states no "planes", and the plan's test refuses there if the order lists it. At a layers'
link the order lists no "planes" (these claims lie inside the caller's own runs): readers must give
nothing there. "join" is the calling kind's to state. Nothing is proved; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Whole
import Johnson.Desc.First.Look.K3Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes
open OnBytes.Model (Aff)

/-- **The block at an address, whole, with all its listed runs of claims stated.** readers: for a
link's number: the calling kind's readers of the planes' matrix; nothing where the order lists no
"planes". -/
def theStated {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers First.S))
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) :
    Option (Block First.S Cl) :=
  (theWhole claim true X codes shape a).bind fun b =>
    match a.link with
    | none => some b
    | some i =>
      if a.piece != pieceAt X i false then some b else
      match readers i with
      | none => some b
      | some r => (First.Look.placeAt X i false).map fun p => withCaller (seatCalls claim) p r b

end VerifiableInference.Desc.K3
