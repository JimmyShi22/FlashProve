-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Names.lean: the names of the format's rounds, each with its kind.

A chain's parameter bytes hold the names of its rounds and not their kinds. The kind of a round
says what the verifier's message consists of. It follows from the name, by the list of the format
page (docs/format/FORMAT.md, R14.11). The list is part of the format: `Given.read`
(OnBytes/Params/Given.lean) refuses a plan that holds a name outside it. A name gives the block
(BAT, PSC, FOLD ..) and the round's place in it. It does not say for which use of the block the
round is made. The C++ counterpart is `kind_of_round` (blocks/numbers/plan.h). There RECORD has a
kind of its own; here it has none, and `namesKnown` admits it by its name.

Main definitions: `kindOf`, `recordName`, `namesKnown`.
-/
import OnBytes.Base

namespace OnBytes.Params

/-- The names of the rounds in which the verifier draws elements of the extension field. -/
def namesElems : List String :=
  ["BAT", "BAT-sigma", "PSC round", "PSC Y", "ZERO", "LINE", "LKP shift", "JOIN", "LKP",
   "FOLD round", "BASE lambda", "LIN point", "LIN zeta", "LINK point", "LINK phi"]

/-- The names of the rounds in which the verifier draws the element that joins a hiding
polynomial to a claim. -/
def namesJoin : List String := ["PSC epsilon", "FOLD epsilon"]

/-- The names of the rounds in which the verifier draws the seeds of out-of-domain samples. -/
def namesSeeds : List String := ["SEND seed"]

/-- The names of the rounds in which the verifier draws positions. -/
def namesPositions : List String := ["LOC", "CS", "BASE", "LINK"]

/-- The names of the rounds in which the verifier draws entries of a matrix over -1, 0, 1. -/
def namesEntries : List String := ["RNG"]

/-- The names of the rounds that end in a seal. -/
def namesSealed : List String := ["SEAL"]

/-- The names of the rounds in which the verifier says nothing. -/
def namesNothing : List String := ["SEND answer", "SPLIT", "PSC values", "REPLY", "LAST"]

/-- The kind of the round of a name, or nothing if the format has no round of this name. -/
def kindOf (name : String) : Option Fmt.Kind :=
  if namesElems.contains name then some .elems
  else if namesJoin.contains name then some .join
  else if namesSeeds.contains name then some .seeds
  else if namesPositions.contains name then some .positions
  else if namesEntries.contains name then some .entries
  else if namesSealed.contains name then some .sealed
  else if namesNothing.contains name then some .nothing
  else none

/-- The name of the one entry of a plan that is no round of its chain: a stored table's own
sample. -/
def recordName : String := Fmt.recordName

/-- True if every entry of the plan has a name of the format. -/
def namesKnown (P : Fmt.Plan) : Bool :=
  P.entries.all fun e => e.name == recordName || (kindOf e.name).isSome

/-- A round from its plan entry, the items of the prover's message and the trees that it opens.
The kind is the kind of the entry's name. Nothing if the format has no round of this name. -/
def round (e : Fmt.Entry) (items : List Fmt.Item := [])
    (opens : List (Fmt.Shape × Fmt.Src) := []) : Option Fmt.Round :=
  (kindOf e.name).map fun k => { entry := e, kind := k, items := items, opens := opens }

end OnBytes.Params
