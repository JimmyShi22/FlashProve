-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Given.lean: the parameter bytes of one chain, read, and the chain's description.

Every chain begins with a hash call on its parameter bytes (docs/format/FORMAT.md, R4.3 and
R4.4). These hold the format's version, the plan of the chain's rounds, the digest of the public
files and further items: the codes and the shapes of the protocol. The C++ verifier computes these
bytes from the public files. Some of the numbers in them (numbers of positions, lengths of random
tails, lengths of later mask messages) come out of a sizing by interval arithmetic.

This file reads parameter bytes, wherever they come from. It tests their spelling, the form of the
plan and the names of the rounds; none of these tests needs the sizing.
OnBytes/Params/Configure.lean makes parameter bytes from the public files. A caller that reads
those bytes back here uses values that are parsed out of the very bytes that are hashed. A verdict
that rests on bytes from elsewhere holds only "under the given parameter bytes".

A block of the protocol states its rounds from its own sizes. `Given.describe` puts these rounds
together with the given bytes. It returns a description only if the rounds are, entry for entry,
the rounds of the given plan, and if the description meets the strict reader's conditions.

Main definitions: `Given`, `Given.read`, `Given.item`, `Given.describe`.
What is not claimed: that the given numbers meet the conditions of a soundness statement.
-/
import OnBytes.Chain.Lists
import OnBytes.Chain.Loops
import OnBytes.Params.Names

namespace OnBytes.Params

/-- The parameter bytes of one chain, and what they hold. -/
structure Given where
  /-- the bytes as they are hashed -/
  bytes : ByteArray
  /-- the plan of the chain's rounds -/
  plan : Fmt.Plan
  /-- the digest of the public files -/
  cfg : ByteArray
  /-- the further items, in their order: name and value -/
  items : List (String × ByteArray)

namespace Given

/-- Reads parameter bytes. Nothing if they are not spelled as the format page says (R4.3); if the
plan fails `Fmt.Plan.ok` (an entry whose first word, the number of rounds that it is for, is not 1;
a seventh word of the plan other than 1; more than one entry RECORD); or if an entry has a name that
is none of the format's. The version is compared with the plan's own field, 1 or 2: whether that
is the field which this program serves is left to the caller. -/
def read (b : ByteArray) : Option Given :=
  (paramsReadT b).bind fun p =>
    if p.plan.ok && namesKnown p.plan then some ⟨b, p.plan, p.cfg, p.others⟩ else none

/-- The value of the first further item with the name `name`. -/
def item (g : Given) (name : String) : Option ByteArray :=
  (g.items.find? fun x => x.1 == name).map (·.2)

/-- The names of the further items, in their order. -/
def itemNames (g : Given) : List String := g.items.map (·.1)

/-- The plan's entries that are rounds of the chain, in their order. -/
def rounds (g : Given) : List Fmt.Entry := g.plan.rounds

/-- The plan's entry for a stored table's own sample, if the plan has one. -/
def record (g : Given) : Option Fmt.Entry := g.plan.entries.find? fun e => e.name == recordName

/-- The rounds of one name, in their order. -/
def named (g : Given) (name : String) : List Fmt.Entry := g.rounds.filter fun e => e.name == name

/-- The rounds in which positions are drawn, in their order. Each entry holds the number of
positions, their range and the bits of work. -/
def lists (g : Given) : List Fmt.Entry :=
  g.rounds.filter fun e => kindOf e.name == some .positions

/-- True if the digest of the public files that the bytes hold is d. -/
def under (g : Given) (d : ByteArray) : Bool := g.cfg == d

/-- The description of a chain with these parameter bytes.
`rounds` are the rounds as the protocol's blocks state them. `stored` says for each round which
stored trees it opens. Nothing if the rounds are not the rounds of the given plan, or if another
condition of the strict reader on a description fails. -/
def describe (g : Given) (label : Nat) (statement : ByteArray) (rand : Fmt.Rand)
    (rounds : List Fmt.Round) (stored : List (List Fmt.Stored)) (firstTree : Nat := 0) :
    Option Fmt.SpecX :=
  let S : Fmt.SpecX :=
    { base := { label := label, plan := g.plan, params := g.bytes, statement := statement,
                rand := rand, firstTree := firstTree, cfg := g.cfg, rounds := rounds },
      stored := stored }
  if specXOk S then some S else none

/-- `Given.describe` for a chain that opens no stored tree. -/
def describePlain (g : Given) (label : Nat) (statement : ByteArray) (rand : Fmt.Rand)
    (rounds : List Fmt.Round) (firstTree : Nat := 0) : Option Fmt.SpecX :=
  g.describe label statement rand rounds (rounds.map fun _ => []) firstTree

/-- The place of the first round at which the stated rounds and the given plan differ, or nothing
if they agree. For a report on why no description was made. -/
def firstDifference (g : Given) (rounds : List Fmt.Round) : Option Nat :=
  let a := rounds.map (·.entry)
  let b := g.rounds
  if a == b then none
  else some (((zipT a b).takeWhile fun x => x.1 == x.2).length)

end Given

end OnBytes.Params
