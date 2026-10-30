-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/EntryRounds.lean: the parts of the description of an entry's chain.

`Tie.entrySpec` makes a description of an entry file's chain: from the chain's parameter bytes, from
the rounds that a dry run of the link's block states (`Blk.rounds`: a run on zeros that only notes
the rounds), and from the two tables' names. The program's reader `Entry.read` reads the chain under
that description (`Tie.entry_read_spec`).

Main definitions: `plainKey`, `entryBlock`, `entryRounds`, `entrySpecOf`.
-/
import OnBytes.Tie.EntryFile

namespace OnBytes.Params

/-- The key with an empty record and no seeds: the number of the statement's item alone. -/
def plainKey (item : Nat) : TableKey := { item := item, record := #[], seeds := [] }

/-- The block of an entry's chain at the keys `plainKey 0` and `plainKey 1`. -/
def entryBlock (p : Link) : Blk Unit := linkVerify p.link (plainKey 0) (plainKey 1)

/-- The rounds that the dry run of that block states, each with the stored trees that it opens. -/
def entryRounds (p : Link) : Option Rounds := (entryBlock p).rounds (Entry.start p)

/-- The description of an entry's chain with given rounds and a given statement. -/
def entrySpecOf (p : Link) (r : Rounds) (statement : ByteArray) : Fmt.SpecX :=
  { base := { label := labelLink, plan := p.given.plan, params := p.given.bytes,
              statement := statement, rand := .inFile, firstTree := 0, cfg := p.given.cfg,
              rounds := r.map (·.1) },
    stored := r.map (·.2) }

end OnBytes.Params
