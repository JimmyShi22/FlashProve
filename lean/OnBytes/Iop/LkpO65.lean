-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/LkpO65.lean: one small lookup as a closed value, with tests. They run when this file
compiles.

`Lkp.o65` is a value of `Lkp.Public` (OnBytes/Iop/Lkp.lean), the public inputs of one lookup: one
part of 2 ^ 4 keys, of which key number 15 is padding and holds row 1; the range table of 2 rows;
counts of 2 ^ 3 bits, all of them real; one function, no shift; the oracle messages from which keys
or counts are read are 0 and 1, and the value does not say which holds which; the first round of
the last key level binds variable 1. `Lkp.o65Keys` are the 15 keys that are not padding.
`Lkp.o65Size` are the sizes at which the planner (OnBytes/Params/Planner.lean) plans such a lookup,
and `Lkp.o65Entries` the entries that it then writes.

What is tested.
 1. The value is well-formed: `Lkp.Public.ok`.
 2. `Lkp.roundsOf`, which states a lookup's rounds as a function of the public inputs, gives 65.
 3. The planner, run on one lookup alone (`Params.planLookup` at `Lkp.o65Size`), under the setting
    in which every field has its default and in the scope of a request, gives 65 entries.
 4. Beside these: the planner's 65 entries are the entries of the 65 rounds of 2, one by one, at no
    work. The dry run of the block `Lkp.verify` goes through on these entries, with the kinds and
    items of 2 (`TestLkp.dryFits`, with one ledger of mask entries and with two). 14 of the rounds
    have the name with which a sumcheck begins. The order in which a level of two variables is
    bound by default is 1, 0; the order that begins as the value says, at three variables, is
    1, 2, 0 (by `Lkp.levelChain` the last key level of this part has three variables; not tested).
    The keys and the padding together are all keys, and each key is the number of a row. The
    padding is one place, right behind the keys of `Lkp.o65Keys`, and holds row 1.

Main definitions: `Lkp.o65`, `Lkp.o65Keys`, `Lkp.o65Size`, `Lkp.o65Entries`.

Not claimed here: soundness or hiding; no theorem is stated. That the planner gives as many entries
under another setting, or that the plan passes the planner's verdict. How many claims the lookup
ends in. The numbers of rounds and of entries depend on `parts`, `d`, `mu`, `live` and `shifted`
alone: tests 2 and 3 would not notice another padding, table or order. In the dry run the counts
are in message 0, message 1 has no main row, and no key is read. This file imports a file of tests
(OnBytes/Iop/TestLkp.lean), so it compiles only where these pass. No module of the program imports
this file.

-/
import OnBytes.Iop.TestLkp
import OnBytes.Params.Planner

namespace OnBytes.Lkp

/-- The public inputs of the lookup. -/
def o65 : Public where
  parts := [4]
  d := 1
  mu := 3
  live := 0
  h := 0
  g := 0
  shifted := false
  readFrom := [0, 1]
  keys := [{ first := 0, logTrees := 0, function := some 0 }]
  tables := [{ first := 0, logRows := 1, function := 0, rows := [] }]
  padding := [{ part := 0, first := 15, logStep := 0, length := 1, row := 1 }]
  lastKeyLevelOrder := [1]

/-- The keys number 0 to 14. Key number 15 is the padding. -/
def o65Keys : List Nat := [0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1]

/-- The sizes at which the planner plans that lookup. -/
def o65Size : Params.LookupSize :=
  { v := 4, d := 1, mu := 3, shifted := false, live := 0, parts := [] }

/-- The planner's entries for one lookup of these sizes and nothing else, under a setting and in the
scope of a request; nothing if the planner refuses. -/
def o65Entries (s : Params.Setting) : Option (List Fmt.Entry) :=
  (Params.finish s .request (Params.planLookup o65Size)).toOption.map (·.plan.entries)

-- 1, 2, 3
#guard o65.ok
#guard (roundsOf 0 o65).length == 65
#guard (o65Entries {}).map (·.length) == some 65

-- 4
#guard o65Entries {} == some ((roundsOf 0 o65).map (·.entry))
#guard TestLkp.dryFits o65 true && TestLkp.dryFits o65 false
#guard ((roundsOf 0 o65).filter fun r => r.entry.name == "PSC epsilon").length == 14
#guard defaultOrder 2 == [1, 0] && orderBeginning o65.lastKeyLevelOrder 3 == [1, 2, 0]
#guard o65Keys.length + paddingCount o65 == o65.allKeys
#guard o65Keys.all fun k => decide (k < 2 ^ o65.d)
#guard o65.padding.map (fun p => (p.part, p.first, p.length)) == [(0, o65Keys.length, 1)]
#guard paddingList o65 == [(1, 1)]

end OnBytes.Lkp
