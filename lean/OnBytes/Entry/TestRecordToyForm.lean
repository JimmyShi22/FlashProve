-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestRecordToyForm.lean: tests of form on the declared structure of the toy of
OnBytes/Entry/RecordToyFiles.lean (OnBytes/Entry/TestRecordToyDeclared.lean), and the entry RECORD.

1. The plan's words. They are those that the reader of parameter bytes finds in the programs' own
   parameter bytes. The declared rounds' entries were read off these very bytes, so for them this
   holds reader against reader; what it tries is the entry RECORD, its place and the order of an
   entry's words. With one word raised by 1, words and bytes both differ from the programs'.
2. Two tellings under one hash. A word of the plan raised by 2 ^ 64 gives other words and the same
   parameter bytes, since a word is written in eight bytes. Declared.entryFormOk refuses it.
3. The answers to a sample. The setting's number against the table's shape: with two in the setting
   and one in the shape, Declared.settingOk says no, and so does Declared.entryFormOk. The other
   clauses of Declared.settingOk, each by itself: a nonce of nine bytes and of none, a listed
   position of nine bytes, a shape out of the format's ranges.
4. Ten structures with one thing changed, each refused by Declared.entryFormOk. At some of them a
   second clause refuses too.
5. The entry RECORD, which counts what is drawn for the out-of-domain sample on a stored table. By
   R13.15 (docs/format/09-key-and-leaf-files.md; also docs/format/08-parameters.md) it has
   S * (ceil_log2(i) + 1) elements, S of them not 0, for S answers a row and i entries of a row's
   message; it stands first in the plan, it is no round, and a chain without the flag has none. The
   numbers that are expected were worked out by hand from that rule. At the toy's own shape the
   entry is also held by the programs' bytes: it is among the words of the parameter bytes that
   OnBytes/Entry/TestRecordToyDeclared.lean compares.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. The changed structures are made up: no public files give them. Four clauses
of Declared.entryFormOk are refused by no test here: that the link takes no tree over, that it has
no round SEAL, the stored trees' shape against the tables', and, by itself, that the random bytes
stand in the file. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Entry.TestRecordToyDeclared
import Fmt.ParamsReadLaws

namespace OnBytes.Entry.RecordToy
open Fmt

/-- The declared structure with n added to the word "rows" of the entry of round i, from 0. -/
def rowsRaised (D : Declared) (i n : Nat) : Declared :=
  { D with link := { D.link with rounds := D.link.rounds.zipIdx.map fun r =>
      if r.2 == i then { r.1 with entry := { r.1.entry with rows := r.1.entry.rows + n } }
      else r.1 } }

/-- The plan's words as the reader of parameter bytes finds them in the programs' bytes. -/
def programsWords : Option (List (String × List Nat)) :=
  (paramsRead entryParameters).map fun p => p.plan.entries.map fun e => (e.name, e.words)

-- the declared plan's words are the programs'; with one word raised by 1, words and bytes differ
#guard (declared.map fun D => some (D.planWords D.link) == programsWords) == some true
#guard (declared.map fun D =>
  let D' := rowsRaised D 5 1
  (some (D'.planWords D'.link) == programsWords, D'.params D'.link D.cfg == entryParameters)) ==
  some (false, false)

-- other words, the same parameter bytes, refused; the structure itself passes
#guard (declared.bind fun D => statementAt.map fun x =>
  let D' := rowsRaised D 5 (2 ^ 64)
  (D'.planWords D'.link != D.planWords D.link, D'.params D'.link D.cfg == D.params D.link D.cfg,
    D'.entryFormOk D.cfg x, D.entryFormOk D.cfg x)) == some (true, true, false, true)

-- two answers to a sample in the setting, one in the shape: the clause says no, and all is refused
#guard (declared.bind fun D => statementAt.map fun x =>
  let D' : Declared := { D with setting := { D.setting with samples := 2 } }
  (D.settingOk, D'.settingOk, D'.entryFormOk D.cfg x)) == some (true, false, false)
-- the other clauses of the test on the setting, each by itself
#guard (declared.map fun D =>
  ([{ D with setting := { D.setting with nonce := 9 } },
    { D with setting := { D.setting with nonce := 0 } },
    { D with setting := { D.setting with posB := 9 } },
    { D with table := { D.table with a := 0 } }] : List Declared).map (·.settingOk)) ==
  some [false, false, false, false]
-- a digest of 31 bytes: refused
#guard (declared.bind fun D => statementAt.map fun x => D.entryFormOk (D.cfg.extract 0 31) x) ==
  some false

/-- The structure with one thing changed: one of LINK's draws moved from the second table's part to
the first's, so that the sum is kept; a listed position of nine bytes; a nonce of nine bytes, and of
none; the link without the flag of the entry RECORD; no random bytes; another label; the items in
another order; 2 ^ 64 added to a number of the shape, which leaves the item's word as it is; the
link's first tree 5, with its trees' numbers raised by 5. -/
def changed (D : Declared) : List Declared :=
  [{ D with link := { D.link with rounds := D.link.rounds.map fun r =>
      { r with stored := r.stored.map fun t =>
          if t.item == 0 then { t with count := t.count + 1 }
          else { t with lo := t.lo + 1, count := t.count - 1 } } } },
   { D with setting := { D.setting with posB := 9 } },
   { D with setting := { D.setting with nonce := 9 } },
   { D with setting := { D.setting with nonce := 0 } },
   { D with link := { D.link with record := false } },
   { D with link := { D.link with rand := .none } },
   { D with link := { D.link with label := 0x4c494e01 } },
   { D with link := { D.link with others := D.link.others.reverse } },
   { D with table := { D.table with message := D.table.message + 2 ^ 64 } },
   { D with link := { D.link with firstTree := 5, rounds := D.link.rounds.map fun r =>
      { r with opens := r.opens.map fun o => ({ o.1 with tree := o.1.tree + 5 }, o.2) } } }]

#guard (declared.bind fun D => statementAt.map fun x =>
  (changed D).map (·.entryFormOk D.cfg x)) == some (List.replicate 10 false)

-- at the toy (one answer a row, 803 entries): the entry stands first, with 11 elements, one not 0;
-- it is no round; a chain without the flag has none
#guard (declared.map fun D =>
  ((D.entries D.link).head?, (D.entries D.link).length == D.link.rounds.length + 1,
    (D.plan D.link).rounds == (D.plan { D.link with record := false }).rounds &&
      (D.plan D.link).rounds.length == D.link.rounds.length,
    (D.entries { D.link with record := false }).length == D.link.rounds.length)) ==
  some (some { name := recordName, drawE := 11, drawNZ := 1 }, true, true, true)

-- the rule at a power of two with two answers; one entry more; a single entry; 2 ^ 19 entries
#guard recordEntry ⟨14, 1024, 1001, 3, 2, 40⟩ == { name := recordName, drawE := 22, drawNZ := 2 }
#guard recordEntry ⟨14, 1025, 1001, 3, 1, 40⟩ == { name := recordName, drawE := 12, drawNZ := 1 }
#guard recordEntry ⟨14, 1, 1001, 3, 1, 40⟩ == { name := recordName, drawE := 1, drawNZ := 1 }
#guard recordEntry ⟨23, 524288, 65535, 8, 1, 40⟩ ==
  { name := recordName, drawE := 20, drawNZ := 1 }

end OnBytes.Entry.RecordToy
