-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/KeyAnswers.lean, IN PART (the next paragraph says which): the answers in the record as
which a description reads a table are a function of the table's answers; and where the program says
yes they are the table's answers.

Only a part of this file is in this library: it declares `cAL`, `codeA_of_anT`, `recOfArm_answers`,
`codeA_recOfArm`, `codeA_full`, `codeA_small` and nothing else. These are one definition and five
theorems of the first kind of statement below: of the second kind, and so of what the first lines
say of the program's yes, nothing is in the part. The rest of this head describes the whole file and
is kept as written, with its limits. Named in it and not declared in the part that is here:
`recOfArm_digW`, `port_list`, `port_digW_small`, `port_digW`, `port_digW_full`, `port_list_full`,
`recOfArm_list`, `port_list_small`. Named in it and not in this library: OnBytes/K/KeyRecord.lean,
OnBytes/K/KeyRecordAt.lean. Named in the quoted words below and not in this library either:
OnBytes/K/KeyMade.lean.

"The program" is the Lean program `verify-on-bytes` (OnBytes/Main.lean). A tie of the key file that
reads a table t as OnBytes/K/ArmLetters.lean does hands a description the record `recOfArm G Z x t`.
The compiled verifier takes a code of a record's answers, as a list of digests, as a parameter; the
description lays `codeA` (OnBytes/Flat/RecordCode.lean; laid in Johnson/Flat/TwoSizes.lean). By that
file's head the programs write a record as bytes, not as digests. A key file itself holds the
table's answers as the program's elements. This file ties the two spellings.

Two kinds of statement.
 - With no premise but that `recOfArm` returns: the record's answers, and so their list of digests,
   are a written function of `t.answers` (`cAL`). This holds by unfolding and is no tie to the
   program. The function loses two things: an answer with a word at or above the prime is read in
   the field like another, and the list's length is not kept (beyond the list's end 0 is read, and
   nothing is read beyond 2 ^ v * s entries).
 - At a table whose answers have words below the prime and of which `tableKey` returns a key, and so
   at the program's own table where it says yes: nothing is lost. The record's answers, written back
   as the program's elements (the array of `keyOf`, OnBytes/Slice/KeyOfRec.lean), are `t.answers`,
   and their list of digests is `t.answers.map digW`.

Main definition. `cAL v s l`: `codeA` of the list l of the program's elements, read as answers.
Main theorems.
 `codeA_of_anT`       by definition: `codeA` of answers that are read off a list l is `cAL` of l.
 `recOfArm_answers`   the record's answers are `anT` of the table's answers as triples.
 `codeA_recOfArm`     so `codeA` of them is `cAL` of the table's answers.
 `recOfArm_list`      under the two premises on the table: the array of `keyOf` of the record, as a
                      list, is `t.answers`.
 `recOfArm_digW`      and `codeA` of the record's answers is `t.answers.map digW`.
 `port_list`, `port_digW`   the last two at the program's yes on files pinned to Z, at the
                      program's own table, with no premise on the table.
 `codeA_full`, `codeA_small`, `port_list_full`, `port_list_small`, `port_digW_full`,
 `port_digW_small`    at the library's two grounds, with the record in the description's own type.

Hypotheses and whether they can hold: as in the heads of
OnBytes/K/KeyRecord.lean [not in this library] and OnBytes/K/KeyRecordAt.lean [not in this library].

The head of OnBytes/K/KeyRecord.lean [not in this library] says, word for word (files and names in
it that this library does not hold are left as written):
Hypotheses. `PortYesAt`; `G.SaysLines F.pol`; the three pins; the planner's yes and k, which only
name what `PortYesAt` holds; two tests on G: its tables have a record, and its field is the one in
which the program computes; that `recOfArm` returns c; in `recKey_read` and `recKey_chains`, that
the reading returns.

Can the premises hold? The two tests are theorems at both grounds of the library
(`Left.record_answers`, `Left.small_record_answers`, OnBytes/K/Left/Conv.lean; `Left.record_field`,
`Left.small_record_field`, OnBytes/K/Left/LaxKeys.lean). `SaysLines` at these grounds is proved of
every file that begins with the examples' first lines (`Left.full_says_of_prefix`,
`Left.small_says_of_prefix`, OnBytes/K/Left/SaysLinesPrefix.lean). At a run of the program that ends
in 0 on files pinned to Z, `recOfArm` returns a record (`recOfArm_port`) and both readings return:
see the head of OnBytes/K/KeyMade.lean. This file names no such run.

What is not claimed. Nothing on the further table or on a proof file. Nothing on what either
decision says. Nothing on soundness. `recordSeeds` hashes by Lean's BLAKE2b: this is a statement on
values under that one hash. `recOfArm` draws at that hash too: of a reading at another hash these
statements say nothing. That a verifier's test on a record's seeds says yes at this record is not
said here. For proofs only; the program does not import this file.
(Here that head's words end.)
The head of OnBytes/K/KeyMade.lean [not in this library], named in those words: its words stand in
the head of Johnson/Top/KeySilent.lean.

The head of OnBytes/K/KeyRecordAt.lean [not in this library] says, word for word (files and names in
it that this library does not hold are left as written):
Hypotheses, limits and what is not claimed: those of OnBytes/K/KeyRecord.lean, but for the two tests
on the ground.
(Here that head's words end.)

What is not claimed. That any verifier's test on a file's silent rounds says yes. That any coding of
typed queries reads `cAL`. Nothing on the further table. Nothing on soundness. For proofs only; the
program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.RecordCode
import OnBytes.K.ArmLetters
import OnBytes.Flat.EntryTerm

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Tie OnBytes.Slice TypedOracleCompiler.Slice OnBytes.Proof OnBytes.Flat
open _root_.Iop (Dig)

/-- A list of the program's elements, read as the answers of a record with 2 ^ v rows and s answers
a row, and written as a list of digests. -/
def cAL (v s : Nat) (l : List E) : List (Dig 256) := codeA (anT v s (l.map E.triple))

/-- By definition, at answers that are read off a list. -/
theorem codeA_of_anT {v s : Nat} {a : (Fin v → Bool) × Fin s → GE} {l : List E}
    (h : a = anT v s (l.map E.triple)) : codeA a = cAL v s l := by
  rw [h]
  rfl

section
variable {G : EntryGround} {Z : Pub} {x : UserStm} {t : Params.TableName}
  {c : RecP NZ G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers}

/-- The answers of a table's record are the table's answers, read in the field. -/
theorem recOfArm_answers (hc : recOfArm G Z x t = some c) :
    c.2 = anT G.q.link.table.v G.q.link.table.answers (t.answers.map E.triple) := by
  unfold recOfArm at hc
  obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.1 hc
  rfl

/-- **The record's answers as digests are a function of the table's answers.** -/
theorem codeA_recOfArm (hc : recOfArm G Z x t = some c) :
    codeA c.2 = cAL G.q.link.table.v G.q.link.table.answers t.answers :=
  codeA_of_anT (recOfArm_answers hc)

end

/-! ## At the two grounds -/

section
variable {Z : Pub} {x : UserStm} {t : Params.TableName}

/-- At the full size, with no premise but that the record is returned. -/
theorem codeA_full {c : RecFull} (hc : recOfArm recordGround Z x t = some c) :
    codeA c.2 = cAL frS.P.v 1 t.answers :=
  codeA_of_anT (recOfArm_answers hc)

/-- At the small size. -/
theorem codeA_small {c : RecSmall} (hc : recOfArm smallRecordGround Z x t = some c) :
    codeA c.2 = cAL srS.P.v 1 t.answers :=
  codeA_of_anT (recOfArm_answers hc)

end

end OnBytes.K

#print axioms OnBytes.K.codeA_recOfArm
#print axioms OnBytes.K.codeA_full
#print axioms OnBytes.K.codeA_small
