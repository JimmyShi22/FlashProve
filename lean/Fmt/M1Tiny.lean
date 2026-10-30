-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Tiny.lean: the whole verifier of the first toy (a product test), on bytes, tested on files
that a second program, this library's own, has made.

Both honest files are accepted. All 71 bad files are refused, each by the stage (reader or decision)
that the second program's verifier names. The files are this library's own, not the programs' (the
programs: the
C++ implementation that comes with this Lean code). The programs' own files are tested in other
files of this folder (Fmt/M1FullProg.lean).

Sources. The files (Fmt/M1Files.lean: K = 4, 22 rounds, 34 files; Fmt/M1FilesB.lean: K = 3, 21
rounds, 39 files; the re-cut files, three at each size, are not counted here) were made outside Lean
by a reference program of this library's own in Python, which was written independently of the
Lean blocks from the same description of the toy. Each bad file comes with the part of the
description's decision that refuses it first in that reference's verifier: form, proof of work,
openings (here: the reader's), or the last block's two checks (here: the decision's). This file has
not been held against the format page as it ships, and may differ from it
(docs/format/FORMAT.md, which comes with the programs). No Mathlib is imported.

1. What the file contains. Tests, and four small definitions for them (`Who`, `who`, `wants`,
   `wantsB`).
   The path of a file: the strict reader (`wholeChain`, Fmt/Rules8.lean, with the format's hash) at
   the toy's description (`specOf`, Fmt/M1Plan.lean, at the data of Fmt/M1PlanKnown.lean and
   Fmt/M1PlanKnownB.lean); then the view (`viewOf`, Fmt/M1View.lean); then the decision (`dec`,
   Fmt/M1All.lean). That is "verify" of Fmt/M1View.lean at this description and this decision.

2. What is checked when the file compiles (tests, #guard). How many files there are, and of which
   kinds: 34 = 1 honest + 10 for the reader + 23 for the decision; 39 = 1 + 10 + 28. Both honest
   files are accepted. The outcome on every file of the two lists `files` is the one that the table
   asks (`wants`, `wantsB`). "verify" of Fmt/M1View.lean gives these verdicts. One size's honest
   file under the other size's description is refused by the reader.
   The kinds of bad files:
     Bytes of the honest file altered.
     Cheating provers. One word of one message is made one larger before it enters its query; all
       that follows is made by the honest rules. There are nineteen at each size: most messages of
       the protocol in turn, but of the sum-check's rounds the first two alone.
     A false statement proved by the honest rules.
     No code word. A word of a column is altered before the tree is built, at a position that is
       then drawn.

3. Theorems. No theorem in this file. A test (#guard) is an evaluation made while the file compiles;
   the compile fails if the result moves; it leaves no theorem.

4. What is not claimed. It is not shown that either making, Lean's or the reference's, is what the
   programs do: both were written from one description. Which of the decision's two checks refuses
   is not claimed: the decision gives one bit. Which of the reader's tests (form, work, openings)
   refuses is not claimed either: `wants` and `wantsB` take the table's first three parts alike for
   the reader and the last two alike for the decision, so an outcome is compared with the stage
   alone, not with the part that the table names.

Terms: lean/GLOSSARY.md: toy, strict reader, description, view, decision, verifier on bytes,
outcome, re-cut file. Under "Sources" and in part 4 the word "description" names a text, the
description of the toy that belongs to the programs.
-/
import Fmt.M1All
import Fmt.M1View
import Fmt.M1PlanKnown
import Fmt.M1PlanKnownB

namespace Fmt.M1
namespace Tiny

inductive Who where
  | reader
  | decision
  | accepted
  deriving DecidableEq, Repr

/-- The outcome on a file: the reader refuses, the decision refuses, or it is accepted. -/
def who (S : Spec) (P : Par) (b : ByteArray) : Who :=
  match wholeChain (m := Id) formatHash S b with
  | none => .reader
  | some o => if dec P (viewOf S.firstTree o) then .accepted else .decision

def wants : Option Files.Dn → Who
  | none => .accepted
  | some .d1 => .reader
  | some .d2 => .reader
  | some .d3 => .reader
  | some .d4 => .decision
  | some .d5 => .decision

def wantsB : Option FilesB.Dn → Who
  | none => .accepted
  | some .d1 => .reader
  | some .d2 => .reader
  | some .d3 => .reader
  | some .d4 => .decision
  | some .d5 => .decision

end Tiny

-- how many files, and of which kinds: one honest file each; 10 + 23 and 10 + 28 bad ones for the
-- reader and for the decision
open Tiny in
#guard (Files.files.length, (Files.files.filter fun x => wants x.2.2 == .accepted).length, (Files.files.filter fun x => wants x.2.2 == .reader).length, (Files.files.filter fun x => wants x.2.2 == .decision).length) == (34, 1, 10, 23)
open Tiny in
#guard (FilesB.files.length, (FilesB.files.filter fun x => wantsB x.2.2 == .accepted).length, (FilesB.files.filter fun x => wantsB x.2.2 == .reader).length, (FilesB.files.filter fun x => wantsB x.2.2 == .decision).length) == (39, 1, 10, 28)

-- The honest files are accepted
open Tiny in
#guard who Known.spec Known.par Files.honest == .accepted
open Tiny in
#guard who KnownB.spec KnownB.par FilesB.honest == .accepted

-- Every file: the outcome is the one that the table asks
open Tiny in
#guard Files.files.all fun x => who Known.spec Known.par x.2.1 == wants x.2.2
open Tiny in
#guard FilesB.files.all fun x => who KnownB.spec KnownB.par x.2.1 == wantsB x.2.2

-- the verifier on bytes of Fmt/M1View.lean gives these verdicts
#guard Files.files.all fun x => verify Known.spec (fun (_ : Unit) v => dec Known.par v) () x.2.1 == x.2.2.isNone
#guard FilesB.files.all fun x => verify KnownB.spec (fun (_ : Unit) v => dec KnownB.par v) () x.2.1 == x.2.2.isNone

-- one size's honest file under the other size's description: refused by the reader
open Tiny in
#guard who KnownB.spec KnownB.par Files.honest == .reader && who Known.spec Known.par FilesB.honest == .reader

end Fmt.M1
