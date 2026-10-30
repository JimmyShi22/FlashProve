-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1Full.lean: the whole verifier of the first toy (a product test), on bytes, at the programs'
own parameters, in the form that runs fast. Here: its definition, the proof that it equals the slow
form, and the tests at their tiny parameters.

The verifier on bytes takes a proof file and answers in two stages: a parser that also makes the
tests on hashes (the reader; other heads call it the strict reader), and the algebraic check on what
was parsed (the decision). Definitions, one statement with its proof, tests (#guard). No Mathlib.
(In this head "the programs" are the C++ implementation that comes with this Lean code, and "the
format page" is docs/format/FORMAT.md, which comes with the programs.)

The page: this file has not been held against the format page as it ships, and may differ from it.
The steps: file ↦ the reader of a chain in a file in its fast form
(Fmt/Rules8Fast.lean: `wholeChainF`, proved equal to Fmt/Rules8.lean's reader at the format's hash)
↦ the view (Fmt/M1View.lean: `viewOf`) ↦ the decision (Fmt/M1All.lean: `dec`).

Main names:
  `whoF S P file`: the outcome on a file: the reader or the decision refuses, or "accepted".
  `Spec.whoF_eq` (the statement), `whoF_eq` (its proof): `whoF` = `Tiny.who` (Fmt/M1Tiny.lean), for
    every description, all sizes and every file.
  `valuesF S P file`: the nineteen values that the programs' tool prints beside a proof
    (Fmt/M1Targets.lean: `targets`), from the bytes of a file.

The parameters are the programs' own, byte for byte (Fmt/M1PlanKnownT.lean holds that against
Fmt/M1Theirs.lean). The proof files are this library's own, not theirs (Fmt/M1FilesT.lean): made
outside Lean by a reference program of this library's own in Python (a second program, this
library's own, written
independently of the Lean blocks from the same description), at these parameters. This file's
sources include no proof file of the programs. A proof file of the programs is judged by `whoF` at
its description and sizes, and `valuesF` is set beside their nineteen printed values:
Fmt/M1FullProg.lean and the files that it gathers.

Tests (#guard), at their tiny parameters (22 rounds; three trees; 3, 3, 5 positions; 6 bits of
work):
  The honest file is accepted.
  All 42 bad files are refused, each at the stage that the table (`FilesT.files`, Fmt/M1FilesT.lean)
    asks for.
  The three re-cut files are refused by the reader. A re-cut file has a nonce that fails the work
    test of one round, and all that follows is made by the honest rules, with the challenges drawn
    from that nonce's answer. By the reference program's own assertion only the work test can refuse
    them (`recut_16`, `recut_20`, `recut_22`, Fmt/MustBeRefused/M1FilesT.lean).
  The nineteen values of the honest file are the reference's own list.

Notation:
  `S`: a description (`Fmt.Spec`, Fmt/Rules8.lean);
  `P`: the sizes (`Par`, Fmt/M1Types.lean);
  d1 form; d2 work; d3 openings; d4 the last block's linear check; d5 its checks at the positions
    (`Dn`; the head of Fmt/M1FilesT.lean);
  BAT: the batching block;
  FOLD: a fold;
  CS: the code switch;
  BASE: the last block
  (the heads of Fmt/M1Dec.lean and Fmt/M1Ref.lean).

Limits: this file does not show that either implementation (the reference program's, Lean's) matches
the programs'. It does not show which of the decision's two checks refuses. It does not show either
which of the reader's tests (form, work, openings) refuses: `wantsT` takes the table's parts d1, d2,
d3 alike for the reader and d4, d5 alike for the decision, so an outcome is compared with the stage
alone, not with the part that the table names. The outcome "decision" says only that the reader
reads the file and `dec` is false. The guards are tests by evaluation; the one theorem ties two
forms of one function.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1Tiny
import Fmt.M1Targets
import Fmt.Rules8Fast
import Fmt.M1PlanKnownT

namespace Fmt.M1
namespace Full

/-- The outcome on a file, by the fast reader: the stage that refuses it, or "accepted". -/
def whoF (S : _root_.Fmt.Spec) (P : Par) (b : ByteArray) : Tiny.Who :=
  match wholeChainF S b with
  | none => .reader
  | some o => if dec P (viewOf S.firstTree o) then .accepted else .decision

/-- The values of `targets` (nineteen where `P.stages` has three entries), from a file's bytes; none
if the reader refuses or `targets` gives none. -/
def valuesF (S : _root_.Fmt.Spec) (P : Par) (b : ByteArray) : Option (List E) :=
  (wholeChainF S b).bind fun o => targets P (ofView (viewOf S.firstTree o))

def wantsT : Option FilesT.Dn → Tiny.Who
  | none => .accepted
  | some .d1 => .reader
  | some .d2 => .reader
  | some .d3 => .reader
  | some .d4 => .decision
  | some .d5 => .decision

namespace Spec

def whoF_eq : Prop := ∀ (S : _root_.Fmt.Spec) (P : Par) (b : ByteArray), whoF S P b = Tiny.who S P b

end Spec

theorem whoF_eq : Spec.whoF_eq := by
  intro S P b
  unfold whoF Tiny.who
  rw [wholeChainF_eq]
  generalize wholeChain (m := Id) formatHash S b = q
  cases q with
  | none => rfl
  | some o => rfl

end Full

-- the sizes that the head names
#guard KnownT.spec.rounds.length == 22 && (List.range 4).map (fun n => (KnownT.spec.shapeOf n).isSome) == [true, true, true, false] &&
  (KnownT.spec.rounds.filter fun r => r.entry.poss != 0).map (fun r => (r.entry.poss, r.entry.work)) == [(3, 6), (3, 6), (5, 6)]
-- how many files, and for whom
open Full in
#guard (FilesT.files.length, (FilesT.files.filter fun x => wantsT x.2.2 == .accepted).length, (FilesT.files.filter fun x => wantsT x.2.2 == .reader).length, (FilesT.files.filter fun x => wantsT x.2.2 == .decision).length, FilesT.recut.length) == (43, 1, 13, 29, 3)
-- the honest file is accepted
open Full in
#guard whoF KnownT.spec KnownT.par FilesT.honest == .accepted
-- every file: the outcome is the one that `wantsT` gives for what the table names
open Full in
#guard FilesT.files.all fun x => whoF KnownT.spec KnownT.par x.2.1 == wantsT x.2.2
-- the re-cut files: the table names the work test; the reader refuses
open Full in
#guard FilesT.recut.all fun x => x.2.2 == some .d2 && whoF KnownT.spec KnownT.par x.2.1 == .reader
-- the slow form says the same on the honest file (for all files: the theorem)
open Full in
#guard Tiny.who KnownT.spec KnownT.par FilesT.honest == .accepted
-- the nineteen values of the honest file, as the reference printed them in the programs' list's
-- form and order
open Full in
#guard valuesF KnownT.spec KnownT.par FilesT.honest == some [(680608101618142392, 10209444979705331995, 8931356548886882391), (2637727688289375359, 10855865163919191383, 4465679465540371469), (3799083078186220895, 5112072507025520481, 7913239970638349822), (10701019736342306640, 18257450498361125476, 15203245618147377310), (16818297972875907557, 11009338634227485953, 4398111056026136337), (11541501933907297096, 17883080249706047511, 15643836348317599291), (16256887865292728071, 5725159430023758250, 3162883159927474824), (11357420405690627657, 3443596223400738876, 12306832359255866078), (9242445956560690495, 2866593591931181186, 6070500428103399272), (18134209372092119855, 17780998536678063988, 3051911278915513500), (6865774099403531348, 5516683074484433836, 5198120729007904195), (11230057008538144923, 11468437827646517311, 233909999399833118), (15412813435927527450, 305656954827421524, 6827624518219596847), (12202717425295615849, 3455442394954750157, 1651686070665446419), (4644909585502076821, 13154305799997773784, 17508051172816461308), (12724507501240187930, 12910557335868450357, 318245607041962604), (8781605420105688655, 11907507969239871989, 11428176060281367646), (18214070653716363266, 8186169370404842958, 5709785673034067352), (18214070653716363266, 8186169370404842958, 5709785673034067352)]
#guard names 3 == ["BAT: target", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "FOLD: target", "CS: y_main at the first draw", "CS: y_0 at the first draw", "CS: y_1 at the first draw", "CS: target", "CS: c'[0]", "CS: d'[0]", "CS: d's last entry", "BASE: left side of the linear check", "BASE: right side of the linear check"]

end Fmt.M1
