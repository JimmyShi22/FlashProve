-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1SpecKnown.lean: the first toy, at the descriptions of this library that are listed below. The
conditions that do not look at a file (`Spec.ok`) hold, as theorems. And from the parameter bytes
alone the sizes and the whole description come back. This file has the statements.
The descriptions:
  the four of this library's own Python reference program's sets of files, T, R, P, F;
  the two at which the programs' own files are judged.

The first toy is a product test. "The programs" are the C++ implementation that comes with this Lean
code; "the format page" is docs/format/FORMAT.md, which comes with the programs. A description is
what a verifier knows before it sees a file. In Lean it is the record `Fmt.Spec` (Fmt/Rules8.lean);
among
its fields: label, plan, parameter bytes, statement, rounds. The sizes (`Par`, Fmt/M1Types.lean) are
the toy's parameters. More on these words: the head of Fmt/M1ParOfLaws.lean.
T, R and P have the tiny parameters, F the full parameters.

Why. `spec_back` of Fmt/M1ParOfLaws.lean assumes `Spec.ok`. A test (#guard) of `Spec.ok` is an
evaluation that leaves no theorem. Here `Spec.ok` is stated as a theorem. With that theorem, at the
descriptions that are run, the bytes that enter the chain's first value fix the description that the
reader follows: the counterpart of rule R0.5 of FORMAT.md.

1. What the file contains. Four statements (`Fmt.M1.Spec.*`). The proofs are in
Fmt/M1SpecKnownProofs.lean. No Mathlib.

2. What is checked when the file compiles. Nothing.

3. Theorems stated here.
   `params_head`: for every plan, digest of the public files and further items, the parameter bytes
     begin with the bytes that the same plan and digest give without further items. This is the
     second of the fourteen clauses of `Spec.ok` (Fmt/Rules8Ok.lean), for all descriptions whose
     parameters are spelled by `paramsBytes` (Fmt/Rules4.lean).
   `known_ok`: `KnownT.spec.ok`, `KnownR.spec.ok`, `KnownP.spec.ok`, `KnownF.spec.ok` = true.
   `known_spec`: specFrom S.params = some (the sizes, S) at these four. (`specFrom`,
     Fmt/M1Prog.lean, reads the bytes, takes the sizes out of the plan and the items, compares the
     plan that was read with the plan of these sizes, spells the description anew and compares its
     parameters with the bytes, and asks `Spec.ok` of it.)
   `theirs_spec`: the same, with `Spec.ok`, at `Theirs.specTiny` with `Theirs.sizesTiny` and at
     `Theirs.specFull` with `Theirs.sizesFull`. These are the descriptions at which the programs'
     own files are judged (Fmt/M1TheirsSpec.lean).
   How the proofs go. Thirteen of the fourteen clauses are decided by the kernel, each by itself.
     The whole of `Spec.ok` at once, and its second clause alone, are too much for the kernel
     (tried: it runs out of memory); that clause is proved by `params_head`.

Notation:
   T, R, P, F: the sets of proof files of Fmt/M1FilesT.lean, Fmt/M1FilesR.lean, Fmt/M1FilesP.lean
     and Fmt/M1FilesF.lean (their heads say what they are);
   R: with the chain's random bytes taken from a run of the programs;
   P: with random bytes at which one position is drawn twice;
   `cfg`: bytes that `paramsBytes` (Fmt/Rules4.lean) takes as the configuration's digest; the row on
     `params_head` calls them the digest of the public files.

4. What is not claimed.
   Nothing is claimed on a file.
   It is not claimed that the sizes follow from the public file's text.
   Nothing is claimed on the second toy's and the entry file's descriptions (see
     Fmt/M2SpecKnown.lean, Fmt/M3SpecKnown.lean).
   It is not claimed that `Spec.ok` is all that the format page asks of a description.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1ParOfKnown
import Fmt.M1ParOfTheirs
import Fmt.Rules8Ok

namespace Fmt
namespace M1
namespace Spec

def params_head : Prop := ∀ (P : Plan) (cfg : ByteArray) (others : List (String × ByteArray)),
  ((paramsBytes P cfg others).extract 0 (paramsBytes P cfg []).size == paramsBytes P cfg []) = true

def known_ok : Prop :=
  KnownT.spec.ok = true ∧ KnownR.spec.ok = true ∧ KnownP.spec.ok = true ∧ KnownF.spec.ok = true

def known_spec : Prop :=
  specFrom KnownT.spec.params = some (KnownT.par, KnownT.spec) ∧
  specFrom KnownR.spec.params = some (KnownR.par, KnownR.spec) ∧
  specFrom KnownP.spec.params = some (KnownP.par, KnownP.spec) ∧
  specFrom KnownF.spec.params = some (KnownF.par, KnownF.spec)

def theirs_spec : Prop :=
  Theirs.specTiny.ok = true ∧ Theirs.specFull.ok = true ∧
  specFrom Theirs.specTiny.params = some (Theirs.sizesTiny, Theirs.specTiny) ∧
  specFrom Theirs.specFull.params = some (Theirs.sizesFull, Theirs.specFull)

end Spec
end M1
end Fmt
