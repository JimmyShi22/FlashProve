-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1ParOfTheirs.lean: the first toy, at the two descriptions at which the programs' own files are
judged (Fmt/M1TheirsSpec.lean: `Theirs.specTiny`, `Theirs.specFull`). The sizes that the decision
takes are those that are read out of the description's own parameter bytes. A theorem, not a test.
"Theirs": the programs' own two sets of parameters.

The first toy is a product test. "The programs" are the C++ implementation that comes with this Lean
code; "the format page" is docs/format/FORMAT.md, which comes with the programs.
The sizes (`Par`, Fmt/M1Types.lean) are the toy's parameters, an argument of the verifier's decision
(`dec`, Fmt/M1All.lean). A description (`Fmt.Spec`, Fmt/Rules8.lean) is the data at which a proof
file is read. More on these words: the head of Fmt/M1ParOfLaws.lean.

Why it matters most here. The format page asks that whatever a verifier's decision reads, beside the
two parties' messages, is read out of the items of its chain's first query or computed from them.
The runs and theorems on files from outside stand at (Theirs.spec.., dec Theirs.sizes..). With
this theorem the sizes in "dec" are what the bytes that are hashed into the chain's first value say.

1. What the file contains. One statement and its proof. No Mathlib.

2. What is checked when the file compiles. Nothing beyond the proof.

3. Theorems.
   `theirs_read` (statement `Fmt.M1.Spec.theirs_read`): the sizes read out of the parameter bytes of
     `Theirs.specTiny` are `Theirs.sizesTiny`, and those of `Theirs.specFull` are
     `Theirs.sizesFull`.
   The files at the tiny parameters with a repeated position (Fmt/M1ProgPRFiles.lean) have the tiny
     parameters' bytes and are judged at `Theirs.specTiny` too. So the two descriptions cover all
     three sets of files.
   How. `known_T` and `known_F` of Fmt/M1TheirsSpec.lean (these descriptions and sizes are those of
     Fmt/M1PlanKnownT.lean and Fmt/M1PlanKnownF.lean, by definition) carry `known_read` of
     Fmt/M1ParOfKnown.lean over. No hash and no reader is evaluated.

4. What is not claimed.
   The same for the whole description is not in this file (`spec_back` of Fmt/M1ParOfLaws.lean asks
     for `Spec.ok`): see Fmt/M1SpecKnown.lean.
   That the parameter bytes of these descriptions are the bytes that came with the programs' files
     is a test elsewhere (Fmt/M1Theirs.lean; an evaluation; it hashes the public file), not a
     theorem.
   It is not claimed that a verifier compares the item "configuration" with the digest of the public
     file's text.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1ParOfKnown
import Fmt.M1TheirsSpec

namespace Fmt
namespace M1

def Spec.theirs_read : Prop :=
  (paramsRead Theirs.specTiny.params).bind parOf = some Theirs.sizesTiny ∧
  (paramsRead Theirs.specFull.params).bind parOf = some Theirs.sizesFull

theorem theirs_read : Spec.theirs_read :=
  ⟨by rw [← known_T.1, ← known_T.2]; exact known_read.1,
    by rw [← known_F.1, ← known_F.2]; exact known_read.2.2.2⟩

end M1
end Fmt
