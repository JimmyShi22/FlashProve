-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2SpecKnown.lean: the second toy, at the two descriptions at which the programs' own files are
judged (Fmt/M2Theirs.lean: Theirs.specTiny, 58 rounds; Theirs.specFull, 76 rounds). The conditions
that do not look at a file (Spec.ok) hold, as a theorem.

The second toy is a chain of three links. "The programs" are the C++ implementation that comes with
this Lean code; "the format page" is docs/format/FORMAT.md, which comes with the programs.
The head of Fmt/M2ParOfLaws.lean says what the toy, the sizes, a description and spelling are.

Why. Spec.ok at these descriptions is also a test (#guard) of Fmt/M2Theirs.lean, an evaluation that
leaves no theorem. The file is a companion of known_ok in Fmt/M1SpecKnown.lean.

1. What the file contains. One statement with its proof, and two lemmas that the proof uses
(`ok_tiny`, `ok_full`). No Mathlib.

2. What is checked when the file compiles. Nothing beyond the proof.

3. Theorems.
   theirs_ok   Theirs.specTiny.ok = true ∧ Theirs.specFull.ok = true.
   How. Thirteen of the fourteen clauses of Spec.ok (Fmt/Rules8Ok.lean) by the kernel, each by
   itself. The second (the parameter bytes begin with version, plan and digest of the public files)
   by params_head of Fmt/M1SpecKnownProofs.lean, which holds of every plan, digest and items.

4. What is not claimed. Nothing is claimed on a file. It is not claimed that Spec.ok is all that the
format page asks of a description. That the sizes and the description come back from the parameter
bytes (the first toy's par_back, read_back, spec_back) is not in this file. The second toy's
statements of these names are in Fmt/M2ParOfLaws.lean, under the hypotheses stated there. The
readers are in Fmt/M2ParOf.lean. At these two descriptions the statements are in
Fmt/M2SpecBack.lean (`theirs_read`, `theirs_spec`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1SpecKnownProofs
import Fmt.M2Theirs

namespace Fmt
namespace M2

def Spec.theirs_ok : Prop := Theirs.specTiny.ok = true ∧ Theirs.specFull.ok = true

theorem ok_tiny : Theirs.specTiny.ok = true :=
  (_root_.Fmt.ok_iff Theirs.specTiny).mpr
    ⟨by decide +kernel, M1.params_head _ _ _, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem ok_full : Theirs.specFull.ok = true :=
  (_root_.Fmt.ok_iff Theirs.specFull).mpr
    ⟨by decide +kernel, M1.params_head _ _ _, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem theirs_ok : Spec.theirs_ok := ⟨ok_tiny, ok_full⟩

end M2
end Fmt
