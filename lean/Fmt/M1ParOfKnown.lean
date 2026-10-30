-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1ParOfKnown.lean: the first toy, at the four descriptions of this library's own Python
reference program's sets of files. The sizes that the decision takes are those that are read out of
the description's own parameter bytes. Theorems, not tests.

The first toy is a product test. "The programs" are the C++ implementation that comes with this Lean
code; "the format page" is docs/format/FORMAT.md, which comes with the programs.
The sizes (`Par`, Fmt/M1Types.lean) are the toy's parameters, an argument of the verifier's decision
(`dec`, Fmt/M1All.lean). A description (`Fmt.Spec`, Fmt/Rules8.lean) is the data at which a proof
file is read; its parameter bytes are hashed into the first value of the hash chain. More on these
words: the head of Fmt/M1ParOfLaws.lean.

1. What the file contains.
   `itemsFit P`: every one of the four items of the sizes has a name that fits and a value of fewer
     than 2^64 bytes. (A test that can be run.)

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems (statements `Fmt.M1.Spec.read_at`, `known_read`, with their proofs). No Mathlib.
   `read_at`: for all sizes P, every number nonceB and every list of public files: `P.small`,
     `(planOf P nonceB).fit`, `itemsFit P` → at
     `S := specOf P (configDigest files) (itemsOf P) nonceB`:
     `(paramsRead S.params).bind parOf = some P`.
   `known_read`: at the (`spec`, `par`) of Fmt/M1PlanKnownT.lean, Fmt/M1PlanKnownR.lean,
     Fmt/M1PlanKnownP.lean and Fmt/M1PlanKnownF.lean:
     `(paramsRead spec.params).bind parOf = some par`.
   How. `read_at` is `read_back` of Fmt/M1ParOfLaws.lean. That the digest of the public files has 32
     bytes is a law on the length of the hash (Fmt/Rules23Laws.lean, `size_H`): no hash is
     evaluated. The three tests at the two sets of sizes (the tiny parameters: T, R and P have the
     same; the full parameters) are theorems by the kernel's own evaluation.

4. What is not claimed.
   The same for the whole description is not in this file. `spec_back` asks that `Spec.ok` holds. At
     these four descriptions that is a theorem, stated in Fmt/M1SpecKnown.lean and proved in
     Fmt/M1SpecKnownProofs.lean.
   Nothing on the public file's text, or on how sizes follow from it.
   Not here: the descriptions at which files from outside are judged (Fmt/M1TheirsSpec.lean:
     `Theirs.specFull`, `Theirs.specTiny`, written from the sizes and the public file; a test there
     compares them with what is read out of the programs' own parameter bytes), although there the
     fact matters most: see Fmt/M1ParOfTheirs.lean.
     `read_at` serves as it is, under its hypotheses, wherever such a description is `specOf` of
     sizes at the digest of a public file and at the items `itemsOf` of these sizes.
     Where Fmt/M1TheirsSpec.lean shows such a description equal to one of these four (`known_T`,
     `known_F`), `known_read` carries over.
   That the parameter bytes of these four descriptions are the programs' is checked elsewhere, by
     tests (#guard), not proved.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1ParOfLawsProofs
import Fmt.Rules23Laws
import Fmt.M1PlanKnownT
import Fmt.M1PlanKnownR
import Fmt.M1PlanKnownP
import Fmt.M1PlanKnownF

namespace Fmt
namespace M1

def itemsFit (P : Par) : Bool := (itemsOf P).all fun x => nameFit x.1 && decide (x.2.size < 2 ^ 64)

namespace Spec

def read_at : Prop :=
  ∀ (P : Par) (nonceB : Nat) (files : List ByteArray), P.small = true →
    (planOf P nonceB).fit = true → itemsFit P = true →
    (paramsRead (specOf P (configDigest files) (itemsOf P) nonceB).params).bind parOf = some P

def known_read : Prop :=
  (paramsRead KnownT.spec.params).bind parOf = some KnownT.par ∧
  (paramsRead KnownR.spec.params).bind parOf = some KnownR.par ∧
  (paramsRead KnownP.spec.params).bind parOf = some KnownP.par ∧
  (paramsRead KnownF.spec.params).bind parOf = some KnownF.par

end Spec

theorem size_configDigest (files : List ByteArray) : (configDigest files).size = 32 :=
  size_H 169 0 2 zero32 (configBytes files)

theorem read_at : Spec.read_at := by
  intro P nonceB files h1 h2 h3
  refine read_back P _ nonceB h1 ?_
  show ((planOf P nonceB).fit && (configDigest files).size == 32 && itemsFit P) = true
  rw [h2, h3, size_configDigest]; rfl

theorem known_read : Spec.known_read :=
  ⟨read_at KnownT.par 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    read_at KnownR.par 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    read_at KnownP.par 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel),
    read_at KnownF.par 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

end M1
end Fmt
