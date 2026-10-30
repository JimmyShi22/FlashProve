-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2SpecBack.lean: the second toy, at the two descriptions at which the programs' own files are
judged (Fmt/M2Theirs.lean: Theirs.specTiny, Theirs.specFull). From the parameter bytes alone the
sizes and the whole description come back.

The second toy is a chain of three links. "The programs" are the C++ implementation that comes with
this Lean code. The file is a companion of theirs_spec in Fmt/M1SpecKnown.lean.
The head of Fmt/M2ParOfLaws.lean says what the toy, the sizes, a description and spelling are.

1. What the file contains. Two statements with their proofs, and three lemmas on the way to them
(`fit_at`, `fit_tiny`, `fit_full`). No Mathlib. Many statements of this library are written twice: a
definition in the namespace `Spec` states a proposition, and a theorem of the same name outside that
namespace proves it (lean/GLOSSARY.md).

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems (statements Fmt.M2.Spec.*).
   theirs_read   paramsRead, then parOf, on Theirs.specTiny.params and on Theirs.specFull.params
     give some tinyPar and some toyPar.
   theirs_spec   specFrom Theirs.specTiny.params = some (tinyPar, Theirs.specTiny), and the same at
     specFull with toyPar.
   How. The proofs apply read_back and spec_back (stated in Fmt/M2ParOfLaws.lean, proved in
   Fmt/M2ParOfLawsProofs.lean). Their tests on the sizes are decided by the kernel. Spec.ok (of the
   record `Spec`, Fmt/Rules8.lean) is theirs_ok of Fmt/M2SpecKnown.lean.

4. What is not claimed.
   These are the bytes that Lean spells from the sizes and the public file. That they are the
   programs' own bytes (Theirs.tiny, Theirs.full) is a test (#guard) of Fmt/M2Theirs.lean, not a
   theorem.
   Nothing is claimed on a file. It is not claimed that the sizes follow from the public file.

Notation: 8: nonceB, the bytes of a nonce in a file (`Plan.nonce`, Fmt/Plan.lean).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M2ParOfLawsProofs
import Fmt.M2SpecKnown

namespace Fmt
namespace M2

def Spec.theirs_read : Prop :=
  (paramsRead Theirs.specTiny.params).bind parOf = some tinyPar ∧
  (paramsRead Theirs.specFull.params).bind parOf = some toyPar

def Spec.theirs_spec : Prop :=
  specFrom Theirs.specTiny.params = some (tinyPar, Theirs.specTiny) ∧
  specFrom Theirs.specFull.params = some (toyPar, Theirs.specFull)

theorem fit_at (P : Par) (files : List ByteArray) (h2 : (planOf P 8).fit = true)
    (h3 : ((itemsOf P).all fun x => nameFit x.1 && decide (x.2.size < 2 ^ 64)) = true) :
    (theParams P (configDigest files) 8).fit = true := by
  show ((planOf P 8).fit && (configDigest files).size == 32 &&
      ((itemsOf P).all fun x => nameFit x.1 && decide (x.2.size < 2 ^ 64))) = true
  rw [h2, h3, M1.size_configDigest]; rfl

theorem fit_tiny : (theParams tinyPar (configDigest [Theirs.pubTiny]) 8).fit = true :=
  fit_at tinyPar _ (by decide +kernel) (by decide +kernel)
theorem fit_full : (theParams toyPar (configDigest [Theirs.pubFull]) 8).fit = true :=
  fit_at toyPar _ (by decide +kernel) (by decide +kernel)

theorem theirs_read : Spec.theirs_read :=
  ⟨read_back tinyPar _ 8 (by decide +kernel) fit_tiny,
    read_back toyPar _ 8 (by decide +kernel) fit_full⟩

theorem theirs_spec : Spec.theirs_spec :=
  ⟨spec_back tinyPar _ 8 (by decide +kernel) fit_tiny theirs_ok.1,
    spec_back toyPar _ 8 (by decide +kernel) fit_full theirs_ok.2⟩

end M2
end Fmt
