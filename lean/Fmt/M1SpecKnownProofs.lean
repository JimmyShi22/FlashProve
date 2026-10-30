-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1SpecKnownProofs.lean: the first toy. `Spec.ok` as a theorem at the descriptions that
Fmt/M1SpecKnown.lean names, and the description back from the parameter bytes. The proofs of the
four statements of Fmt/M1SpecKnown.lean.

The words (description, `Spec.ok`, parameter bytes) are told in the heads of Fmt/M1SpecKnown.lean
and Fmt/M1ParOfLaws.lean.

1. What the file contains. Proofs. No Mathlib.
   `take_front`: the first `a.size` bytes of `a ++ b` are a (`extract_mid` of Fmt/Rules1Laws.lean
     with nothing in front).
   `params_head`: the bytes without further items are the head and the item "configuration", with
     the empty string behind them.
   `ok_T`, `ok_R`, `ok_P`, `ok_F`: `Spec.ok` at each of the four descriptions, from its fourteen
     clauses (`ok_iff`, Fmt/Rules8Ok.lean): the second by `params_head` (that clause is too much
     for the kernel: Fmt/M1SpecKnown.lean, part 3), the thirteen others by the kernel, each by
     itself. Together: `known_ok`.
   `spec_at`: `spec_back` of Fmt/M1ParOfLaws.lean with the tests of `read_at`
     (Fmt/M1ParOfKnown.lean). From it: `known_spec`.
   `theirs_spec`: the two descriptions at which the programs' own files are judged are this
   library's T and F
     (`known_T`, `known_F`, Fmt/M1TheirsSpec.lean). "The programs" are the C++ implementation that
     comes with this Lean code.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems. `params_head`, `known_ok`, `known_spec`, `theirs_spec` (statements and hypotheses:
Fmt/M1SpecKnown.lean).

4. What is not claimed. See Fmt/M1SpecKnown.lean.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1SpecKnown

namespace Fmt
namespace M1

theorem take_front (a b : ByteArray) : (a ++ b).extract 0 a.size = a := by
  have h := extract_mid ByteArray.empty a b
  have e : ByteArray.empty ++ a = a := by
    apply ByteArray.ext
    rw [ByteArray.data_append]
    exact Array.empty_append
  rw [e] at h
  simpa using h

theorem append_nothing (a : ByteArray) : a ++ ByteArray.empty = a := by
  apply ByteArray.ext
  rw [ByteArray.data_append]
  exact Array.append_empty

theorem beq_same (a : ByteArray) : (a == a) = true := by
  cases a with
  | mk x =>
    show (x == x) = true
    exact beq_self_eq_true x

theorem params_head : Spec.params_head := by
  intro P cfg others
  have e : paramsBytes P cfg [] = paramsHead P ++ item configName cfg := by
    show paramsHead P ++ item configName cfg ++ items [] = _
    exact append_nothing _
  rw [e]
  show ((paramsHead P ++ item configName cfg ++ items others).extract
        0 (paramsHead P ++ item configName cfg).size ==
      paramsHead P ++ item configName cfg) = true
  rw [take_front]
  exact beq_same _

theorem ok_T : KnownT.spec.ok = true :=
  (_root_.Fmt.ok_iff KnownT.spec).mpr
    ⟨by decide +kernel, params_head _ _ _, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem ok_R : KnownR.spec.ok = true :=
  (_root_.Fmt.ok_iff KnownR.spec).mpr
    ⟨by decide +kernel, params_head _ _ _, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem ok_P : KnownP.spec.ok = true :=
  (_root_.Fmt.ok_iff KnownP.spec).mpr
    ⟨by decide +kernel, params_head _ _ _, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem ok_F : KnownF.spec.ok = true :=
  (_root_.Fmt.ok_iff KnownF.spec).mpr
    ⟨by decide +kernel, params_head _ _ _, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem known_ok : Spec.known_ok := ⟨ok_T, ok_R, ok_P, ok_F⟩

/-- `spec_back` (Fmt/M1ParOfLaws.lean) with the tests of `read_at` (Fmt/M1ParOfKnown.lean): for all
P, nonceB and files, at `S := specOf P (configDigest files) (itemsOf P) nonceB`, under `h1`, `h2`,
`h3` and `hok`: `specFrom S.params = some (P, S)`. -/
theorem spec_at (P : Par) (nonceB : Nat) (files : List ByteArray) (h1 : P.small = true)
    (h2 : (planOf P nonceB).fit = true) (h3 : itemsFit P = true)
    (hok : (specOf P (configDigest files) (itemsOf P) nonceB).ok = true) :
    specFrom (specOf P (configDigest files) (itemsOf P) nonceB).params =
      some (P, specOf P (configDigest files) (itemsOf P) nonceB) := by
  refine spec_back P _ nonceB h1 ?_ hok
  show ((planOf P nonceB).fit && (configDigest files).size == 32 && itemsFit P) = true
  rw [h2, h3, size_configDigest]; rfl

theorem known_spec : Spec.known_spec :=
  ⟨spec_at KnownT.par 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ok_T,
    spec_at KnownR.par 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ok_R,
    spec_at KnownP.par 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ok_P,
    spec_at KnownF.par 8 _ (by decide +kernel) (by decide +kernel) (by decide +kernel) ok_F⟩

theorem theirs_spec : Spec.theirs_spec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← known_T.2]; exact ok_T
  · rw [← known_F.2]; exact ok_F
  · rw [← known_T.1, ← known_T.2]; exact known_spec.1
  · rw [← known_F.1, ← known_F.2]; exact known_spec.2.2.2

end M1
end Fmt
