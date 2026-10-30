-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsCoreProofs.lean: one of the four main statements of Run/PageIs.lean, `pi_core` (F2), is
proved; and the statement of Run/PageIsCore.lean, `core_lax`.

1. What the file contains. Theorems only.

2. What is checked when the file compiles. The proofs; there are no tests (#guard) here.

3. Theorems. `pi_core`, `roots_HO`, `core_lax`.

4. What is not claimed. All that the heads of Run/PageIs.lean and Run/PageIsCore.lean leave out.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PageIsCore
import Run.StrictDomProofs
import Run.PageIsStrict2

set_option autoImplicit false

namespace Run.PQ

theorem pi_core : Spec.pi_core := core_of pi_formula pi_facts pi_strict1 pi_strict2

/-- On a small file (`hs`) the test on roots is the same at the format's hash and at its oracle. -/
theorem roots_HO (S : _root_.Fmt.Spec) (file : ByteArray) (hs : smallB S file = true) :
    rootsDiffer (_root_.Fmt.HO _root_.Fmt.oracle) S file = rootsDiffer _root_.Fmt.formatHash S file := by
  unfold rootsDiffer
  rw [laxWhole_dom (h := _root_.Fmt.formatHash) (h' := _root_.Fmt.HO _root_.Fmt.oracle)
      (fun n t i s b hd => _root_.Fmt.HO_oracle n t i s b hd)
      (fun n t i s b => _root_.Fmt.size_H n t i s b) S file hs]

theorem core_lax : Spec.core_lax := fun S dec file hok hF hd => by
  have hs : smallB S file = true := (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hF).1).1
  have h1 : decide (runLaxSP S dec file = .accepted) =
      _root_.Fmt.verify S (fun (_ : Unit) => dec) () file :=
    ((run_lax S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file hok hs).trans
        (pi_core _ S _ _ _ dec file (fit_pull S hok) ((roots_HO S file hs).trans hd))).trans
      (strict_HO Unit S (fun _ => dec) () file hF)
  exact ⟨h1, by rw [run_two S dec file hok hs]; exact h1⟩

end Run.PQ
