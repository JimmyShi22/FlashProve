-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/HomProofs.lean: the proofs of the two statements of Run/Hom.lean.

Main names (statements and hypotheses: Run/Hom.lean):
  `hom_foldlM`: a morphism of monads (`Hom`) passes through `List.foldlM`.
  `cost_foldlM`: for a count of questions c (`Cost`), if each step asks at most t, the loop over l
    asks at most l.length * t.
What a count says depends on the instance c: Run/Hom.lean, the head, Limits.
-/
import Run.Hom

set_option autoImplicit false

namespace Run

theorem hom_foldlM : Spec.hom_foldlM := by
  intro m n _ _ φ α β g l
  induction l with
  | nil => intro b; exact φ.app_pure b
  | cons a l ih =>
    intro b
    simp only [List.foldlM_cons, φ.app_bind, ih]

theorem cost_foldlM : Spec.cost_foldlM := by
  intro m _ c α β g t hg l
  induction l with
  | nil => intro b; exact c.le_mono _ 0 _ (c.le_pure b) (Nat.zero_le _)
  | cons a l ih =>
    intro b
    simp only [List.foldlM_cons]
    exact c.le_mono _ _ _ (c.le_bind _ _ t (l.length * t) (hg b a) ih)
      (by rw [List.length_cons, Nat.succ_mul, Nat.add_comm]; exact Nat.le_refl _)

end Run
