-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowRulesProofs.lean: the proofs of the statements of Ior/KnowRules.lean: knowledge soundness of
a reduction beside a carried part, of a step without rounds, and at joints whose condition may fail.

Proofs only.
Main names: `know_beside`, `onOut_beside`, `know_pure`, `onOut_pure`, `know_cf`.
Limits: see Limits in the head of Ior/KnowRules.lean.

-/
import Ior.KnowRules
import Ior.KnowCollRulesFrameProofs

set_option autoImplicit false

namespace Iop
open IOR Reduction

theorem know_beside : Spec.know_beside := by
  intro K Xi Xo Z Ei Eo F R Wi Wo Wz A B ext ε S h a ha
  refine Doomed.mono _ _ ?_ (h (a.1.1, a.2.1) ha.1)
  intro τ hτ b w hb hw
  obtain ⟨e2, hb'⟩ := keepE_red_out (R.keepX Z) F a τ b hb
  obtain ⟨e1, hb''⟩ := keepX_red_out R Z _ τ _ hb'
  refine ⟨hτ (b.1.1, b.2.1) w.1 hb'' hw.1, ?_⟩
  show S.relR (a.1.2, a.2.2) w.2
  rw [← e2, ← (show b.1.2 = a.1.2 from e1)]
  exact hw.2

theorem onOut_beside : Spec.onOut_beside := by
  intro K Xi Xo Z Ei Eo F R Wi Wo Wz A B S h a τ b ha hb
  obtain ⟨e2, hb'⟩ := keepE_red_out (R.keepX Z) F a τ b hb
  obtain ⟨e1, hb''⟩ := keepX_red_out R Z _ τ _ hb'
  refine ⟨h (a.1.1, a.2.1) τ (b.1.1, b.2.1) ha.1 hb'', ?_⟩
  show S.on (b.1.2, b.2.2)
  rw [e2, (show b.1.2 = a.1.2 from e1)]
  exact ha.2

theorem know_pure : Spec.know_pure := by
  intro Xi Xo Ei Eo f g Wi Wo on RA RB back ε h a ha b w hb hw
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  rw [show b = (b.1, g.map a.2) from Prod.ext rfl h2] at hw
  exact h a b.1 w ha h1 hw

theorem onOut_pure : Spec.onOut_pure := by
  intro Xi Xo Ei Eo f g on on' h a τ b ha hb
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  rw [show b = (b.1, g.map a.2) from Prod.ext rfl h2]
  exact h a b.1 ha h1

theorem know_cf : Spec.know_cf := by
  intro K Xi Xo Ei Eo R Wi Wo A B ext ε h ho
  exact (knowInto_iff _ _ _ _ _ _ _ _ _ _ _).1
    (knowInto_of_carry _ _ _ _ _ _ _ _ _ _ _ (fun a τ b hb ha => ho a τ b ha hb) h)

end Iop
