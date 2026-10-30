-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/FreshJoinProofs.lean: the proofs of the statements of Ior/FreshJoin.lean.

Limits: see Limits in the head of Ior/FreshJoin.lean.
-/
import Ior.FreshJoin
import Ior.KnowCollRulesMaskProofs

set_option autoImplicit false

namespace Iop
open IOR Prob

theorem fresh_join : Spec.fresh_join := by
  intro Xi Xo Ei Eo R Wi Wo H Ri bud Kc kc M₁ M₂ _ _ _ _ put₁ put₂ h₁ h₂ x y w hR ρ hρ T hT
  have e₁ := h₁ x y w hR ρ hρ T hT
  have e₂ := h₂ x y w hR ρ hρ T hT
  -- an independent M₁ beside both sides of the second equation; then overwrite by it
  have e₃ := congrArg
    (PMF.map fun z : (View R × Xo × Kc) × M₁ => (z.1.1, z.1.2.1, put₁ z.2 z.1.2.2))
    (MaskKit.map_pair_indep (β := M₁) _ _ e₂)
  rw [PMF.map_comp, PMF.map_comp] at e₃
  refine Eq.trans ?_ (e₃.trans e₁)
  exact MaskKit.map_unif_of_equiv
    (⟨fun a => ((a.1, a.2.2), a.2.1),
      fun b => (b.1.1, (b.2, b.1.2)),
      fun _ => rfl,
      fun _ => rfl⟩ : H.Coin × (M₁ × M₂) ≃ (H.Coin × M₂) × M₁)
    (fun a : (H.Coin × M₂) × M₁ =>
      ((H.seen kc w x ρ T a.1.1).1,
        (H.seen kc w x ρ T a.1.1).2.1,
        put₁ a.2 (put₂ a.1.2 (H.seen kc w x ρ T a.1.1).2.2)))

theorem fresh_join_seq : Spec.fresh_join_seq := fun X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ Ra Rb b₁ b₂ K₂ K₃ kc₂ kc₃ M₁ M₂ _ _ _ _ put₁' put₁ put₂ hA h₁ hB h₂ =>
  fresh_join _ _ _ _ _ _ _ (H₁.seq H₂) Ra (budSeq R₁ R₂ b₁ b₂) K₃ kc₃ M₁ M₂ put₁ put₂
    (fresh_seq X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ Ra b₁ b₂ K₂ K₃ kc₂ kc₃ M₁ put₁' put₁ h₁ hB)
    (fresh_snd X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ Ra Rb b₁ b₂ K₃ kc₃ M₂ put₂ hA h₂)

end Iop
