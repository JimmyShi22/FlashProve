-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontOnProofs.lean: the proofs of the statements of Cb/Ld/LdFrontOn.lean.

Main names (statements and hypotheses: Cb/Ld/LdFrontOn.lean):
  `frontOn_keys`: the keys, from conditions at the front's two ends.
  `frontOn_forget`: the annotated links of `Front.onV` are `p.cA true`.
  `frontOn_sh`: see its statement in Cb/Ld/LdFrontOn.lean.
`Front.on1`: nil ; the splitting ; the step without rounds (Cb/Ld/LdFrontOn.lean, under "The
front.").

Limits: what the head of Cb/Ld/LdFrontOn.lean lists as not said is not said here either.
-/
import Cb.Ld.LdFrontOn
import Cb.Ld.LdFrontVProofs
import Cb.Ld.LdLinClosePlanSProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Front

section
variable (E : Type) [Field E] [Fintype E]

theorem frontOn_keys : Spec.frontOn_keys E := by
  intro S E₀ Wp G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f N kx kz F h
  unfold Front.on1
  rw [Keys]
  refine ⟨⟨kz.κ, fun b => kz.key ((f b.1.1, b.1.2), (sideG S (ExtMap.id E₀)).map b.2)⟩, ?_, id, ?_⟩
  · rw [Keys]
    refine ⟨kx, ?_, fun κ' τ => F κ' (said τ), ⟨fun e => Bool.noConfusion e, ?_⟩⟩
    · rw [Keys]
      exact ⟨id, fun _ => rfl⟩
    · rintro a τ b hb
      obtain rfl := Option.some.inj hb
      exact h a (said τ)
  · rintro a τ b hb
    obtain rfl := Option.some.inj hb
    rfl

theorem frontOn_forget :
    Spec.frontOn_forget
      E := fun S E₀ Wp G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f N W0 t₁ q rd t₃ =>
  frontV_forgetSh E S E₀ Wp G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z (sideF S f)
    (sideG S (ExtMap.id E₀)) (sideM S f fun _ w => w.2) (sideB S fun _ w => w.2) N W0 t₁ q rd _ t₃ q

theorem frontOn_sh : Spec.frontOn_sh E := by
  intro S E₀ Wp G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs z f N W0 t₁ q rd xp₀
    t₃ Z VZ c₀ hH hq hrd h3 hF
  unfold Front.on1 at hH
  rw [prog_step, LdProg.hyp_snoc, prog_split, LdProg.hyp_snoc] at hH
  have hT := (Chain.allT_one _).1
    (ldSeg_mvT E Unit _ _
      (LdMv.step
        (⟨_, (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).tgt.A⟩ : FSt S E₀ Wp Unit).stage z.stage
        (sideF S f) (sideG S (ExtMap.id E₀)) (sideM S f fun _ w => w.2) (sideB S fun _ w => w.2))
      hH.2 (by intro e; cases e) (by intro e; cases e))
  refine frontV_sh E (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs) N W0 t₁ q rd xp₀ _ _ _ t₃ q Z VZ
    c₀ hH.1.2 hT (fun _ _ => rfl) hq hq hrd (fun x y w h => ⟨x, h, rfl⟩) ?_ ?_ hF
  · rintro x' y w _ _ ⟨_, x, hx, rfl⟩ _
    exact h3 x y w hx
  · intro Jn ρ Us h
    refine ⟨fun _ => trivial, ?_⟩
    have e : (fun j : Jn =>
          (IOR.pure (sideF S f) (sideG S (ExtMap.id E₀))).need (ρ.slot j.1) (Us j)) = Us :=
      funext fun j => by rw [need_pure, sideG_id_src]
    show q Jn fun j => (IOR.pure (sideF S f) (sideG S (ExtMap.id E₀))).need (ρ.slot j.1) (Us j)
    rw [e]
    exact h

end
end Cb
