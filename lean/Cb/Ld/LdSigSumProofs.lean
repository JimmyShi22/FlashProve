-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSigSumProofs.lean: the proofs of the statements of Cb/Ld/LdSigSum.lean (two signatures side
by side; the sending of a family to a statement that has oracle messages already).
Nothing is defined here that a statement reads.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigSum
import Cb.Ld.LdSendFamProofs
import Ior.FrameProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (E : Type) [Field E]

theorem sigSum_cf : Spec.sigSum_cf E := fun _ _ _ _ =>
  ⟨fun h => ⟨fun a => h (.inl a), fun a => h (.inr a)⟩, fun h a => match a with
    | .inl a => h.1 a
    | .inr a => h.2 a⟩

theorem sigSum_decs : Spec.sigSum_decs E := fun _ _ _ _ => ⟨fun _ => rfl, fun _ => rfl⟩

theorem sigSum_step : Spec.sigSum_step E := by
  intro S N Kc St Wp Wp' E₀ A bk
  have hon : ∀ (x : (St × S.Smp) × N.Smp) (y : ((E₀.prod S.ext).prod N.ext).Str),
      ((S.sum N).over (S.grow N A bk)).on
        ((x.1.1, S.join N (T := OMsg.Smp) x.1.2 x.2), (S.mergeE N E₀).map y) →
      (N.over (N.pull (S.over A) (S.backN N bk))).on (x, y) :=
    fun x y h => ⟨fun a => h.1 (.inr a), fun a => h.1 (.inl a), h.2⟩
  exact
    { isLocal := by
        intro y y' q h
        rcases q with p | ⟨a | a, x⟩
        · have := h (Sum.inl (Sum.inl p)) (Finset.mem_singleton_self _)
          exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj this))
        · have := h (Sum.inl (Sum.inr ⟨a, x⟩)) (Finset.mem_singleton_self _)
          have h2 : (⟨a, (S.om a).C.T ((S.om a).upW (y.1.2 a)) x⟩ : S.ext.Sym) =
              ⟨a, (S.om a).C.T ((S.om a).upW (y'.1.2 a)) x⟩ :=
            Sum.inr.inj (Sum.inl.inj this)
          have h3 := eq_of_heq (Sigma.mk.inj h2).2
          exact congrArg (fun s => (Sum.inr ⟨Sum.inl a, s⟩ : (E₀.prod (S.sum N).ext).Sym)) h3
        · have := h (Sum.inr ⟨a, x⟩) (Finset.mem_singleton_self _)
          have h2 : (⟨a, (N.om a).C.T ((N.om a).upW (y.2 a)) x⟩ : N.ext.Sym) =
              ⟨a, (N.om a).C.T ((N.om a).upW (y'.2 a)) x⟩ := Sum.inr.inj this
          have h3 := eq_of_heq (Sigma.mk.inj h2).2
          exact congrArg (fun s => (Sum.inr ⟨Sum.inr a, s⟩ : (E₀.prod (S.sum N).ext).Sym)) h3
      acc := by
        intro x y w h
        obtain ⟨hEN, hAN, hES, hAS, hA⟩ := h
        refine ⟨rfl, fun a => ?_, fun a => ?_, hA⟩
        · rcases a with a | a
          · exact hES a
          · exact hEN a
        · rcases a with a | a
          · exact hAS a
          · exact hAN a
      onOut := fun _ _ _ _ _ => trivial
      keeps := fun _ _ => rfl
      know := by
        intro x y x' w' _ hx hw
        obtain rfl : (x.1.1, S.join N (T := OMsg.Smp) x.1.2 x.2) = x' := Option.some.inj hx
        rcases hw with hw | hn
        · exact Or.inl ⟨fun a => hw.1 (.inr a), fun a => hw.1 (.inl a), hw.2⟩
        · refine Or.inr fun h => hn ⟨fun a => ?_, h.2.2⟩
          rcases a with a | a
          · exact h.2.1 a
          · exact h.1 a }

theorem ldSendSig_good : Spec.ldSendSig_good E := by
  intro S N Sd Kc St Wp Wp' E₀ A bk D L t hC hF hL hE hD hB hZ
  have g := ldSendFam_good E N Sd Kc (St × S.Smp) (S.Wit × Wp) (S.Wit × Wp') (E₀.prod S.ext)
    (S.over A) (S.backN N bk) D L t hC hF hL hE hD hB hZ
  exact good_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ w => S.splitW N Wp' w)
    (fun (y : (E₀.prod S.ext).Str) (o : Orcs (N.sh Sd)) =>
      ((y, fun a p => o (Sum.inl ⟨a, p⟩)) : ((E₀.prod S.ext).prod N.ext).Str))
    g (sigSum_step E S N Kc St Wp Wp' E₀ A bk) fun _ _ => rfl

theorem ldSendSig_goodT :
    Spec.ldSendSig_goodT E := fun S N Sd Kc St Wp Wp' E₀ A bk D L t hC hF hL hE hD hB hZ =>
  goodT_of_good _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldSendSig_good E S N Sd Kc St Wp Wp' E₀ A bk D L t hC hF hL hE hD hB hZ)

theorem ldSendSig_chain :
    Spec.ldSendSig_chain E := fun S N Sd Kc St Wp Wp' E₀ A bk D L t hC hF hL hE hD hB hZ =>
  (goodT_cf_in _ _ _ _ _ _ _ _ _ (S.over A) ((S.sum N).over (S.grow N A bk)) _ _).1
    (ldSendSig_goodT E S N Sd Kc St Wp Wp' E₀ A bk D L t hC hF hL hE hD hB hZ)

end
end Cb
