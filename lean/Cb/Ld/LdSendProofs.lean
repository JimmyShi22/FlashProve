-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendProofs.lean: the proofs of the statements of Cb/Ld/LdSend.lean (the sending of an oracle
message with its sample, as an interactive oracle reduction).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The order. The data; completeness; the bad seeds, the condition on the output, the backward step,
knowledge soundness in both forms; the two lemmas on the law of the answers; locality; exact
honest-verifier zero knowledge; the bundles.
Nothing is defined here that a statement reads.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSend
import Cb.Ld.LdSigProofs
import Cb.Gen.OodDecSendProofs
import Cb.Gen.CodeProofs
import Prob.LawKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

section
variable (E : Type) [Field E]

theorem ldSend_data : Spec.ldSend_data E := by
  classical
  intro o X E₀
  refine ⟨rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, fun _ q => ⟨rfl, fun _ => Finset.mem_image⟩,
    fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩⟩
  rintro ⟨a, ⟨⟩, ⟨⟩⟩ ⟨b, ⟨⟩, ⟨⟩⟩ h
  exact congrArg (fun c : o.Z.D => ((c, (), ()) : Rho o.sh)) h

theorem ldSend_acc : Spec.ldSend_acc E := by
  intro o Kc X W W' E₀ A back D hD x y w c ρ hR _
  obtain ⟨ρ₁, u, u'⟩ := ρ
  refine ⟨rfl, hD.enc _ _, rfl, ?_⟩
  show A.rel x y (back (D.upM (D.put w c.1)) (D.rest w))
  rw [hD.back]
  exact hR

theorem ldSend_within : Spec.ldSend_within E := fun o L hL hE =>
  ⟨fun m => (sig_cnt_clash E o L hL hE m.1).1,
    fun _ _ => ⟨fun _ => le_of_eq (cnt_false fun _ h => h), fun _ _ => trivial⟩⟩

theorem ldSend_out_on : Spec.ldSend_out_on E := by
  intro o Kc X W W' E₀ A back a τ b ha hc hb
  obtain ⟨⟨g, u₀⟩, ρ, ⟨u₁, ans⟩, c, u₂⟩ := τ
  obtain rfl : ((a.1, (ρ, ans)), (a.2, g)) = b := Option.some.inj hb
  exact ⟨ha, hc.1⟩

theorem ldSend_back : Spec.ldSend_back E := by
  intro o Kc X W W' E₀ A back a τ b w hb hw
  obtain ⟨⟨g, u₀⟩, ρ, ⟨u₁, ans⟩, c, u₂⟩ := τ
  obtain rfl : ((a.1, (ρ, ans)), (a.2, g)) = b := Option.some.inj hb
  exact hw.2

theorem ldSend_into : Spec.ldSend_into E := by
  intro o Kc X W W' E₀ A back L hL hE
  exact knowInto_of_badFam _ _ _ _ (ldSend o X E₀).red A.on (o.sent A back).on A.relR
    (o.sent A back).relR _ _ (fun _ => ldSendBad o) (fun _ _ => ldSend_within E o L hL hE)
    (fun a τ b ha hc hb => ldSend_out_on E o Kc X W W' E₀ A back a τ b ha hc hb)
    fun a τ b w _ _ hb hw => ldSend_back E o Kc X W W' E₀ A back a τ b w hb hw

theorem ldSend_literal : Spec.ldSend_literal E := by
  classical
  intro o Kc X W W' E₀ A back L hL hE a ha
  refine ⟨⟨fun s => decide_eq_true_iff, ?_, fun τ s => decide_eq_true_iff⟩, ?_⟩
  · intro τ m s h
    rcases τ with _ | ⟨m₁, ρ, τ'⟩
    · exact h
    · rcases τ' with _ | ⟨_, _, τ''⟩
      · exact h
      · exact τ''.elim
  · intro τ
    rcases τ with m | ⟨m₁, ρ, τ'⟩
    · refine le_trans (cnt_mono ?_) (sig_cnt_clash E o L hL hE m.1).1
      rintro ρ ⟨s, h0, h1⟩
      exact (of_decide_eq_true h1).resolve_left (of_decide_eq_false h0)
    · rcases τ' with m₂ | ⟨_, _, τ''⟩
      · refine le_of_eq (cnt_false ?_)
        rintro c ⟨s, h0, h1⟩
        obtain ⟨b, hb, hw⟩ := of_decide_eq_true h1
        have h0' := of_decide_eq_false h0
        rcases s with w | w'
        · exact hw.elim
        · rcases hw with hw | hn
          · exact h0' (Or.inl (ldSend_back E o Kc X W W' E₀ A back a (m₁, ρ, m₂, c, ()) b w' hb hw))
          · exact hn (ldSend_out_on E o Kc X W W' E₀ A back a (m₁, ρ, m₂, c, ()) b ha
                ⟨fun hcl => h0' (Or.inr hcl), fun h => h, trivial⟩ hb)
      · exact τ''.elim

theorem ldSend_blind_of_uniform [Fintype E] : Spec.ldSend_blind_of_uniform E :=
  fun _ _ _ _ h ρ w w' => (h ρ w).trans (h ρ w').symm

theorem ldSend_uniform_of_private [Fintype E] : Spec.ldSend_uniform_of_private E := by
  classical
  intro F _ _ _ o W W' D J₀ Pd Mk₀ _ _ _ _ ν κ body hput hP ρ w
  have h1 : D.ans ρ w =
      fun k =>
        (fun x : Mk₀ × (Pd → F) => (o.Z.comap ν.symm).val ρ (withPad (F := F) (body w x.1) x.2))
            (κ k) := by
    funext k
    show o.Z.val ρ (D.upM (D.put w k)) =
      (o.Z.comap ν.symm).val ρ (withPad (F := F) (body w (κ k).1) (κ k).2)
    rw [ood_val_comap E o.C.J (J₀ ⊕ Pd) o.Z ν.symm ρ]
    congr 1
    funext j
    have := hput w k (ν j)
    rw [Equiv.symm_apply_apply] at this
    exact this
  rw [h1]
  show (unif D.Mk).map
      ((fun x : Mk₀ × (Pd → F) => (o.Z.comap ν.symm).val ρ (withPad (F := F) (body w x.1) x.2)) ∘
        κ) = _
  rw [← PMF.map_comp, map_unif_equiv κ, map_unif_prod]
  have h2 : ∀ k₀ : Mk₀,
      ((unif (Pd → F)).map fun c => (o.Z.comap ν.symm).val ρ (withPad (F := F) (body w k₀) c)) =
        unif (o.Z.S → E) := fun k₀ => by
    convert hP ρ trivial (body w k₀)
  simp only [h2]
  exact PMF.bind_const _ _

end

/-! ## Locality, honest-verifier zero knowledge, the bundles -/

section
variable {E : Type} [Field E] (o : OMsg E) (X : Type) (E₀ : ExtSpec)

theorem ldSend_isLocal (hL : o.C.Laws) : (ldSend o X E₀).IsLocal where
  out := by
    intro x y y' τ τ' hρ hp _ _
    obtain ⟨⟨g, u₀⟩, ρ, ⟨u₁, ans⟩, c, u₂⟩ := τ
    obtain ⟨⟨g', u₀'⟩, ρ', ⟨u₁', ans'⟩, c', u₂'⟩ := τ'
    obtain rfl : ρ = ρ' := congrArg Prod.fst hρ
    obtain rfl : ans = ans' := congrArg (fun r : Plains o.sh => r.2.1) hp
    rfl
  imp := by
    classical
    intro y y' τ τ' q _ _ hy hτ
    rcases q with p | x
    · exact congrArg Sum.inl (hy p (Finset.mem_singleton_self p))
    · refine congrArg Sum.inr (hL.loc _ _ x fun p hp => ?_)
      exact congrArg (o.up p) (hτ (Sum.inl p) (Finset.mem_image.2 ⟨p, hp, rfl⟩))

theorem ldSend_ite_congr {α : Type} {p q : Prop} {_ : Decidable p} {_ : Decidable q} (hpq : p ↔ q)
    {a b : α} (hab : q → a = b) :
    (if p then some a else none) = if q then some b else none := by
  by_cases hq : q
  · rw [if_pos (hpq.2 hq), if_pos hq, hab hq]
  · rw [if_neg fun hp => hq (hpq.1 hp), if_neg hq]

/-- Two transcripts with the same plain parts that agree on T show the same, in this sense: they
have the same `view T`. -/
theorem ldSend_view_congr (T : Finset (OPos o.sh)) (τ τ' : Tr o.sh) (hp : τ.plains = τ'.plains)
    (hr : ∀ q ∈ ldSendSet o T, τ.1.1 q = τ'.1.1 q) :
    (ldSend o X E₀).view T τ = (ldSend o X E₀).view T τ' := by
  unfold IOR.view
  refine congrArg₂ IOR.View.mk hp ?_
  funext p
  rcases p with q | q | q
  · refine ldSend_ite_congr Iff.rfl fun hx => ?_
    have hq : (Sum.inl q : OPos o.sh) ∈ T :=
      hx.elim (fun h3 => absurd h3 (Finset.notMem_empty _)) fun h3 =>
        h3.elim id fun h4 => Bool.noConfusion h4
    exact hr q (Finset.mem_toLeft.2 hq)
  · exact q.elim
  · exact q.elim

end

section
variable (E : Type) [Field E]

theorem ldSend_exactWith : Spec.ldSend_exactWith E := by
  classical
  intro o X W W' E₀ D t Ri hB hZ x y w _ ρ _ T hT
  obtain ⟨ρ₁, u, u'⟩ := ρ
  have h1 : (ldSendHon X E₀ D).output w x (ρ₁, u, u') T =
      (unif (D.Mk × D.N.Rnd)).map fun c =>
        some ((ldSend o X E₀).view T (((ldSendHon X E₀ D).strat w x c).run (ρ₁, u, u')).1) :=
    if_neg fun h => h.elim id id
  refine h1.trans ?_
  show _ = (unif (D.Mk × D.N.Rnd)).map fun c =>
      some ((ldSend o X E₀).view T (((ldSendHon X E₀ D).strat D.w0 x c).run (ρ₁, u, u')).1)
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq _ _ (hB ρ₁ w D.w0)
  refine map_unif_prod_congr σ _ _ fun k => ?_
  obtain ⟨e₂, he₂⟩ :=
    (hides_iff_equiv _ D.N (o.C.budT t)).1 hZ (ldSendSet o T) hT (D.put w k) (D.put D.w0 (σ k))
  refine map_unif_reindex e₂ _ _ fun r => congrArg some ?_
  refine ldSend_view_congr o X E₀ T _ _ ?_ fun q hq => ?_
  · exact congrArg (fun a : o.Z.S → E => (((), (a, ())) : Plains o.sh)) (hσ k)
  · exact eq_of_heq (Sigma.mk.inj (he₂ r q hq)).2

theorem ldSend_goodT : Spec.ldSend_goodT E := by
  intro o Kc X W W' E₀ A back D L t hC hL hE hD hB hZ
  exact
    { point := ⟨o.pt⟩
      isLocal := ldSend_isLocal o X E₀ hC
      acc := ldSend_acc E o Kc X W W' E₀ A back D hD
      onOut := fun _ _ _ _ _ => trivial
      keeps := fun w x c ρ => congrArg A.core (hD.back w c.1)
      prBad := prRho_empty _ fun _ h => h
      cover := fun _ _ => Set.empty_subset _
      prCov := fun _ => prRho_empty _ fun _ h => h
      know := ldSend_into E o Kc X W W' E₀ A back L hL hE
      exact := ⟨ldSendSim X E₀ D, ldSend_exactWith E o X W W' E₀ D t _ hB hZ⟩ }

theorem ldSend_good : Spec.ldSend_good E := fun o Kc X W W' E₀ A back D L t hC hL hE hD hB hZ =>
  good_of_goodT _ _ _ _ _ _ _ _ _ _ _ (fun _ _ (w : o.Wit × W') => back w.1.1 w.2) _
    (ldSend_goodT E o Kc X W W' E₀ A back D L t hC hL hE hD hB hZ)

theorem ldSend_chain : Spec.ldSend_chain E := fun o Kc X W W' E₀ A back D L t hC hL hE hD hB hZ =>
  (goodT_cf_in _ _ _ _ _ _ _ _ _ A (o.sent A back) _ _).1
    (ldSend_goodT E o Kc X W W' E₀ A back D L t hC hL hE hD hB hZ)

end
end Cb
