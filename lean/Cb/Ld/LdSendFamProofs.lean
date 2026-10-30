-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendFamProofs.lean: the proofs of the statements of Cb/Ld/LdSendFam.lean (the sending of
several oracle messages in one prover message).

The main one is `ldSendFam_goodT`: see its statement in Cb/Ld/LdSendFam.lean.
The order. A count under a map with small fibres; the count of bad joint seeds; independent seeds,
and one seed read in parts; then as in Cb/Ld/LdSendProofs.lean: the data, completeness, knowledge
soundness, locality, exact honest-verifier zero knowledge, the bundles.
Nothing is defined here that a statement reads.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendFam
import Cb.Ld.LdSendProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-- If every value has at most k preimages, a property of the image holds of at most k times as many
arguments. -/
theorem cnt_comp_le {C D : Type} [Fintype C] [Fintype D] (g : C → D) (P : D → Prop)
    (k : ℕ) (h : ∀ d, cnt (fun c => g c = d) ≤ k) :
    cnt (fun c => P (g c)) ≤ k * cnt P := by
  classical
  have h1 : cnt (fun c => P (g c)) ≤ cnt (fun c => ∃ d ∈ Finset.univ.filter P, g c = d) :=
    cnt_mono fun c hc => ⟨g c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩, rfl⟩
  refine h1.trans ((cnt_exists_mem_le _ _).trans ?_)
  refine (Finset.sum_le_sum fun d _ => h d).trans ?_
  rw [Finset.sum_const, smul_eq_mul, cnt_eq_card_filter, Nat.mul_comm]

section
variable (E : Type) [Field E]

theorem ldSendFam_cnt : Spec.ldSendFam_cnt E := by
  intro N Sd L hF hL hE f
  refine (cnt_exists_le _).trans (Finset.sum_le_sum fun a _ => ?_)
  exact (cnt_comp_le (Sd.sd a) ((N.om a).Clash (f a)) (Sd.mult a) (hF a)).trans
    (Nat.mul_le_mul_left _ (sig_cnt_clash E (N.om a) (L a) (hL a) (hE a) (f a)).1)

omit [Field E] in
theorem ldSendFam_fair_indep : Spec.ldSendFam_fair_indep E := by
  classical
  intro N
  have hcard : ∀ a, (∏ b ∈ Finset.univ.erase a, Fintype.card (N.om b).Z.D) *
        Fintype.card (N.om a).Z.D =
      Fintype.card (∀ a, (N.om a).Z.D) := by
    intro a
    rw [Fintype.card_pi, Nat.mul_comm]
    exact Finset.mul_prod_erase Finset.univ (fun b => Fintype.card (N.om b).Z.D) (Finset.mem_univ a)
  refine ⟨fun a ρ => ?_, hcard⟩
  have h1 := cnt_pi_coord (A := fun b => (N.om b).Z.D) a (fun x => x = ρ)
  rw [cnt_eq_const, one_mul, ← hcard a] at h1
  exact le_of_eq (Nat.eq_of_mul_eq_mul_right Fintype.card_pos h1)

omit [Field E] in
theorem ldSendFam_fair_parts : Spec.ldSendFam_fair_parts E := by
  intro N D _ _ Rst _ e
  refine ⟨fun a ρ => ?_, fun a => ?_⟩
  · have h1 : cnt (fun s : D => (e a s).1 = ρ) = cnt (fun x : (N.om a).Z.D × Rst a => x.1 = ρ) :=
      cnt_equiv (e a) fun x => x.1 = ρ
    refine le_of_eq (h1.trans ?_)
    rw [cnt_fst (fun c : (N.om a).Z.D => c = ρ), cnt_eq_const, one_mul]
  · rw [Fintype.card_congr (e a), Fintype.card_prod, Nat.mul_comm]

theorem ldSendFam_data : Spec.ldSendFam_data E := by
  classical
  intro N Sd X E₀
  refine ⟨rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, fun _ q => ⟨rfl, fun _ => Finset.mem_image⟩,
    fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩⟩
  rintro ⟨a, ⟨⟩, ⟨⟩⟩ ⟨b, ⟨⟩, ⟨⟩⟩ h
  exact congrArg (fun c : Sd.D => ((c, (), ()) : Rho (N.sh Sd))) h

theorem ldSendFam_acc : Spec.ldSendFam_acc E := by
  intro N Sd Kc X W W' E₀ A back D hD x y w c ρ hR _
  obtain ⟨ρ₁, u, u'⟩ := ρ
  refine ⟨rfl, fun a => hD.enc _ _ a, fun _ => rfl, ?_⟩
  show A.rel x y (back (D.upM (D.put w c.1)) (D.rest w))
  rw [hD.back]
  exact hR

theorem ldSendFam_within : Spec.ldSendFam_within E := fun N Sd L hF hL hE =>
  ⟨fun m => ldSendFam_cnt E N Sd L hF hL hE m.1,
    fun _ _ => ⟨fun _ => le_of_eq (cnt_false fun _ h => h), fun _ _ => trivial⟩⟩

theorem ldSendFam_out_on : Spec.ldSendFam_out_on E := by
  intro N Sd Kc X W W' E₀ A back a τ b ha hc hb
  obtain ⟨⟨g, u₀⟩, ρ, ⟨u₁, ans⟩, c, u₂⟩ := τ
  obtain rfl : ((a.1, fun i => (Sd.sd i ρ, ans i)), (a.2, g)) = b := Option.some.inj hb
  exact ⟨fun i hi => hc.1 ⟨i, hi⟩, ha⟩

theorem ldSendFam_back : Spec.ldSendFam_back E := by
  intro N Sd Kc X W W' E₀ A back a τ b w hb hw
  obtain ⟨⟨g, u₀⟩, ρ, ⟨u₁, ans⟩, c, u₂⟩ := τ
  obtain rfl : ((a.1, fun i => (Sd.sd i ρ, ans i)), (a.2, g)) = b := Option.some.inj hb
  exact hw.2

theorem ldSendFam_into : Spec.ldSendFam_into E := by
  intro N Sd Kc X W W' E₀ A back L hF hL hE
  exact knowInto_of_badFam _ _ _ _ (ldSendFam N Sd X E₀).red A.on (N.over (N.pull A back)).on A.relR
    (N.over (N.pull A back)).relR _ _ (fun _ => ldSendFamBad N Sd)
    (fun _ _ => ldSendFam_within E N Sd L hF hL hE)
    (fun a τ b ha hc hb => ldSendFam_out_on E N Sd Kc X W W' E₀ A back a τ b ha hc hb)
    fun a τ b w _ _ hb hw => ldSendFam_back E N Sd Kc X W W' E₀ A back a τ b w hb hw

theorem ldSendFam_literal : Spec.ldSendFam_literal E := by
  classical
  intro N Sd Kc X W W' E₀ A back L hF hL hE a ha
  refine ⟨⟨fun s => decide_eq_true_iff, ?_, fun τ s => decide_eq_true_iff⟩, ?_⟩
  · intro τ m s h
    rcases τ with _ | ⟨m₁, ρ, τ'⟩
    · exact h
    · rcases τ' with _ | ⟨_, _, τ''⟩
      · exact h
      · exact τ''.elim
  · intro τ
    rcases τ with m | ⟨m₁, ρ, τ'⟩
    · refine le_trans (cnt_mono ?_) (ldSendFam_cnt E N Sd L hF hL hE m.1)
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
          · exact h0'
              (Or.inl (ldSendFam_back E N Sd Kc X W W' E₀ A back a (m₁, ρ, m₂, c, ()) b w' hb hw))
          · exact hn (ldSendFam_out_on E N Sd Kc X W W' E₀ A back a (m₁, ρ, m₂, c, ()) b ha
                ⟨fun hcl => h0' (Or.inr hcl), fun h => h, trivial⟩ hb)
      · exact τ''.elim

end

section
variable {E : Type} [Field E] (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec)

theorem ldSendFam_isLocal (hL : ∀ a, (N.om a).C.Laws) : (ldSendFam N Sd X E₀).IsLocal where
  out := by
    intro x y y' τ τ' hρ hp _ _
    obtain ⟨⟨g, u₀⟩, ρ, ⟨u₁, ans⟩, c, u₂⟩ := τ
    obtain ⟨⟨g', u₀'⟩, ρ', ⟨u₁', ans'⟩, c', u₂'⟩ := τ'
    obtain rfl : ρ = ρ' := congrArg Prod.fst hρ
    obtain rfl : ans = ans' := congrArg (fun r : Plains (N.sh Sd) => r.2.1) hp
    rfl
  imp := by
    classical
    intro y y' τ τ' q _ _ hy hτ
    rcases q with p | ⟨a, x⟩
    · exact congrArg Sum.inl (hy p (Finset.mem_singleton_self p))
    · refine congrArg (fun s => (Sum.inr ⟨a, s⟩ : (E₀.prod N.ext).Sym))
        ((hL a).loc _ _ x fun p hp => ?_)
      exact congrArg ((N.om a).up p) (hτ (Sum.inl ⟨a, p⟩) (Finset.mem_image.2 ⟨p, hp, rfl⟩))

theorem ldSendFam_view_congr (T : Finset (OPos (N.sh Sd))) (τ τ' : Tr (N.sh Sd))
    (hp : τ.plains = τ'.plains) (hr : ∀ q ∈ ldSendFamSet N Sd T, τ.1.1 q.1 q.2 = τ'.1.1 q.1 q.2) :
    (ldSendFam N Sd X E₀).view T τ = (ldSendFam N Sd X E₀).view T τ' := by
  unfold IOR.view
  refine congrArg₂ IOR.View.mk hp ?_
  funext p
  rcases p with q | q | q
  · refine ldSend_ite_congr Iff.rfl fun hx => ?_
    have hq : (Sum.inl q : OPos (N.sh Sd)) ∈ T :=
      hx.elim (fun h3 => absurd h3 (Finset.notMem_empty _)) fun h3 =>
        h3.elim id fun h4 => Bool.noConfusion h4
    exact hr q (Finset.mem_toLeft.2 hq)
  · exact q.elim
  · exact q.elim

end

section
variable (E : Type) [Field E]

theorem ldSendFam_exactWith : Spec.ldSendFam_exactWith E := by
  classical
  intro N Sd X W W' E₀ D t Ri hB hZ x y w _ ρ _ T hT
  obtain ⟨ρ₁, u, u'⟩ := ρ
  have h1 : (ldSendFamHon Sd X E₀ D).output w x (ρ₁, u, u') T =
      (unif (D.Mk × D.Nn.Rnd)).map fun c =>
        some ((ldSendFam N Sd X E₀).view
              T (((ldSendFamHon Sd X E₀ D).strat w x c).run (ρ₁, u, u')).1) :=
    if_neg fun h => h.elim id id
  refine h1.trans ?_
  show _ = (unif (D.Mk × D.Nn.Rnd)).map fun c =>
      some
        ((ldSendFam N Sd X E₀).view T (((ldSendFamHon Sd X E₀ D).strat D.w0 x c).run (ρ₁, u, u')).1)
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq _ _ (hB ρ₁ w D.w0)
  refine map_unif_prod_congr σ _ _ fun k => ?_
  obtain ⟨e₂, he₂⟩ :=
    (hides_iff_equiv _ D.Nn (N.budT t)).1 hZ (ldSendFamSet N Sd T) hT (D.put w k) (D.put D.w0 (σ k))
  refine map_unif_reindex e₂ _ _ fun r => congrArg some ?_
  refine ldSendFam_view_congr N Sd X E₀ T _ _ ?_ fun q hq => ?_
  · exact congrArg (fun a : N.Answ => (((), (a, ())) : Plains (N.sh Sd))) (hσ k)
  · exact eq_of_heq (Sigma.mk.inj (he₂ r q hq)).2

theorem ldSendFam_goodT : Spec.ldSendFam_goodT E := by
  intro N Sd Kc X W W' E₀ A back D L t hC hF hL hE hD hB hZ
  exact
    { point := ⟨N.pt Sd⟩
      isLocal := ldSendFam_isLocal N Sd X E₀ hC
      acc := ldSendFam_acc E N Sd Kc X W W' E₀ A back D hD
      onOut := fun _ _ _ _ _ => trivial
      keeps := fun w x c ρ => congrArg A.core (hD.back w c.1)
      prBad := prRho_empty _ fun _ h => h
      cover := fun _ _ => Set.empty_subset _
      prCov := fun _ => prRho_empty _ fun _ h => h
      know := ldSendFam_into E N Sd Kc X W W' E₀ A back L hF hL hE
      exact := ⟨ldSendFamSim Sd X E₀ D, ldSendFam_exactWith E N Sd X W W' E₀ D t _ hB hZ⟩ }

theorem ldSendFam_good :
    Spec.ldSendFam_good E := fun N Sd Kc X W W' E₀ A back D L t hC hF hL hE hD hB hZ =>
  good_of_goodT _ _ _ _ _ _ _ _ _ _ _ (fun _ _ (w : N.Wit × W') => back (N.msgs w.1) w.2) _
    (ldSendFam_goodT E N Sd Kc X W W' E₀ A back D L t hC hF hL hE hD hB hZ)

theorem ldSendFam_chain :
    Spec.ldSendFam_chain E := fun N Sd Kc X W W' E₀ A back D L t hC hF hL hE hD hB hZ =>
  (goodT_cf_in _ _ _ _ _ _ _ _ _ A (N.over (N.pull A back)) _ _).1
    (ldSendFam_goodT E N Sd Kc X W W' E₀ A back D L t hC hF hL hE hD hB hZ)

end
end Cb
