-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitchProofs.lean: the proofs of the statements of Cb/Ld/LdSwitch.lean (the zero-knowledge
code switch "with lists" as an interactive oracle reduction), but for the two on privacy of a sample
(Cb/Ld/LdSwitchPrivProofs.lean) and `Spec.ldSwitch_goodT`, which rests on one of them
(Cb/Ld/LdSwitchTop.lean).

The order. Tools: the long word of an encoding by the rows of the generator (`LdCode.word_eq`); the
named coordinates of a new message; the rows with their states. Then the form. Further tools: the
new claim and the relaxed input relation in the words of Cb/Ld/LdSwitchWords.lean (`LdSw.holds_iff`,
`LdSw.in_iff`); the list (`LdSw.listLE`).
Then: the data; completeness; the bad sets, the backward step, knowledge soundness in both forms;
locality; exact zero knowledge; the bundle.
Nothing is defined here that a statement reads.

Main names, each under the hypotheses of its statement (Cb/Ld/LdSwitch.lean):
  `ldSwitch_form`: the new form at the verifier's state as the batched form on vectors.
  `ldSwitch_data`: the data of the code switch.
  `ldSwitch_acc`: completeness.
  `ldSwitch_within`: the bad sets within the errors.
  `ldSwitch_clean`: the backward step.
  `ldSwitch_know`, `ldSwitch_literal`: round-by-round knowledge soundness, in the working form and
    in the form with a knowledge state function.
  `ldSwitch_isLocal` (stated here, under `D.Cout.Reads`): locality (`IOR.IsLocal`).
  `ldSwitch_exactWith`: see its statement in Cb/Ld/LdSwitch.lean.
  `ldSwitch_good`: the bundle `IOR.Good` (Ior/Chain.lean).

Notation: the proofs' names for the statements' hypotheses: `hL`: `D.Cin.Laws`; `hR`: `D.Cout.Reads`
(but in `ldSwitch_acc`: that the input is in the relation); `hl`: `D.Cout.ListAt e' L`; `hZo`:
`D.Zo.OK`; `hZb`: `D.Zb.OK`; `hB`: `D.Zo.Blind good`; `hZ`: `D.Cout.Zk t'`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSwitch
import Cb.Ld.LdSwitchWordsProofs
import Cb.Gen.CodeProofs
import Prob.LawKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-! ## Tools -/

section Tools
variable {E P P' St : Type} [Field E]

/-- Under `h : C.Laws`, the transform of an encoding is the long word that the rows of the generator
give. -/
theorem LdCode.word_eq (C : LdCode E P) (h : C.Laws) (m : C.J → E) (r : C.Q → E) :
    C.T (C.enc m r) = ldWord C.row (Sum.elim m r) := by
  classical
  let Φ : ((C.J → E) × (C.Q → E)) →ₗ[E] (P → C.Aa → E) := (h.tLin.mk' _).comp (h.encLin.mk' _)
  have hΦ : ∀ w : (C.J → E) × (C.Q → E), Φ w = C.T (C.enc w.1 w.2) := fun _ => rfl
  have h1 : C.T (C.enc m r) = Φ (m, 0) + Φ (0, r) := by
    rw [← map_add, hΦ]
    simp
  have h2 : Φ (m, 0) = ∑ j, m j • Φ (Pi.single j 1, 0) := by
    have := LinearMap.pi_apply_eq_sum_univ (Φ.comp (LinearMap.inl E (C.J → E) (C.Q → E))) m
    simp only [LinearMap.comp_apply, LinearMap.inl_apply] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 3
    funext j'
    simp [Pi.single_apply, eq_comm]
  have h3 : Φ (0, r) = ∑ q, r q • Φ (0, Pi.single q 1) := by
    have := LinearMap.pi_apply_eq_sum_univ (Φ.comp (LinearMap.inr E (C.J → E) (C.Q → E))) r
    simp only [LinearMap.comp_apply, LinearMap.inr_apply] at this
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 3
    funext q'
    simp [Pi.single_apply, eq_comm]
  funext x α
  rw [h1, h2, h3]
  unfold ldWord ldAt
  rw [Fintype.sum_sum_type]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Sum.elim_inl, Sum.elim_inr, hΦ]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    (Finset.sum_congr rfl fun q _ => mul_comm _ _)

theorem ldSw_ite_congr {α : Type} {p q : Prop} {_ : Decidable p} {_ : Decidable q} (hpq : p ↔ q)
    {a b : α} (hab : q → a = b) :
    (if p then some a else none) = if q then some b else none := by
  by_cases hq : q
  · rw [if_pos (hpq.2 hq), if_pos hq, hab hq]
  · rw [if_neg fun hp => hq (hpq.1 hp), if_neg hq]

namespace LdSw
variable (D : LdSw E P P' St)

omit [Field E] in
theorem un_re (u : D.Nw → E) : D.un (D.re u) = u :=
  funext fun n => congrArg u (D.place.symm_apply_apply n)

omit [Field E] in
theorem re_un (m' : D.Cout.J → E) : D.re (D.un m') = m' :=
  funext fun j => congrArg m' (D.place.apply_symm_apply j)

omit [Field E] in
theorem old_back (w' : (D.Cout.J → E) × (D.Cout.Q → E)) :
    Sum.elim (D.back w').1 (D.back w').2 = ldOld (D.un w'.1) := by
  funext k
  cases k <;> rfl

omit [Field E] in
theorem back_re (w : (D.Cin.J → E) × (D.Cin.Q → E)) (ro : D.Qo → E) (r' : D.Cout.Q → E) :
    D.back (D.re (D.msg w ro), r') = w := by
  refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
  · show D.un (D.re (D.msg w ro)) _ = _
    rw [un_re]
    rfl
  · show D.un (D.re (D.msg w ro)) _ = _
    rw [un_re]
    rfl

theorem rowSl_stOf (z : St) (ρo : D.Zo.D) (Qs : Fin D.t → P) (b : LdRow D.Zo.S D.t D.Cin.Aa) :
    D.rowSl b (D.stOf z ρo Qs b) = D.W.rows (ldPad (D.sl z)) ρo Qs b := by
  rcases b with _ | _ | _ <;> rfl

end LdSw
end Tools

theorem ldSwitch_form : Spec.ldSwitch_form := by
  intro E P P' St _ D z ρo c n
  show Slf.bat D.Zb.ze D.rowSl (D.stOf z ρo c.1, c.2) (D.place.symm (D.place n)) = _
  rw [Equiv.symm_apply_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  show D.rowSl b (D.stOf z ρo c.1 b) n * D.Zb.ze c.2 b =
    D.Zb.ze c.2 b * D.W.rows (ldPad (D.sl z)) ρo c.1 b n
  rw [D.rowSl_stOf, mul_comm]

section Links
variable {E P P' St : Type} [Field E] (D : LdSw E P P' St)

/-- The new claim, in the words of Cb/Ld/LdSwitchWords.lean. -/
theorem LdSw.holds_iff (z : St) (ρo : D.Zo.D) (c : D.W.Ch2) (τ' : E) (m' : D.Cout.J → E) :
    D.sl'.Holds (τ', (D.stOf z ρo c.1, c.2)) m' ↔
    ldAt (D.W.form' (ldPad (D.sl z)) ρo c) (D.un m') = τ' := by
  have h : ∑ j, D.sl' (D.stOf z ρo c.1, c.2) j * m' j =
      ldAt (D.W.form' (ldPad (D.sl z)) ρo c) (D.un m') := by
    rw [← Equiv.sum_comp D.place]
    exact Finset.sum_congr rfl fun n _ => by rw [ldSwitch_form E P P' St D z ρo c n]; rfl
  unfold Slf.Holds
  rw [h]

variable [Fintype E] [Fintype P]

/-- The relaxed input relation, in the words of Cb/Ld/LdSwitchWords.lean. -/
theorem LdSw.in_iff (h : D.Cin.Laws) (e : ℕ) (a : (E × St) × D.Cin.Word) (w : D.Cin.N.Wit) :
    ConL D.Cin.N e D.sl.Holds a w ↔
    LdSwIn D.W.G e (ldPad (D.sl a.1.2)) a.1.1 (D.Cin.T a.2) (Sum.elim w.1 w.2) := by
  unfold ConL LdSwIn
  rw [ldAt_pad, ← D.Cin.word_eq h w.1 w.2]
  exact Iff.rfl

variable [Fintype P']

omit [Field E] [Fintype P] in
/-- The list of represented messages is at most as long as the list of pairs (message,
randomness). -/
theorem LdSw.listLE (e' L : ℕ) (h : D.Cout.ListAt e' L) (g : D.Cout.Word) :
    ListLE (D.Lst e' g) L := by
  have h1 := ood_list_of_cnt
    _ (fun w : (D.Cout.J → E) × (D.Cout.Q → E) => D.Cout.Near e' g (D.Cout.enc w.1 w.2)) L (h g)
  have h2 := ood_list_image _ _ _ (fun w : (D.Cout.J → E) × (D.Cout.Q → E) => D.un w.1) L h1
  exact ood_list_mono _ _ _ L (fun u hu => hu.elim fun r' hr => ⟨(D.re u, r'), hr, D.un_re u⟩) h2

end Links

/-! ## The data, completeness -/

theorem ldSwitch_data : Spec.ldSwitch_data := by
  classical
  intro E P P' St _ _ _ _ D
  refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun ρ => ?_, fun _ _ => rfl,
    fun _ _ _ => Finset.mem_image, fun b hb ρ q => ?_, fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
  · exact Finset.card_image_le.trans (hb q)

theorem ldSwitch_acc : Spec.ldSwitch_acc := by
  intro E P P' St _ _ _ _ D good hL x y w c ρ hR _
  obtain ⟨hy, hx⟩ := hR
  obtain ⟨ρo, ch, u⟩ := ρ
  subst hy
  refine ⟨rfl, rfl, ?_⟩
  refine (D.holds_iff x.2 ρo ch _ _).2 ?_
  show ldAt _ (D.un (D.re (D.msg w c.1))) = _
  rw [D.un_re, D.Cin.word_eq hL w.1 w.2]
  refine ldSw_complete E _ _ P _ D.W (ldPad (D.sl x.2)) x.1 (Sum.elim w.1 w.2) c.1 ρo ch ?_
  rw [ldAt_pad]
  exact hx

/-! ## Knowledge soundness -/

theorem ldSwitch_within : Spec.ldSwitch_within := by
  intro E P P' St _ _ _ _ _ D e e' L hl hZo hZb a
  exact ⟨fun m => (cnt_ldSwBad1 E _ _ P _ D.W (D.Lst e' m.1) L (D.listLE e' L hl m.1) hZo).1,
    fun m ρo =>
      ⟨fun m₂ =>
          cnt_ldSwBad2 E _ _ P _ D.W (D.Lst e' m.1) e L _ _ _ ρo m₂.2 (D.listLE e' L hl m.1) hZb,
        fun _ _ => trivial⟩⟩

theorem ldSwitch_clean : Spec.ldSwitch_clean := by
  intro E P P' St _ _ _ _ _ D e e' hL a τ b w' hc hb hw
  obtain ⟨⟨g, u₀⟩, ρo, ⟨u₁, ans⟩, c, u₂⟩ := τ
  obtain rfl : ((D.W.tgt' a.1.1 ans (D.Cin.T a.2) c, (D.stOf a.1.2 ρo c.1, c.2)), g) = b :=
    Option.some.inj hb
  obtain ⟨hnear, hholds⟩ := hw
  rw [D.in_iff hL, D.old_back]
  exact ldSw_back E _ _ P _ D.W (D.Lst e' g) e _ _ _ ρo ans c (D.un w'.1) hc.1 hc.2.1
    ⟨w'.2, by rw [D.re_un]; exact hnear⟩ ((D.holds_iff _ ρo c _ _).1 hholds)

theorem ldSwitch_know : Spec.ldSwitch_know := by
  intro E P P' St _ _ _ _ _ D e e' L hL hl hZo hZb
  exact Reduction.Know.of_badFam (ldSwBad D e e')
    (fun a _ => ldSwitch_within E P P' St D e e' L hl hZo hZb a)
    fun a τ b w' _ hc hb hw => ldSwitch_clean E P P' St D e e' hL a τ b w' hc hb hw

theorem ldSwitch_literal : Spec.ldSwitch_literal := by
  classical
  intro E P P' St _ _ _ _ _ D e e' L hL hl hZo hZb a _
  refine ⟨⟨fun s => decide_eq_true_iff, ?_, fun τ s => decide_eq_true_iff⟩, ?_⟩
  · intro τ m s h
    rcases τ with _ | ⟨m₁, ρo, τ'⟩
    · exact h
    · rcases τ' with _ | ⟨_, _, τ''⟩
      · exact h
      · exact τ''.elim
  · intro τ
    rcases τ with m | ⟨m₁, ρo, τ'⟩
    · refine le_trans (cnt_mono ?_)
        (cnt_ldSwBad1 E _ _ P _ D.W (D.Lst e' m.1) L (D.listLE e' L hl m.1) hZo).1
      rintro ρo ⟨s, h0, h1⟩
      exact (of_decide_eq_true h1).resolve_left (of_decide_eq_false h0)
    · rcases τ' with m₂ | ⟨_, _, τ''⟩
      · refine le_trans (cnt_mono ?_)
          (cnt_ldSwBad2 E _ _ P _ D.W (D.Lst e' m₁.1) e L (ldPad (D.sl a.1.2)) a.1.1 (D.Cin.T a.2)
            ρo m₂.2 (D.listLE e' L hl m₁.1) hZb)
        rintro c ⟨s, h0, h1⟩
        obtain ⟨b, hb, hw⟩ := of_decide_eq_true h1
        have h0' := of_decide_eq_false h0
        rcases s with w | w'
        · exact hw.elim
        · by_contra hn
          exact h0' (Or.inl
              (ldSwitch_clean E P P' St D e e' hL a (m₁, ρo, m₂, c, ()) b w'
                ⟨fun hb1 => h0' (Or.inr hb1), hn, trivial⟩ hb hw))
      · exact τ''.elim

/-! ## Locality, zero knowledge, the bundle -/

section
variable {E P P' St : Type} [Field E] [Fintype P] [Nonempty P] (D : LdSw E P P' St)

theorem ldSwitch_isLocal (hR : D.Cout.Reads) : (ldSwitch D).IsLocal where
  out := by
    classical
    intro x y y' τ τ' hρ hp hy _
    obtain ⟨⟨g, u₀⟩, ρo, ⟨u₁, ans⟩, c, u₂⟩ := τ
    obtain ⟨⟨g', u₀'⟩, ρo', ⟨u₁', ans'⟩, c', u₂'⟩ := τ'
    obtain rfl : ρo = ρo' := congrArg Prod.fst hρ
    obtain rfl : c = c' := congrArg (fun r : Rho D.sh => r.2.1) hρ
    obtain rfl : ans = ans' := congrArg (fun r : Plains D.sh => r.2.1) hp
    have hv : D.W.vals x.1 ans (D.Cin.T y) c.1 = D.W.vals x.1 ans (D.Cin.T y') c.1 := by
      funext ν
      rcases ν with _ | _ | ic
      · rfl
      · rfl
      · exact congrFun (hy (c.1 ic.1) (Finset.mem_image.2 ⟨ic.1, Finset.mem_univ _, rfl⟩)) ic.2
    show some (D.W.tgt' x.1 ans (D.Cin.T y) c, _) = some (D.W.tgt' x.1 ans (D.Cin.T y') c, _)
    unfold LdSwW.tgt'
    rw [hv]
  imp := by
    classical
    intro y y' τ τ' q _ _ _ hτ
    exact hR _ _ q fun p hp => hτ (Sum.inl p) (Finset.mem_image.2 ⟨p, hp, rfl⟩)

/-- Two transcripts with the same verifier messages and plain parts (`hp`) that agree on T (`hr`)
show the same. -/
theorem ldSw_view_congr (T : Finset (OPos D.sh)) (τ τ' : Tr D.sh) (hp : τ.plains = τ'.plains)
    (hr : ∀ q ∈ ldSwSet D T, τ.1.1 q = τ'.1.1 q) :
    (ldSwitch D).view T τ = (ldSwitch D).view T τ' := by
  unfold IOR.view
  refine congrArg₂ IOR.View.mk hp ?_
  funext p
  rcases p with q | q | q
  · refine ldSw_ite_congr Iff.rfl fun hx => ?_
    have hq : (Sum.inl q : OPos D.sh) ∈ T :=
      hx.elim (fun h3 => absurd h3 (Finset.notMem_empty _)) fun h3 =>
        h3.elim id fun h4 => Bool.noConfusion h4
    exact hr q (Finset.mem_toLeft.2 hq)
  · exact q.elim
  · exact q.elim

end

theorem ldSwitch_exactWith : Spec.ldSwitch_exactWith := by
  classical
  intro E P P' St _ _ _ _ D good t' Ri hB hZ x y w _ ρ _ T hT
  obtain ⟨ρo, ch, u⟩ := ρ
  by_cases hg : good ρo
  · have h1 : (ldSwitchHon D good).output w x (ρo, ch, u) T
        = (unif ((D.Qo → E) × (D.Cout.Q → E))).map fun c =>
            some ((ldSwitch D).view T (((ldSwitchHon D good).strat w x c).run (ρo, ch, u)).1) :=
      if_neg fun h => h.elim (fun h' => h' hg) id
    have h2 : ∀ z, ldSwSim D good x (ρo, ch, u) T z =
        (unif ((D.Qo → E) × (D.Cout.Q → E))).map fun c =>
          some ((ldSwitch D).view T (((ldSwitchHon D good).strat (0, 0) x c).run (ρo, ch, u)).1) :=
      fun _ => if_pos hg
    refine h1.trans (Eq.trans ?_ (h2 _).symm)
    obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq _ _ (hB ρo hg (Sum.elim w.1 w.2) (Sum.elim 0 0))
    refine map_unif_prod_congr σ _ _ fun ro => ?_
    obtain ⟨e₂, he₂⟩ := (hides_iff_equiv _ D.Cout.Nn (D.Cout.budT t')).1
      hZ (ldSwSet D T) hT (D.re (D.msg w ro)) (D.re (D.msg (0, 0) (σ ro)))
    refine map_unif_reindex e₂ _ _ fun r' => congrArg some ?_
    refine ldSw_view_congr D T _ _ ?_ fun q hq => ?_
    · exact congrArg (fun a : D.Zo.S → E => (((), (a, ())) : Plains D.sh)) (hσ ro)
    · exact eq_of_heq (Sigma.mk.inj (he₂ r' q hq)).2
  · have h1 : (ldSwitchHon D good).output w x (ρo, ch, u) T = PMF.pure none := if_pos (Or.inl hg)
    have h2 : ∀ z, ldSwSim D good x (ρo, ch, u) T z = PMF.pure none := fun _ => if_neg hg
    exact h1.trans (h2 _).symm

theorem ldSwitch_good : Spec.ldSwitch_good := by
  intro E P P' St _ _ _ _ _ D Kc core good e e' L t' hL hR hl hZo hZb hB hZ
  exact
    { point := ⟨D.pt⟩
      isLocal := ldSwitch_isLocal D hR
      acc := ldSwitch_acc E P P' St D good hL
      onOut := fun _ _ _ _ _ => trivial
      keeps := fun w x c ρ => congrArg core (D.back_re w c.1 c.2)
      prBad := le_refl _
      cover := fun _ _ => Set.empty_subset _
      prCov := fun _ => prRho_empty _ fun _ h => h
      know := ldSwitch_know E P P' St D e e' L hL hl hZo hZb
      exact := ⟨ldSwSim D good, ldSwitch_exactWith E P P' St D good t' _ hB hZ⟩ }

end Cb
