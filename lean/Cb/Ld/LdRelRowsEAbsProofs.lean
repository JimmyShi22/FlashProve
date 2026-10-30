-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelRowsEAbsProofs.lean: the proofs of the statements of Cb/Ld/LdRelRowsEAbs.lean
(Cb.rows_avoid, Cb.rows_free_abs).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdRelRowsEAbs.lean):
  `rows_avoid`: at most |E| proper subspaces of E^R do not cover E^R.
  `rows_free_abs`: there is one vector w of coefficients such that every θ that is exceptional for
    the tables g₀, g₁ is exceptional for the two words ∑ w i • g₀ i, ∑ w i • g₁ i.

`rows_avoid` is shown by counting the vectors other than 0 (the count: the row of `Spec.rows_avoid`
in Cb/Ld/LdRelRowsEAbs.lean). For `rows_free_abs` (with the parameters of `Spec.rows_free_abs`), fix
for each exceptional θ (`Bad θ`) one set S θ, and let V θ be the coefficients w for which both
combinations, ∑ w i • g₀ i and ∑ w i • g₁ i, lie in W (S θ); it is a subspace, and it is proper
because the unit vectors give back the rows. By `rows_avoid` there is a vector w in none of the V θ.
-/
import Cb.Ld.LdRelRowsEAbs

set_option autoImplicit false

namespace Cb
open Module

theorem rows_avoid : Spec.rows_avoid := by
  classical
  intro E R _ _ _ B V hV
  by_contra hcon
  have hcov : ∀ w : R → E, ∃ θ ∈ B, w ∈ V θ := by
    intro w
    by_contra hw
    exact hcon ⟨w, fun θ hθ hm => hw ⟨θ, hθ, hm⟩⟩
  -- B has at least two members
  have hB2 : 2 ≤ B.card := by
    by_contra hlt
    have hle : B.card ≤ 1 := by omega
    obtain ⟨θ₀, hθ₀, -⟩ := hcov 0
    apply hV θ₀ hθ₀
    rw [Submodule.eq_top_iff']
    intro w
    obtain ⟨θ, hθ, hm⟩ := hcov w
    rwa [Finset.card_le_one.1 hle θ hθ θ₀ hθ₀] at hm
  obtain ⟨θ₀, hθ₀, -⟩ := hcov 0
  -- R is not empty
  have hR : 0 < Fintype.card R := by
    rw [Fintype.card_pos_iff]
    by_contra hne
    haveI : IsEmpty R := not_nonempty_iff.1 hne
    apply hV θ₀ hθ₀
    rw [Submodule.eq_top_iff']
    intro w
    rw [Subsingleton.elim w 0]
    exact (V θ₀).zero_mem
  set q := Fintype.card E with hq
  set s := Fintype.card R with hs
  let Wf : E → Finset (R → E) := fun θ => Finset.univ.filter fun w => w ∈ V θ
  have hW : ∀ θ ∈ B, (Wf θ).card ≤ q ^ (s - 1) := by
    intro θ hθ
    have h1 : (Wf θ).card = Fintype.card (V θ) := (Fintype.card_subtype fun w => w ∈ V θ).symm
    have h2 : finrank E (V θ) < s := by
      have := Submodule.finrank_lt (hV θ hθ)
      rwa [finrank_fintype_fun_eq_card] at this
    rw [h1, card_eq_pow_finrank (K := E) (V := V θ)]
    exact Nat.pow_le_pow_right Fintype.card_pos (by omega)
  have h0 : ∀ θ, (0 : R → E) ∈ Wf θ := fun θ =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (V θ).zero_mem⟩
  have hsub : (Finset.univ.erase (0 : R → E)) ⊆ B.biUnion fun θ => (Wf θ).erase 0 := by
    intro w hw
    obtain ⟨θ, hθ, hm⟩ := hcov w
    exact Finset.mem_biUnion.2
      ⟨θ, hθ,
        Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hw).1, Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩⟩⟩
  have hT : (Finset.univ.erase (0 : R → E)).card + 1 = q ^ s := by
    rw [Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun]
  have hS : (Finset.univ.erase (0 : R → E)).card ≤ ∑ θ ∈ B, ((Wf θ).erase 0).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hsum : ∑ θ ∈ B, (((Wf θ).erase 0).card + 1) ≤ B.card • q ^ (s - 1) :=
    Finset.sum_le_card_nsmul B _ _ fun θ hθ => by
      rw [Finset.card_erase_add_one (h0 θ)]
      exact hW θ hθ
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one] at hsum
  have hBq : B.card * q ^ (s - 1) ≤ q ^ s := by
    calc B.card * q ^ (s - 1) ≤ q * q ^ (s - 1) := Nat.mul_le_mul_right _ (Finset.card_le_univ B)
      _ = q ^ s := by rw [← pow_succ', Nat.sub_add_cancel hR]
  omega

theorem rows_free_abs : Spec.rows_free_abs := by
  classical
  intro E R M 𝒮 _ _ _ _ _ ok W g₀ g₁
  cases nonempty_fintype E
  let Bad : E → Prop := fun θ =>
    ∃ S, ok S ∧ (∀ i, g₀ i + θ • g₁ i ∈ W S) ∧ ¬ ((∀ i, g₀ i ∈ W S) ∧ ∀ i, g₁ i ∈ W S)
  let L : (R → M) → (R → E) →ₗ[E] M := fun g =>
    { toFun := fun w => ∑ i, w i • g i
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hL1 : ∀ (g : R → M) (i : R), L g (Pi.single i 1) = g i := by
    intro g i
    show ∑ j, (Pi.single i (1 : E) : R → E) j • g j = g i
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  let V : E → Submodule E (R → E) := fun θ =>
    if h : Bad θ then (W h.choose).comap (L g₀) ⊓ (W h.choose).comap (L g₁) else ⊥
  have hV : ∀ θ ∈ Finset.univ.filter Bad, V θ ≠ ⊤ := by
    intro θ hθ htop
    have hb : Bad θ := (Finset.mem_filter.1 hθ).2
    have hmem : ∀ w : R → E, w ∈ (W hb.choose).comap (L g₀) ⊓ (W hb.choose).comap (L g₁) := by
      intro w
      have : w ∈ V θ := by rw [htop]; exact Submodule.mem_top
      simpa only [V, dif_pos hb] using this
    refine hb.choose_spec.2.2 ⟨fun i => ?_, fun i => ?_⟩
    · have h1 : L g₀ (Pi.single i 1) ∈ W hb.choose := (hmem (Pi.single i 1)).1
      rwa [hL1] at h1
    · have h1 : L g₁ (Pi.single i 1) ∈ W hb.choose := (hmem (Pi.single i 1)).2
      rwa [hL1] at h1
  obtain ⟨w, hw⟩ := rows_avoid E R (Finset.univ.filter Bad) V hV
  refine ⟨w, fun θ hb => ?_⟩
  have hb' : Bad θ := hb
  refine ⟨hb'.choose, hb'.choose_spec.1, ?_, fun hc => ?_⟩
  · have e1 : (∑ i, w i • g₀ i) + θ • (∑ i, w i • g₁ i) = ∑ i, w i • (g₀ i + θ • g₁ i) := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_add, smul_comm]
    rw [e1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb'.choose_spec.2.1 i)
  · apply hw θ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb'⟩)
    simp only [V, dif_pos hb']
    exact ⟨hc.1, hc.2⟩

end Cb
