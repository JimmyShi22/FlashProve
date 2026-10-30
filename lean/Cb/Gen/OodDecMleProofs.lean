-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecMleProofs.lean: the proofs of the statements of Cb/Gen/OodDecMle.lean (the sample at
multilinear points).

Every theorem here is "name : Cb.Spec.name".

m = |μ| is the number of variables, s the number of points.
Main names, each under the hypotheses of its statement (Cb/Gen/OodDecMle.lean):
  `ood_ok_mle`: the property of a sample map (`Sample.OK`), with err (`Sample.err`) =
    (m |E|^(m-1))^s.
  `ood_cnt_mle`: for a table with at most L tables of messages within the radius: the lists of s
    points at which some answers get the value "several" number at most (L choose 2) (m
    |E|^(m-1))^s.
  `ood_val_rows`: a sample of the whole table is a sample of one combined row.

Limits: see "Limits" in the head of Cb/Gen/OodDecMle.lean.
-/
import Cb.Gen.OodDecMle
import Cb.Gen.OodDecProofs
import Cb.Gen.BatEvaderProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood Finset

theorem ood_val_mle : Spec.ood_val_mle := by
  intro E μ J _ _ _ _ _ pl s ρ u i
  show ∑ j, eqk (ρ i) (pl j) * u j = ∑ b, eqk (ρ i) b * placed pl u b
  unfold placed
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_eq_single (pl j)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg fun h => hb h.symm, mul_zero]
  · intro h
    exact absurd (mem_univ _) h

theorem ood_placed_at : Spec.ood_placed_at := by
  intro E μ J _ _ _ pl u hpl
  refine ⟨fun j => ?_, fun b hb => ?_⟩
  · unfold placed
    rw [sum_eq_single j]
    · rw [if_pos rfl]
    · intro i _ hi
      rw [if_neg fun h => hi (hpl h)]
    · intro h
      exact absurd (mem_univ _) h
  · unfold placed
    exact sum_eq_zero fun j _ => if_neg (hb j)

theorem ood_ok_mle : Spec.ood_ok_mle := by
  intro E μ J _ _ _ _ _ pl s hpl
  exact ood_ok_pow E J _ s (ok_comap E J (μ → Bool) (Evader.eqPt E μ) pl hpl (ok_eqPt E μ))

theorem ood_frac_mle : Spec.ood_frac_mle := by
  intro E μ J _ _ _ _ pl s
  refine ⟨rfl, ?_⟩
  show (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1)) ^ s * Fintype.card E ^ s ≤
    Fintype.card μ ^ s * Fintype.card (Fin s → μ → E)
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
  have hb : Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1) * Fintype.card E ≤
      Fintype.card μ * Fintype.card E ^ Fintype.card μ := by
    rcases Nat.eq_zero_or_pos (Fintype.card μ) with h0 | h0
    · rw [h0]; simp
    · rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel h0]
  calc
    (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1)) ^ s * Fintype.card E ^ s =
        (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1) * Fintype.card E) ^ s :=
      (mul_pow _ _ _).symm
    _ ≤ (Fintype.card μ * Fintype.card E ^ Fintype.card μ) ^ s := Nat.pow_le_pow_left hb s
    _ = Fintype.card μ ^ s * (Fintype.card E ^ Fintype.card μ) ^ s := mul_pow _ _ _

theorem ood_cnt_mle : Spec.ood_cnt_mle := by
  intro E ι κ R μ J _ _ _ _ _ _ _ G e view pl s f L hpl hL
  have h1 : cnt
        (fun ρ : Fin s → μ → E => ∃ y, decS G e view (Sample.mle E μ J pl s) f ρ y = .several) ≤
      L.choose 2 * (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1)) ^ s :=
    (ood_cnt_severalS E ι κ R J G e view (Sample.mle E μ J pl s)
      f L hL (ood_ok_mle E μ J pl s hpl)).1
  refine ⟨h1, ?_⟩
  calc
    cnt (fun ρ : Fin s → μ → E => ∃ y, decS G e view (Sample.mle E μ J pl s) f ρ y = .several) *
          Fintype.card E ^ s ≤
        L.choose 2 * (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1)) ^ s *
          Fintype.card E ^ s :=
      Nat.mul_le_mul_right _ h1
    _ = L.choose 2 *
          ((Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1)) ^ s * Fintype.card E ^ s) :=
      Nat.mul_assoc _ _ _
    _ ≤ L.choose 2 * (Fintype.card μ ^ s * Fintype.card (Fin s → μ → E)) :=
      Nat.mul_le_mul_left _ (ood_frac_mle E μ J pl s).2
    _ = L.choose 2 * Fintype.card μ ^ s * Fintype.card (Fin s → μ → E) := (Nat.mul_assoc _ _ _).symm

theorem ood_cnt_mle_plain_pow : Spec.ood_cnt_mle_plain_pow := by
  intro E ι κ R μ J _ _ _ _ _ _ _ G e view pl s f L hpl hL
  refine (cnt_mono fun z => ?_).trans
    (ood_cnt_clashS E ι κ R J G e view (Sample.mle E μ J pl s) f L hL (ood_ok_mle E μ J pl s hpl))
  rintro ⟨M, M', hM, hM', hne, hz⟩
  refine ⟨view M, view M', ⟨M, hM, rfl⟩, ⟨M', hM', rfl⟩, hne, funext fun i => ?_⟩
  rw [ood_val_mle E μ J pl s z (view M) i, ood_val_mle E μ J pl s z (view M') i]
  exact hz i

theorem ood_cnt_mle_plain : Spec.ood_cnt_mle_plain := by
  intro E ι κ R μ J _ _ _ _ _ _ _ G e view pl f L hpl hL
  have h := ood_cnt_mle_plain_pow E ι κ R μ J G e view pl 1 f L hpl hL
  rw [pow_one] at h
  refine le_trans (le_of_eq ?_) h
  exact (cnt_equiv (Equiv.funUnique (Fin 1) (μ → E)) (fun z : μ → E =>
      ∃ M M',
        DecodesTo G e f M ∧ DecodesTo G e f M' ∧ view M ≠ view M' ∧
        Alg.mle (placed pl (view M)) z = Alg.mle (placed pl (view M')) z)).symm.trans
    (cnt_congr fun z =>
      exists_congr fun M =>
        exists_congr fun M' =>
          and_congr_right fun _ =>
            and_congr_right fun _ =>
              and_congr_right fun _ =>
                ⟨fun h i => by rw [Subsingleton.elim i 0]; exact h, fun h => h 0⟩)

theorem ood_val_rows : Spec.ood_val_rows := by
  intro E R κ μR μP _ _ _ _ _ _ _ _ plR plP s ρ M i
  show ∑ n : R × κ, eqk (ρ i) (plBoth plR plP n) * M n.1 n.2 =
    ∑ k,
      eqk (fun v => ρ i (Sum.inr v)) (plP k) * (∑ a, eqk (fun v => ρ i (Sum.inl v)) (plR a) • M a) k
  rw [Fintype.sum_prod_type_right]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_apply, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  have h : eqk (ρ i) (plBoth plR plP (a, k)) =
      eqk (fun v => ρ i (Sum.inl v)) (plR a) * eqk (fun v => ρ i (Sum.inr v)) (plP k) := by
    have hρ : Sum.elim (fun v => ρ i (Sum.inl v)) (fun v => ρ i (Sum.inr v)) = ρ i := by
      funext v
      cases v <;> rfl
    have h0 :=
      eqk_sumElim (fun v => ρ i (Sum.inl v)) (fun v => ρ i (Sum.inr v)) (plBoth plR plP (a, k))
    rw [hρ] at h0
    exact h0
  rw [h, Pi.smul_apply, smul_eq_mul]
  ring

theorem ood_plBoth_inj : Spec.ood_plBoth_inj := by
  intro R κ μR μP plR plP hR hP n n' h
  have h1 : plR n.1 = plR n'.1 := funext fun v => congrFun h (Sum.inl v)
  have h2 : plP n.2 = plP n'.2 := funext fun v => congrFun h (Sum.inr v)
  exact Prod.ext (hR h1) (hP h2)

end Cb
