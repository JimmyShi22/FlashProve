-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecPadProofs.lean: the proofs of the statements of Cb/Gen/OodDecPad.lean (sample maps on a
set of vectors, the sample row with a pad, one sample for each row, privacy).

The theorems are "ood_* : Cb.Spec.ood_*"; `Ood.pad_val_raw`, `Ood.padVal_zero`,
`Ood.map_unif_equiv_any` and `Ood.map_pair_unif` are auxiliary.
-/
import Cb.Gen.OodDecPad
import Cb.Gen.OodDecMleProofs
import Cb.Gen.OodDecCxProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood Finset

theorem ood_ok_iff_okOn : Spec.ood_ok_iff_okOn := fun _ _ _ _ _ =>
  ⟨fun h v _ hv => h v hv, fun h v hv => h v trivial hv⟩

theorem ood_okOn_of_ok : Spec.ood_okOn_of_ok := fun _ _ _ _ _ _ h v _ hv => h v hv

theorem ood_cnt_clash_on : Spec.ood_cnt_clash_on := by
  intro E J _ _ Z V Lst L hL hZ hV
  refine ood_cnt_clash (J → E) Z.D (Z.S → E) Lst Z.val L Z.err hL fun u u' hu hu' hne => ?_
  refine (cnt_mono fun ρ hρ => ?_).trans (hZ (u - u') (hV u u' hu hu') (sub_ne_zero.mpr hne))
  rw [Sample.val_sub, hρ, sub_self]

theorem ood_cnt_several_on : Spec.ood_cnt_several_on := by
  intro E J _ _ Z V Lst L hL hZ hV
  have h : cnt (fun ρ : Z.D => ∃ y, Coll Lst Z.val ρ y) ≤ L.choose 2 * Z.err :=
    (le_of_eq (cnt_congr fun ρ => (ood_clash_iff _ _ _ Lst Z.val ρ).symm)).trans
      (ood_cnt_clash_on E J Z V Lst L hL hZ hV)
  exact ⟨h, two_mul_le_sq h⟩

theorem ood_padInF_sub : Spec.ood_padInF_sub := by
  intro F E J₀ P _ _ _ u u' hu hu' i
  obtain ⟨x, hx⟩ := hu i
  obtain ⟨x', hx'⟩ := hu' i
  exact ⟨x - x', by rw [map_sub, hx, hx']; rfl⟩

/-- Auxiliary: the answer of the row with a pad, as two sums. -/
theorem Ood.pad_val_raw {E μ J₀ P B : Type} [Field E] [Fintype E] [Fintype μ] [DecidableEq μ]
    [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool) (w : P → E) (b : B → E)
    (ρ : (μ → E) × B) (v : J₀ ⊕ P → E) :
    (Sample.pad E μ J₀ P B pl w b).val ρ v () =
      (∑ j, eqk ρ.1 (pl j) * v (Sum.inl j)) + b ρ.2 * ∑ i, w i * v (Sum.inr i) := by
  show ∑ n : J₀ ⊕ P, (Sum.elim (fun j => eqk ρ.1 (pl j)) (fun i => b ρ.2 * w i) n) * v n = _
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [mul_sum]
  exact congrArg _ (sum_congr rfl fun i _ => mul_assoc _ _ _)

theorem ood_val_pad : Spec.ood_val_pad := by
  intro E μ J₀ P B _ _ _ _ _ _ _ _ pl w b z β v
  rw [pad_val_raw]
  exact congrArg (· + _) (ood_val_mle E μ J₀ pl 1 (fun _ => z) (fun j => v (Sum.inl j)) 0)

theorem Ood.padVal_zero {F E P : Type} [Field F] [Field E] [Algebra F E] [Fintype P] (w : P → E) :
    padVal (F := F) w 0 = 0 := by
  simp [padVal]

theorem ood_okOn_pad : Spec.ood_okOn_pad := by
  intro F E μ J₀ P B _ _ _ _ _ _ _ _ _ _ pl w b hpl hb hw v hV hv
  show cnt (fun ρ : (μ → E) × B => (Sample.pad E μ J₀ P B pl w b).val ρ v = 0) ≤
    max (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1) * Fintype.card B)
      (Fintype.card E ^ Fintype.card μ)
  have hval : ∀ ρ : (μ → E) × B, (Sample.pad E μ J₀ P B pl w b).val ρ v = 0 →
      (∑ j, eqk ρ.1 (pl j) * v (Sum.inl j)) + b ρ.2 * ∑ i, w i * v (Sum.inr i) = 0 :=
    fun ρ hρ => (pad_val_raw pl w b ρ v).symm.trans (congrFun hρ ())
  have hV' : ∀ i, ∃ x : F, algebraMap F E x = v (Sum.inr i) := hV
  choose c hc using hV'
  have hπ : ∑ i, w i * v (Sum.inr i) = padVal w c := sum_congr rfl fun i _ => by rw [hc]
  by_cases h0 : ∑ i, w i * v (Sum.inr i) = 0
  · have hc0 : c = 0 := hw ((hπ.symm.trans h0).trans (padVal_zero w).symm)
    have hr : ∀ i, v (Sum.inr i) = 0 := fun i => by rw [← hc, hc0, Pi.zero_apply, map_zero]
    have ha : (fun j => v (Sum.inl j)) ≠ 0 := fun h => hv (funext fun n => by
      cases n with
      | inl j => exact congrFun h j
      | inr i => exact hr i)
    refine le_trans ?_ (le_max_left _ _)
    refine (cnt_mono (Q := fun ρ : (μ → E) × B => ∑ j, eqk ρ.1 (pl j) * v (Sum.inl j) = 0)
      fun ρ hρ => ?_).trans ?_
    · have := hval ρ hρ
      rwa [h0, mul_zero, add_zero] at this
    · rw [cnt_fst (D := B) fun z : μ → E => ∑ j, eqk z (pl j) * v (Sum.inl j) = 0]
      exact Nat.mul_le_mul_right
        _ (ok_comap E J₀ (μ → Bool) (Evader.eqPt E μ) pl hpl (ok_eqPt E μ) _ ha)
  · refine le_trans ?_ (le_max_right _ _)
    refine (cnt_prod_le _ 1 fun z => cnt_le_one fun β β' hβ hβ' => hb ?_).trans
      (by rw [mul_one, Fintype.card_fun])
    have h1 := hval (z, β) hβ
    have h2 := hval (z, β') hβ'
    exact mul_right_cancel₀ h0 (add_left_cancel (h1.trans h2.symm))

theorem ood_frac_pad : Spec.ood_frac_pad := by
  intro E μ J₀ P B _ _ _ _ _ _ pl w b hb
  show max (Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1) * Fintype.card B)
        (Fintype.card E ^ Fintype.card μ) * Fintype.card B ≤
    (Fintype.card μ + 1) * Fintype.card ((μ → E) × B)
  rw [Fintype.card_prod, Fintype.card_fun, ← Nat.mul_assoc]
  refine Nat.mul_le_mul_right _ (max_le ?_ (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)))
  have hB : Fintype.card B ≤ Fintype.card E := Fintype.card_le_of_injective b hb
  have h1 : Fintype.card μ * Fintype.card E ^ (Fintype.card μ - 1) * Fintype.card E ≤
      Fintype.card μ * Fintype.card E ^ Fintype.card μ := by
    rcases Nat.eq_zero_or_pos (Fintype.card μ) with h0 | h0
    · rw [h0]; simp
    · rw [Nat.mul_assoc, ← pow_succ, Nat.sub_add_cancel h0]
  exact (Nat.mul_le_mul_left _ hB).trans (h1.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)))

/-- Auxiliary: `Prob.map_unif_equiv` with the two instances of finiteness as explicit arguments. -/
theorem Ood.map_unif_equiv_any
    {C D : Type} (iC : Fintype C) (iD : Fintype D) [Nonempty C] [Nonempty D] (e : C ≃ D) :
    (unif C).map e = unif D := map_unif_equiv e

theorem ood_private_pad : Spec.ood_private_pad := by
  intro F E μ J₀ P B _ _ _ _ _ _ _ _ _ _ _ pl w b hw
  classical
  rintro ⟨z, β⟩ hβ a
  have hβ' : b β ≠ 0 := hβ
  let e : (P → F) ≃ (Unit → E) :=
    (Equiv.ofBijective _ hw).trans
      ((Equiv.mulLeft₀ (b β) hβ').trans
        ((Equiv.addLeft (∑ j, eqk z (pl j) * a j)).trans (Equiv.funUnique Unit E).symm))
  have hfun : (fun c : P → F => (Sample.pad E μ J₀ P B pl w b).val (z, β) (withPad a c)) = e := by
    funext c u
    cases u
    exact pad_val_raw pl w b (z, β) (withPad a c)
  refine (congrArg (fun g => PMF.map g _) hfun).trans ?_
  exact map_unif_equiv_any _ _ e

/-- Auxiliary, for non-empty D, C, Y: if the second component is uniform for every first component,
the pair is uniform. -/
theorem Ood.map_pair_unif {D C Y : Type} [Fintype D] [Nonempty D] [Fintype C] [Nonempty C]
    [Fintype Y] [Nonempty Y] (g : D → C → Y) (h : ∀ ρ, (unif C).map (g ρ) = unif Y) :
    (unif (D × C)).map (fun x => (x.1, g x.1 x.2)) = unif (D × Y) := by
  rw [map_unif_eq_unif_iff]
  rintro ⟨ρ, y⟩
  have h1 := (map_unif_eq_unif_iff (g ρ)).mp (h ρ) y
  have h2 : cnt (fun x : D × C => (x.1, g x.1 x.2) = (ρ, y)) = cnt (fun c => g ρ c = y) := by
    rw [cnt_prod_eq_sum, sum_eq_single ρ]
    · exact cnt_congr fun c => ⟨fun h => (Prod.mk.inj h).2, fun h => by
        show (ρ, g ρ c) = (ρ, y)
        rw [h]⟩
    · intro ρ' _ hne
      exact cnt_false fun c hc => hne (Prod.mk.inj hc).1
    · intro h
      exact absurd (mem_univ _) h
  rw [h2, Fintype.card_prod, Fintype.card_prod, ← h1]
  ring

theorem ood_privateSim : Spec.ood_privateSim := by
  intro F E J₀ P _ _ _ _ _ _ _ Z h
  classical
  exact ⟨unif (Z.D × (Z.S → E)),
    fun a => map_pair_unif (fun ρ c => Z.val ρ (withPad a c)) fun ρ => h ρ trivial a⟩

theorem ood_privateSim_pad : Spec.ood_privateSim_pad := by
  intro F E μ J₀ P B _ _ _ _ _ _ _ _ _ _ _ pl w b hw hb
  exact ood_privateSim F E J₀ P _ fun ρ _ a => ood_private_pad F E μ J₀ P B pl w b hw ρ (hb ρ.2) a

theorem ood_val_rows_same : Spec.ood_val_rows_same := by
  intro E J R _ _ _ Z ρ v a s
  classical
  show ∑ n : R × J, (if n.1 = a then Z.mat ρ s n.2 else 0) * v n = ∑ j, Z.mat ρ s j * v (a, j)
  rw [Fintype.sum_prod_type, sum_eq_single a]
  · exact sum_congr rfl fun j _ => by rw [if_pos rfl]
  · intro a' _ hne
    exact sum_eq_zero fun j _ => by rw [if_neg hne, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

theorem ood_okOn_rows : Spec.ood_okOn_rows := by
  intro E J R _ _ _ Z V hZ v hV hv
  obtain ⟨n, hn⟩ := Function.ne_iff.mp hv
  have ha : (fun j => v (n.1, j)) ≠ 0 := fun h => hn (congrFun h n.2)
  refine (cnt_mono fun ρ hρ => ?_).trans (hZ _ (hV n.1) ha)
  funext s
  exact (ood_val_rows_same E J R Z ρ v n.1 s).symm.trans (congrFun hρ (n.1, s))

end Cb
