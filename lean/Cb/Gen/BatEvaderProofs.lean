-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/BatEvaderProofs.lean: the proofs of Cb/Gen/BatEvader.lean.
The value is linear in the form, so the value of the combination is ∑_j ze(ρ)_j v_j for v the vector
of the J values (`val_comb`). If v ≠ 0, the seeds at which this is 0 are the bad ones, and the
evader's property counts them (`cnt_bad_le`).
`ok_indep` uses `Alg.count_affine_form_le_pow` (constant term 0), `ok_powers` uses
`Alg.count_powers_le` (exponents from 0).
-/
import Cb.Gen.BatEvader

set_option autoImplicit false

namespace Cb
open Blocks Iop Prob Alg Finset

theorem val_comb {E J Y P : Type} [Field E] [Fintype J] (𝔉 : Forms E Y P) (Z : Evader E J) (ρ : Z.D)
    (f : J → 𝔉.Fm) (y : Y) :
    𝔉.val y (Z.comb ρ f) = ∑ j, Z.ze ρ j * 𝔉.val y (f j) := by
  unfold Evader.comb
  rw [map_sum]
  exact sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]

/-- the count, in the form that `clean_batB` and `clean_batS` use -/
theorem cnt_bad_le {E J : Type} [Field E] [Fintype J] (Z : Evader E J) (hZ : Z.OK) (v : J → E) :
    cnt (fun ρ : Z.D => (¬ ∀ j, v j = 0) ∧ ∑ j, Z.ze ρ j * v j = 0) ≤ Z.err := by
  by_cases hv : ∀ j, v j = 0
  · exact le_trans (le_of_eq (cnt_false fun _ h => h.1 hv)) (Nat.zero_le _)
  · exact le_trans (cnt_mono fun _ h => h.2) (hZ v fun h0 => hv fun j => congrFun h0 j)

theorem clean_batB : Spec.clean_batB := by
  intro E J Y P _ _ 𝔉 Z hZ
  refine Block.clean_one
    (fun x y _ => {ρ | (¬ ∀ j, 𝔉.val y (x j) = 0) ∧ ∑ j, Z.ze ρ j * 𝔉.val y (x j) = 0}) _
    (fun x y _ => cnt_bad_le Z hZ fun j => 𝔉.val y (x j)) fun x y m c xo hc hxo hRo => ?_
  obtain rfl := Option.some.inj hxo
  by_contra hR
  exact hc ⟨hR, (val_comb 𝔉 Z c x y).symm.trans hRo⟩

theorem clean_batS : Spec.clean_batS := by
  intro E J X Y P _ _ 𝔉 Z rows hZ
  refine Block.clean_sample
    (fun x y => {ρ | (¬ ∀ j, 𝔉.val y (rows x j) = 0) ∧ ∑ j, Z.ze ρ j * 𝔉.val y (rows x j) = 0}) _
    (fun x y => cnt_bad_le Z hZ fun j => 𝔉.val y (rows x j)) fun x y c hc _ hRo => ?_
  by_contra hR
  exact hc ⟨hR, (val_comb 𝔉 Z c (rows x) y).symm.trans hRo⟩

theorem accOn_batB : Spec.accOn_batB := by
  intro E J Y P Ii Io _ _ 𝔉 Z nx Hi hHi
  refine Hon.accOn_one fun a π x y c hi _ _ => ⟨Z.comb c x, rfl, ⟨a, x, c, hi, rfl, rfl⟩, ?_⟩
  rw [val_comb]
  exact sum_eq_zero fun j _ => by rw [hHi a π x y hi j, mul_zero]

theorem accOn_batS : Spec.accOn_batS := by
  intro E J X Y P Ii Io _ _ 𝔉 Z rows nx Hi hHi
  refine Hon.accOn_sample _ nx fun a π x y c hi _ => ⟨⟨a, hi, rfl⟩, ?_⟩
  rw [val_comb]
  exact sum_eq_zero fun j _ => by rw [hHi a π x y hi j, mul_zero]

theorem withheld_batB : Spec.withheld_batB := by
  intro E J Y P Ii Io _ _ 𝔉 Z nx a
  refine Set.eq_empty_of_forall_notMem fun ρ h => ?_
  rcases h with h | h <;> exact h

theorem withheld_batS : Spec.withheld_batS := by
  intro E J X Y P Ii Io _ _ Z nx a
  refine Set.eq_empty_of_forall_notMem fun ρ h => ?_
  rcases h with h | h
  · exact Bool.noConfusion h
  · exact h

theorem masked_batB : Spec.masked_batB := by
  intro E J Y P Ii Io _ _ _ _ _ 𝔉 Z nx V
  exact Hon.masked_one_const V _ fun _ _ _ => rfl

theorem masked_batS : Spec.masked_batS := by
  intro E J X Y P Ii Io _ _ _ _ _ Z nx V
  exact Hon.masked_sample _ nx V

theorem clean_batK : Spec.clean_batK := by
  intro E J J' Y P _ _ 𝔉 Z hZ
  refine Block.Clean.on' (clean_batB E J Y P 𝔉 Z hZ) fun x y _ f _ hR =>
    ⟨hR (.inl ()), fun h k => ?_⟩
  rcases k with j | j'
  · exact h j
  · exact hR (.inr j')

theorem accOn_batK : Spec.accOn_batK := by
  intro E J J' Y P Ii Io _ _ 𝔉 Z nx Hi hHi a π x y ρ hi _
  refine ⟨keptRows x (Z.comb ρ.1 (joinedRows x)), rfl, ⟨a, x, ρ.1, hi, rfl, rfl⟩, fun k => ?_⟩
  rcases k with _ | j'
  · show 𝔉.val y (Z.comb ρ.1 (joinedRows x)) = 0
    rw [val_comb]
    exact sum_eq_zero fun j _ => by
      rw [show 𝔉.val y (joinedRows x j) = 0 from hHi a π x y hi (.inl j), mul_zero]
  · exact hHi a π x y hi (.inr j')

theorem withheld_batK : Spec.withheld_batK := by
  intro E J J' Y P Ii Io _ _ 𝔉 Z nx a
  refine Set.eq_empty_of_forall_notMem fun ρ h => ?_
  rcases h with h | h <;> exact h

theorem masked_batK : Spec.masked_batK := by
  intro E J J' Y P Ii Io _ _ _ _ _ 𝔉 Z nx V
  exact (masked_batB E J Y P Ii Io 𝔉 Z nx V).on (joinedRows (J' := J')) keptRows (id : Y → Y)
    (fun (_ : Y) (y : Y) => y) (id : Ii → Ii) (fun (_ : Ii) (b : Io) => b)

theorem ok_eqPt : Spec.ok_eqPt := by
  intro E ι _ _ _ _ v hv
  exact count_mle_zero_le v hv

theorem lt_eqPt : Spec.lt_eqPt := by
  intro E ι _ _ _ _ h
  show Fintype.card ι * Fintype.card E ^ (Fintype.card ι - 1) < Fintype.card (ι → E)
  rw [Fintype.card_fun]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
  · rw [h0]; simp
  · calc Fintype.card ι * Fintype.card E ^ (Fintype.card ι - 1) < Fintype.card E * Fintype.card E ^ (Fintype.card ι - 1) :=
          Nat.mul_lt_mul_of_pos_right h (pow_pos Fintype.card_pos _)
      _ = Fintype.card E ^ (Fintype.card ι) := by rw [← pow_succ', Nat.sub_add_cancel h0]

theorem ok_comap : Spec.ok_comap := by
  intro E J J₀ _ _ _ Z e he hZ v hv
  classical
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hv
  have hw : ∀ j, (∑ i, if e i = e j then v i else 0) = v j := fun j => by
    rw [sum_eq_single j]
    · simp
    · intro i _ hi; rw [if_neg fun h => hi (he h)]
    · intro h; exact absurd (mem_univ _) h
  refine le_trans (cnt_mono fun ρ hρ => ?_)
    (hZ (fun k => ∑ i, if e i = k then v i else 0) fun h0 =>
      hj0 ((hw j0).symm.trans (congrFun h0 (e j0))))
  have h1 : ∑ j, Z.ze ρ (e j) * v j = 0 := hρ
  show ∑ k, Z.ze ρ k * (∑ i, if e i = k then v i else 0) = 0
  have h2 : ∀ k, Z.ze ρ k * (∑ i, if e i = k then v i else 0) =
      ∑ i, if e i = k then Z.ze ρ (e i) * v i else 0 := fun k => by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  simp only [h2]
  rw [sum_comm]
  refine Eq.trans (sum_congr rfl fun i _ => ?_) h1
  rw [sum_ite_eq, if_pos (mem_univ _)]

theorem ok_indep : Spec.ok_indep := by
  intro E J _ _ _ _ v hv
  have := count_affine_form_le_pow (J := J) (0 : E) v (Or.inr hv)
  simpa [cnt] using this

theorem ok_powers : Spec.ok_powers := by
  intro E _ _ n v hv
  have := count_powers_le v hv 0
  simpa [cnt] using this

theorem lt_indep : Spec.lt_indep := by
  intro E J _ _ _ _ _
  show Fintype.card E ^ (Fintype.card J - 1) * Fintype.card E = Fintype.card (J → E)
  rw [Fintype.card_fun, ← pow_succ, Nat.sub_add_cancel Fintype.card_pos]

theorem lt_powers : Spec.lt_powers := by
  intro E _ _ n hn
  show n - 1 < Fintype.card E
  have : 0 < Fintype.card E := Fintype.card_pos
  omega

theorem comb_form : Spec.comb_form := by
  intro E J N _ _ Z ρ f o
  unfold Evader.comb
  rw [Finset.sum_apply]
  rfl

end Cb
