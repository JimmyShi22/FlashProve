-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/RngAlgProofs.lean: the statements of Cb/Gen/RngAlg.lean, proved.
-/
import Cb.Gen.RngAlg
import Alg.Range

set_option autoImplicit false

namespace Cb
open Prob Finset Cb.Rng
open scoped ENNReal

theorem short_of_pass_two : Spec.short_of_pass_two := by
  intro F _ R C _ _ D Y cf c₀ e he h0 h1 r
  obtain ⟨a0, l0, u0, e0⟩ := h0 r
  obtain ⟨a1, l1, u1, e1⟩ := h1 r
  unfold combF at e0 e1
  rw [Alg.sum_update_cast_mul] at e0 e1
  rw [Int.cast_zero, zero_mul, zero_add] at e0
  have hee : (e : F) * (e : F) = 1 := by rcases he with rfl | rfl <;> simp
  refine ⟨e * (a1 - a0), ?_, ?_⟩
  · rw [abs_lt]
    rcases he with rfl | rfl <;> constructor <;> linarith
  · push_cast
    rw [← e0, ← e1]
    linear_combination (-Y r c₀) * hee

theorem cnt_allPass_mul_le : Spec.cnt_allPass_mul_le := by
  intro F _ R C U _ _ _ _ D Y hbad
  push Not at hbad
  obtain ⟨r, c₀, hc⟩ := hbad
  exact cnt_forall_pass_mul_le (Pass D Y) c₀ fun cf e he h0 h1 =>
    hc (short_of_pass_two F R C D Y cf c₀ e he h0 h1 r)

theorem pass_of_digits : Spec.pass_of_digits := by
  intro F _ R C _ D q H Y cf l h hq hl hh hrow r
  obtain ⟨a, ha, ea⟩ := hl r
  obtain ⟨b, hb, eb⟩ := hh r
  refine ⟨(a : ℤ) + q * b - D, ?_, ?_, ?_⟩
  · have : (0 : ℤ) ≤ (a : ℤ) + q * b := by positivity
    linarith
  · have h1 : (a : ℤ) + 1 ≤ q := by exact_mod_cast ha
    have h2 : (b : ℤ) + 1 ≤ H := by exact_mod_cast hb
    have h3 : (q : ℤ) * ((b : ℤ) + 1) ≤ q * H := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  · rw [hrow, ea, eb]
    push_cast
    ring

theorem digits_ok : Spec.digits_ok := by
  intro F _ C _ D q H y g hq hqH hl hu
  set z := comb y g with hz
  have h0 : 0 ≤ z + D := by linarith
  have hA : (((z + D).toNat : ℕ) : ℤ) = z + D := Int.toNat_of_nonneg h0
  have hlt : (z + D).toNat < q * H := by
    have : (((z + D).toNat : ℕ) : ℤ) < ((q * H : ℕ) : ℤ) := by
      rw [hA]
      push_cast
      linarith
    exact_mod_cast this
  refine ⟨Nat.mod_lt _ hq, Nat.div_lt_of_lt_mul hlt, ?_⟩
  have hsplit : (lo D q z : ℕ) + q * hi D q z = (z + D).toNat := Nat.mod_add_div _ _
  have hcast : ((lo D q z : ℕ) : F) + (q : F) * ((hi D q z : ℕ) : F) = ((z + D : ℤ) : F) := by
    have h1 : (((lo D q z + q * hi D q z : ℕ) : ℤ) : F) = ((z + D : ℤ) : F) := by rw [hsplit, hA]
    rw [← h1]
    push_cast
    ring
  rw [hcast, hz]
  unfold comb
  push_cast
  ring

theorem pr_event_le : Spec.pr_event_le := by
  intro R C U _ _ _ _ _ _ B D Yz hB hD hY
  have hB' : (0 : ℝ) < ((B - 1 : ℤ) : ℝ) := by exact_mod_cast (by linarith : (0 : ℤ) < B - 1)
  have hC : (0 : ℝ) < (Fintype.card C : ℝ) := by exact_mod_cast Fintype.card_pos
  exact pr_exists_window_le Yz _ D (by positivity) hD fun r =>
    sum_sq_le (Yz r) (B - 1) fun c => by have := hY r c; linarith

theorem event_empty : Spec.event_empty := by
  intro R C U _ D Yz hD hY Λ
  rintro ⟨x, hx⟩
  apply hx
  have h0 : comb (Yz x.1) (Λ x.2) = 0 := by
    unfold comb
    refine Finset.sum_eq_zero fun c _ => ?_
    have : Yz x.1 c = 0 := by
      have := hY x.1 c
      rw [abs_lt] at this
      omega
    rw [this, mul_zero]
  rw [h0]
  constructor <;> linarith

theorem rep_unique : Spec.rep_unique := by
  intro F _ p _ b a a' hb ha ha' h
  have hd : ((a - a' : ℤ) : F) = 0 := by
    push_cast
    rw [h, sub_self]
  have hdvd : (p : ℤ) ∣ a - a' := (CharP.intCast_eq_zero_iff F p _).1 hd
  rw [abs_lt] at ha ha'
  have habs : |a - a'| < p := by
    rw [abs_lt]
    constructor <;> linarith [ha.1, ha.2, ha'.1, ha'.2]
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

theorem short_iff_valMinAbs : Spec.short_iff_valMinAbs := by
  intro p _ b hb x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : ((a : ℤ) : ZMod p).valMinAbs = a := by
      rw [ZMod.valMinAbs_spec]
      rw [abs_lt] at ha
      refine ⟨rfl, ?_, ?_⟩ <;> linarith [ha.1, ha.2]
    rw [this]
    exact ha
  · intro h
    exact ⟨x.valMinAbs, h, (ZMod.coe_valMinAbs x).symm⟩

end Cb
