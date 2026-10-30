-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRngAlgProofs.lean: the statements of Cb/Ld/LdRngAlg.lean, proved.

The main one, `rngPk_cnt_out`: for q H = 2 D, if the predicate `Rng` fails at the bound 2 D, digits
with `Out` exist for at most the fraction 2^(-|U|) of the challenges (q, H: the sizes of the two
tables of digits; |U| combinations).
The counts come from Prob/Window.lean, the honest digits and the tables from
Cb/Gen/RngAlgProofs.lean.
-/
import Cb.Ld.LdRngAlg
import Cb.Gen.RngAlgProofs

set_option autoImplicit false

namespace Cb
open Prob Finset Cb.Rng Cb.RngPk

namespace RngPk

section
variable {A Rp : Type} [CommRing A] {P : ℕ} (ϱ : ℤ)

theorem pack_intCast (y : Rp × Fin P → ℤ) (i : Rp) :
    pack ϱ (fun r => ((y r : ℤ) : A)) i = ((pack ϱ y i : ℤ) : A) := by
  unfold pack
  push_cast
  rfl

theorem pack_sub (a b : Rp × Fin P → A) (i : Rp) :
    pack ϱ (fun r => a r - b r) i = pack ϱ a i - pack ϱ b i := by
  unfold pack
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun l _ => mul_sub _ _ _

theorem pack_mul_left (e : A) (a : Rp × Fin P → A) (i : Rp) :
    pack ϱ (fun r => e * a r) i = e * pack ϱ a i := by
  unfold pack
  rw [mul_sum]
  exact sum_congr rfl fun l _ => mul_left_comm _ _ _

theorem pack_sum {C : Type} (s : Finset C) (a : C → Rp × Fin P → A) (i : Rp) :
    pack ϱ (fun r => ∑ c ∈ s, a c r) i = ∑ c ∈ s, pack ϱ (a c) i := by
  unfold pack
  rw [sum_comm]
  exact sum_congr rfl fun l _ => mul_sum _ _ _

end

/-- Integer lanes below the radix in absolute value whose packing is 0 are 0. -/
theorem lanes_zero (ϱ : ℤ) :
    ∀ (P : ℕ) (d : Fin P → ℤ), (∀ l, |d l| < ϱ) → ∑ l : Fin P, ϱ ^ (l : ℕ) * d l = 0 → ∀ l, d l = 0
  | 0, _, _, _ => fun l => l.elim0
  | P + 1, d, hd, h => by
    have e : ∀ l : Fin P,
        ϱ ^ ((l.succ : Fin (P + 1)) : ℕ) * d l.succ = ϱ * (ϱ ^ (l : ℕ) * d l.succ) := fun l => by
      rw [Fin.val_succ, pow_succ]
      ring
    rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul,
      sum_congr rfl (fun l _ => e l), ← mul_sum] at h
    have h0 : d 0 = 0 := Alg.eq_zero_of_add_mul_eq_zero (hd 0) h
    have hϱ : 0 < ϱ := lt_of_le_of_lt (abs_nonneg _) (hd 0)
    have h1 : ∑ l : Fin P, ϱ ^ (l : ℕ) * d l.succ = 0 := by
      rw [h0, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left hϱ.ne'
    have ih := lanes_zero ϱ P (fun l => d l.succ) (fun l => hd _) h1
    intro l
    exact Fin.cases h0 ih l

end RngPk

theorem rngPk_unique : Spec.rngPk_unique := by
  intro E _ p _ Rp P b ϱ y y' hU hy hy' hp
  obtain ⟨h1, h2⟩ := hU
  funext r
  obtain ⟨i, l⟩ := r
  have hd : ∀ l, |y (i, l) - y' (i, l)| ≤ 2 * b - 2 := by
    intro l
    have a1 := abs_lt.1 (hy (i, l))
    have a2 := abs_lt.1 (hy' (i, l))
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hb : 0 ≤ 2 * b - 2 := le_trans (abs_nonneg _) (hd l)
  have hϱ : 0 < ϱ := lt_of_le_of_lt hb h1
  have eS : ∑ l : Fin P, ϱ ^ (l : ℕ) * (y (i, l) - y' (i, l)) = pack ϱ y i - pack ϱ y' i := by
    rw [← pack_sub]
    unfold pack
    simp
  have hS : ((∑ l : Fin P, ϱ ^ (l : ℕ) * (y (i, l) - y' (i, l)) : ℤ) : E) = 0 := by
    have h := hp i
    rw [pack_intCast, pack_intCast] at h
    rw [eS, Int.cast_sub, h, sub_self]
  have hdvd : (p : ℤ) ∣ ∑ l : Fin P, ϱ ^ (l : ℕ) * (y (i, l) - y' (i, l)) :=
    (CharP.intCast_eq_zero_iff E p _).1 hS
  have habs : |∑ l : Fin P, ϱ ^ (l : ℕ) * (y (i, l) - y' (i, l))| < p := by
    refine lt_of_le_of_lt (le_trans (abs_sum_le_sum_abs _ _) ?_) h2
    rw [mul_sum, ← Fin.sum_univ_eq_sum_range (fun l => (2 * b - 2) * ϱ ^ l) P]
    refine sum_le_sum fun l _ => ?_
    rw [abs_mul, abs_of_pos (pow_pos hϱ _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hd l) (pow_pos hϱ _).le
  have hS0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  exact sub_eq_zero.1
    (lanes_zero ϱ P (fun l => y (i, l) - y' (i, l)) (fun l => lt_of_le_of_lt (hd l) h1) hS0 l)

theorem rngPk_cells : Spec.rngPk_cells := by
  intro E _ p _ Rp C _ P b b' ϱ Y mpk hU hb hY
  have hP : Packed P b ϱ mpk := ⟨Y, fun r c => lt_of_lt_of_le (hY.1 r c) hb, hY.2⟩
  have hc := hP.choose_spec
  unfold cells
  rw [dif_pos hP]
  funext r c
  exact congrFun
    (rngPk_unique E p Rp P b ϱ (fun r => hP.choose r c) (fun r => Y r c) hU (fun r => hc.1 r c)
      (fun r => lt_of_lt_of_le (hY.1 r c) hb) (fun i => (hc.2 i c).symm.trans (hY.2 i c))) r

theorem rngPk_iff_cells : Spec.rngPk_iff_cells := by
  intro E _ p _ Rp Rd C _ P b ϱ W mpk mrd hU
  constructor
  · rintro ⟨Y, hp, hr⟩
    refine ⟨⟨Y, hp⟩, ?_⟩
    rw [rngPk_cells E p Rp C P b b ϱ Y mpk hU (le_refl b) hp]
    exact hr
  · rintro ⟨⟨Y, hp⟩, hr⟩
    rw [rngPk_cells E p Rp C P b b ϱ Y mpk hU (le_refl b) hp] at hr
    exact ⟨Y, hp, hr⟩

theorem rngPk_mono : Spec.rngPk_mono := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb h =>
  ⟨⟨fun r c => lt_of_lt_of_le (h.1.1 r c) hb, h.1.2⟩, h.2⟩

theorem rngPk_plain : Spec.rngPk_plain := by
  intro E _ Rp C _ b ϱ W mpk mrd
  constructor
  · rintro ⟨Y, ⟨hs, hp⟩, _⟩ i c
    refine ⟨Y (i, 0) c, hs _ _, ?_⟩
    rw [hp i c]
    simp [pack]
  · intro h
    choose f hf using h
    refine ⟨fun r c => f r.1 c, ⟨fun r c => (hf r.1 c).1, fun i c => ?_⟩, fun k => k.elim⟩
    rw [(hf i c).2]
    simp [pack]

theorem rngPk_iff_cols : Spec.rngPk_iff_cols := by
  intro E _ Rp Rd C _ P b ϱ W mpk mrd
  constructor
  · rintro ⟨Y, ⟨hs, hp⟩, hr⟩ c
    exact ⟨fun r => Y r c, fun r => hs r c, fun i => hp i c, fun k => hr k c⟩
  · intro h
    choose y hy using h
    exact ⟨fun r c => y c r,
      ⟨fun r c => (hy c).1 r, fun i c => (hy c).2.1 i⟩,
      fun k c => (hy c).2.2 k⟩

theorem rngPk_good_of_two : Spec.rngPk_good_of_two := by
  intro E _ Rp Rd C _ _ _ P D ϱ W mpk mrd cf c₀ e he h0 h1
  obtain ⟨z, hz, hT, hR⟩ := h0
  obtain ⟨z', hz', hT', hR'⟩ := h1
  have hee : (e : E) * (e : E) = 1 := by rcases he with rfl | rfl <;> simp
  refine ⟨fun r => e * (z' r - z r), ?_, ?_, ?_⟩
  · intro r
    have a1 := hz r
    have a2 := hz' r
    rw [abs_lt]
    rcases he with rfl | rfl <;> constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · intro i
    have a0 := hT i
    have a1 := hT' i
    beta_reduce at a0 a1
    rw [Alg.sum_update_cast_mul] at a0 a1
    rw [Int.cast_zero, zero_mul, zero_add] at a0
    have e1 : pack ϱ (fun r => ((e * (z' r - z r) : ℤ) : E)) i =
        (e : E) * (pack ϱ (fun r => ((z' r : ℤ) : E)) i - pack ϱ (fun r => ((z r : ℤ) : E)) i) := by
      rw [← pack_sub, ← pack_mul_left]
      congr 1
      funext r
      push_cast
      ring
    rw [e1, ← a0, ← a1]
    linear_combination (-mpk i c₀) * hee
  · intro k
    have a0 := hR k
    have a1 := hR' k
    beta_reduce at a0 a1
    rw [Alg.sum_update_cast_mul] at a0 a1
    rw [Int.cast_zero, zero_mul, zero_add] at a0
    have e1 : ∑ r, W k r * ((e * (z' r - z r) : ℤ) : E) =
        (e : E) * (∑ r, W k r * ((z' r : ℤ) : E) - ∑ r, W k r * ((z r : ℤ) : E)) := by
      rw [← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun r _ => by push_cast; ring
    rw [e1, ← a0, ← a1]
    linear_combination (-mrd k c₀) * hee

theorem rngPk_cnt_pass : Spec.rngPk_cnt_pass := by
  intro E _ Rp Rd C U _ _ _ _ _ P D ϱ W mpk mrd hbad
  rw [rngPk_iff_cols E Rp Rd C P (2 * D) ϱ W mpk mrd] at hbad
  push Not at hbad
  obtain ⟨c₀, hc⟩ := hbad
  exact cnt_forall_pass_mul_le (CanPass D ϱ W mpk mrd) c₀ fun cf e he h0 h1 =>
    hc (rngPk_good_of_two E Rp Rd C P D ϱ W mpk mrd cf c₀ e he h0 h1)

theorem rngPk_pass_of_out : Spec.rngPk_pass_of_out := by
  intro E _ Rp Rd C U _ _ P D ϱ q H W Θ mpk mrd d hq hO u
  obtain ⟨⟨hl, hh⟩, hp, hr⟩ := hO
  choose a ha using fun r => hl r u
  choose b hb using fun r => hh r u
  have hψ : ∀ r, psi D q d r u = (((a r : ℤ) + q * b r - D : ℤ) : E) := by
    intro r
    unfold psi
    rw [(ha r).2, (hb r).2]
    push_cast
    ring
  refine ⟨fun r => (a r : ℤ) + q * b r - D, fun r => ⟨?_, ?_⟩, fun i => ?_, fun k => ?_⟩
  · have : (0 : ℤ) ≤ (a r : ℤ) + q * b r := by positivity
    linarith
  · have h1 : (a r : ℤ) + 1 ≤ q := by exact_mod_cast (ha r).1
    have h2 : (b r : ℤ) + 1 ≤ H := by exact_mod_cast (hb r).1
    have h3 : (q : ℤ) * ((b r : ℤ) + 1) ≤ q * H := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  · show ∑ c, (((Θ u c).val : ℤ) : E) * mpk i c =
      pack ϱ (fun r => (((a r : ℤ) + q * b r - D : ℤ) : E)) i
    rw [hp i u]
    congr 1
    funext r
    exact hψ r
  · show ∑ c, (((Θ u c).val : ℤ) : E) * mrd k c = ∑ r, W k r * (((a r : ℤ) + q * b r - D : ℤ) : E)
    rw [hr k u]
    exact sum_congr rfl fun r _ => by rw [hψ r]

theorem rngPk_cnt_out : Spec.rngPk_cnt_out := by
  intro E _ Rp Rd C U _ _ _ _ _ P D ϱ q H W mpk mrd hq hbad
  refine le_trans (Nat.mul_le_mul_right _ (cnt_mono fun Θ hΘ => ?_))
    (rngPk_cnt_pass E Rp Rd C U P D ϱ W mpk mrd hbad)
  obtain ⟨d, hd⟩ := hΘ
  exact rngPk_pass_of_out E Rp Rd C U P D ϱ q H W Θ mpk mrd d hq hd

theorem rngPk_honest : Spec.rngPk_honest := by
  intro E _ Rp Rd C U _ _ P b D ϱ q H W Y Θ mpk mrd hq hqH hY hE
  have hw : ∀ r u, -D ≤ comb (Y r) (Θ u) ∧ comb (Y r) (Θ u) < D := by
    intro r u
    by_contra hn
    exact hE ⟨(r, u), hn⟩
  have hd := fun r u => digits_ok E C D q H (Y r) (Θ u) hq hqH (hw r u).1 (hw r u).2
  have hψ : ∀ r u,
      psi D q (hdig (E := E) D q Y Θ) r u = ∑ c, (((Θ u c).val : ℤ) : E) * ((Y r c : ℤ) : E) :=
    fun r u => (hd r u).2.2.symm
  refine ⟨⟨fun r u => ⟨_, (hd r u).1, rfl⟩, fun r u => ⟨_, (hd r u).2.1, rfl⟩⟩,
    fun i u => ?_, fun k u => ?_⟩
  · have e1 : (fun r => psi D q (hdig (E := E) D q Y Θ) r u) =
        fun r => ∑ c, (((Θ u c).val : ℤ) : E) * ((Y r c : ℤ) : E) :=
      funext fun r => hψ r u
    rw [e1, pack_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [pack_mul_left, hY.1.2 i c]
  · have e1 : ∀ r, W k r * psi D q (hdig (E := E) D q Y Θ) r u =
        ∑ c, (((Θ u c).val : ℤ) : E) * (W k r * ((Y r c : ℤ) : E)) := by
      intro r
      rw [hψ r u, mul_sum]
      exact sum_congr rfl fun c _ => mul_left_comm _ _ _
    rw [sum_congr rfl fun r _ => e1 r, sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [hY.2 k c, mul_sum]

theorem rngPk_tight : Spec.rngPk_tight := by
  intro U _ _
  constructor
  · rintro ⟨Y, ⟨hs, hp⟩, _⟩
    have h := hp () ()
    simp [pack] at h
    have h2 := hs ((), 0) ()
    rw [← h] at h2
    norm_num at h2
  · have key : ∀ Θ : U → Unit → Coef,
        (∃ d, Out (E := ℤ) (Rp := Unit) (Rd := Empty) (P := 1) 1 1 2 1 (fun k => k.elim) Θ
          (fun _ _ => 2) (fun k => k.elim) d) ↔
        ∀ u, (fun g : Unit → Coef => (g ()).val = 0) (Θ u) := by
      intro Θ
      constructor
      · rintro ⟨d, ⟨hl, hh⟩, hp, _⟩ u
        obtain ⟨a, ha, ea⟩ := hl ((), 0) u
        obtain ⟨b, hb, eb⟩ := hh ((), 0) u
        have h : (Θ u ()).val * 2 = (a : ℤ) + 2 * (b : ℤ) - 1 := by
          have h := hp () u
          simpa [pack, psi, ea, eb] using h
        show (Θ u ()).val = 0
        omega
      · intro h
        refine ⟨(fun _ _ => 1, fun _ _ => 0),
          ⟨fun _ _ => ⟨1, by norm_num, by simp⟩, fun _ _ => ⟨0, by norm_num, by simp⟩⟩,
          fun i u => ?_, fun k => k.elim⟩
        have hu : (Θ u ()).val = 0 := h u
        simp [pack, psi, hu]
    rw [cnt_congr key, cnt_forall (U := U) (fun g : Unit → Coef => (g ()).val = 0)]
    have h2 : cnt (fun g : Unit → Coef => (g ()).val = 0) = 2 := by
      rw [cnt_eq_card_filter]
      decide
    have h4 : Fintype.card (U → Unit → Coef) = 4 ^ Fintype.card U := by
      rw [Fintype.card_fun]
      congr 1
    rw [h2, h4, ← mul_pow]
    norm_num

end Cb
