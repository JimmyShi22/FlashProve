-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/HonestArith.lean: the arithmetic of the honest trace of an attention segment.

  Integers only: no cell, no entry, no index of the segment. Keys are looked-up values.
  Each result below holds under the hypotheses of its statement.
  * Part 1: remainder, flag and weight of an extended gap (`rmOf`, `flOf`, `wOf`), their ranges,
    and: the keys of the first two calls are entries of τ1 and τ2.
  * Part 2: the remainder of the division, high digits: the keys of the third and
    fourth call are entries of τ3 and τ4.
  * Part 3: scores, the greatest score, gaps: ranges.
  * Part 4: the weight of the program is the weight of the gap.
  * Part 5: the bits of an index: their weighted sum is the index; the product of the equality
    polynomials of the bits selects the index.
  (PA4), (PA7): Inst/Model/Program.lean. Calls, extended gap: Inst/Model/Att/Trace.lean. Entries of
  a region: Inst/Model/Att/Index.lean.

  Notation: `sh`, `u0` : ℕ: the input shift of the exponential; its live rows (Part 1 below). In
  Inst/Model/Tables.lean: `cutC sh u0` : ℤ: the cut-off C = 2^sh u0; `stp sh` : ℤ: st = 2^16 − 2^sh;
  `Smax` : ℤ: S_max (see its doc comment); `ExpOK sh u0` : Prop: the valid shifts and numbers of
  rows in use.
-/
import Inst.Model.TablesExp
import Inst.Model.Sanity

set_option autoImplicit false

namespace Inst.Model.AttSeg.Hon

open Finset

/-! ## Part 1. Remainder, flag and weight of an extended gap
sh: the input shift of the exponential; u0: its live rows (Inst/Model/Tables.lean; 8 and 2,307
at the reference parameters). -/

section Gap
variable (sh u0 : ℕ)

/-- the remainder: below the cut-off the gap modulo 2^sh; from the cut-off on 2^sh plus the
remainder of the excess modulo st -/
def rmOf (gp : ℤ) : ℤ :=
  if gp < cutC sh u0 then gp % 2 ^ sh else 2 ^ sh + (gp - cutC sh u0) % stp sh
/-- the flag: 1 from the cut-off on -/
def flOf (gp : ℤ) : ℤ := if gp < cutC sh u0 then 0 else 1
/-- the weight: Exp at the gap without its sh low bits; 0 from the cut-off on -/
def wOf (tb : Tables) (gp : ℤ) : ℤ := if gp < cutC sh u0 then tb.Exp (gp / 2 ^ sh) else 0

variable {sh u0}

theorem rmOf_range (h : ExpOK sh u0) (gp : ℤ) : 0 ≤ rmOf sh u0 gp ∧ rmOf sh u0 gp < 2 ^ 16 := by
  obtain ⟨a, b⟩ := un_bounds h
  unfold rmOf stp
  generalize (2 : ℤ) ^ sh = s at *
  split_ifs
  · have h1 := Int.emod_nonneg gp (show s ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos gp (show 0 < s by omega)
    constructor <;> omega
  · have h1 := Int.emod_nonneg (gp - cutC sh u0) (show (2 ^ 16 - s : ℤ) ≠ 0 by omega)
    have h2 := Int.emod_lt_of_pos (gp - cutC sh u0) (show (0 : ℤ) < 2 ^ 16 - s by omega)
    constructor <;> omega

theorem flOf_eq (h : ExpOK sh u0) (gp : ℤ) :
    flOf sh u0 gp = if rmOf sh u0 gp < 2 ^ sh then 0 else 1 := by
  obtain ⟨a, b⟩ := un_bounds h
  unfold flOf rmOf stp
  generalize (2 : ℤ) ^ sh = s at *
  by_cases hc : gp < cutC sh u0
  · have h2 := Int.emod_lt_of_pos gp (show 0 < s by omega)
    rw [if_pos hc, if_pos hc, if_pos h2]
  · have h1 := Int.emod_nonneg (gp - cutC sh u0) (show (2 ^ 16 - s : ℤ) ≠ 0 by omega)
    rw [if_neg hc, if_neg hc, if_neg (by omega)]

theorem flOf_01 (gp : ℤ) : flOf sh u0 gp = 0 ∨ flOf sh u0 gp = 1 := by
  unfold flOf
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- an entry of a table -/
def InLut (L : Lut) (v : ℤ) : Prop := ∃ ι : ℕ, ι < L.rows ∧ v = L.row ι

/-- Under `ExpOK`, the key of the first call is an entry of τ1. -/
theorem inLut_tau1 (h : ExpOK sh u0) (gp : ℤ) :
    InLut (tau1 sh)
      (rmOf sh u0 gp % 256 + 2 ^ 20 * (rmOf sh u0 gp / 256) + 2 ^ 40 * flOf sh u0 gp) := by
  obtain ⟨h0, h1⟩ := rmOf_range h gp
  rw [flOf_eq h]
  generalize rmOf sh u0 gp = r at *
  lift r to ℕ using h0
  refine ⟨r, by simpa [tau1] using (by exact_mod_cast h1 : r < 2 ^ 16), ?_⟩
  simp only [tau1]
  by_cases hr : 2 ^ sh ≤ r
  · have hr' : ¬ ((r : ℤ) < 2 ^ sh) := by
      intro hlt
      have : r < 2 ^ sh := by exact_mod_cast hlt
      omega
    rw [if_pos hr, if_neg hr']
    push_cast
    omega
  · have hr' : (r : ℤ) < 2 ^ sh := by exact_mod_cast not_le.1 hr
    rw [if_neg hr, if_pos hr']
    push_cast
    omega

/-- Under h, h0, h1: the key of the second call is an entry of τ2 (in the proof: a live row below
the cut-off, a dead row from it on). -/
theorem inLut_tau2 (h : ExpOK sh u0) (tb : Tables) {gp : ℤ}
    (h0 : 0 ≤ gp) (h1 : gp ≤ 4 * Smax + cutC sh u0) :
    InLut (tau2 sh u0 tb)
      (gp - rmOf sh u0 gp + 2 ^ 32 * flOf sh u0 gp + 2 ^ 33 * wOf sh u0 tb gp) := by
  have hs : (0 : ℤ) < 2 ^ sh := by positivity
  have hroom := h.room
  unfold rmOf flOf wOf
  by_cases hc : gp < cutC sh u0
  · simp only [if_pos hc]
    have hq0 : 0 ≤ gp / 2 ^ sh := Int.ediv_nonneg h0 hs.le
    have hq1 : gp / 2 ^ sh < u0 := Int.ediv_lt_of_lt_mul hs (by unfold cutC at hc; linarith)
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hq0
    have hn' : n < u0 := by rw [hn] at hq1; exact_mod_cast hq1
    refine ⟨n, by simp only [tau2]; omega, ?_⟩
    simp only [tau2, if_pos hn']
    have h4 := Int.emod_add_mul_ediv gp (2 ^ sh)
    rw [hn] at h4 ⊢
    linarith
  · simp only [if_neg hc]
    have hc' : cutC sh u0 ≤ gp := not_lt.1 hc
    have hst : 0 < stp sh := lt_of_lt_of_le (by norm_num) (stp_bounds h).1
    have hq0 : 0 ≤ (gp - cutC sh u0) / stp sh := Int.ediv_nonneg (by omega) hst.le
    have hq1 : (gp - cutC sh u0) / stp sh < nd sh :=
      Int.ediv_lt_of_lt_mul hst (by have := (nd_spec h).2; linarith)
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hq0
    have hn' : n < nd sh := by rw [hn] at hq1; exact_mod_cast hq1
    refine ⟨u0 + n, by simp only [tau2]; omega, ?_⟩
    have h2 : ¬ (u0 + n < u0) := by omega
    have h3 : u0 + n < u0 + nd sh := by omega
    simp only [tau2, if_neg h2, if_pos h3]
    have h4 := Int.emod_add_mul_ediv (gp - cutC sh u0) (stp sh)
    rw [hn] at h4
    push_cast
    linarith

theorem wOf_range {tb : Tables} (hE : ∀ u : ℕ, u < u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12)
    {gp : ℤ} (h0 : 0 ≤ gp) :
    0 ≤ wOf sh u0 tb gp ∧ wOf sh u0 tb gp ≤ 2 ^ 12 := by
  have hs : (0 : ℤ) < 2 ^ sh := by positivity
  unfold wOf
  split_ifs with hc
  · have hq0 : 0 ≤ gp / 2 ^ sh := Int.ediv_nonneg h0 hs.le
    have hq1 : gp / 2 ^ sh < u0 := Int.ediv_lt_of_lt_mul hs (by unfold cutC at hc; linarith)
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hq0
    have hn' : n < u0 := by rw [hn] at hq1; exact_mod_cast hq1
    have h := hE n hn'
    rw [hn]
    exact ⟨by have := h.1; show (0 : ℤ) ≤ tb.Exp (n : ℕ); linarith, h.2⟩
  · norm_num

end Gap

/-! ## Part 2. The division -/

/-- the remainder of the division (PA7): 2 ac + den - 2 den out -/
def reOf (ac den : ℤ) : ℤ := 2 * ac + den - 2 * den * ((2 * ac + den) / (2 * den))

theorem reOf_range (ac : ℤ) {den : ℤ} (hd : 0 < den) : 0 ≤ reOf ac den ∧ reOf ac den < 2 * den := by
  unfold reOf
  have h1 := Int.emod_nonneg (2 * ac + den) (show (2 * den) ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos (2 * ac + den) (show 0 < 2 * den by omega)
  have h3 := Int.emod_add_mul_ediv (2 * ac + den) (2 * den)
  constructor <;> linarith

/-- A number without its digits from 2^16 on is an entry of τ3. -/
theorem inLut_tau3 (a : ℤ) : InLut tau3 (a - 2 ^ 16 * (a / 2 ^ 16)) := by
  have h0 : 0 ≤ a - 2 ^ 16 * (a / 2 ^ 16) := by omega
  have h1 : a - 2 ^ 16 * (a / 2 ^ 16) < 2 ^ 16 := by omega
  generalize a - 2 ^ 16 * (a / 2 ^ 16) = r at *
  lift r to ℕ using h0
  exact ⟨r, by simpa [tau3, R16] using (by exact_mod_cast h1 : r < 2 ^ 16), by simp [tau3, R16]⟩

theorem inLut_tau3_of_range {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 2 ^ 16) : InLut tau3 a := by
  lift a to ℕ using h0
  exact ⟨a, by simpa [tau3, R16] using (by exact_mod_cast h1 : a < 2 ^ 16), by simp [tau3, R16]⟩

/-- Two bytes are an entry of τ4. -/
theorem inLut_tau4 {a b : ℤ} (ha0 : 0 ≤ a) (ha1 : a < 256) (hb0 : 0 ≤ b) (hb1 : b < 256) :
    InLut tau4 (a + 2 ^ 20 * b) := by
  lift a to ℕ using ha0
  lift b to ℕ using hb0
  refine ⟨a + 256 * b, by simp only [tau4]; omega, ?_⟩
  simp only [tau4]
  have e1 : (a + 256 * b) % 256 = a := by omega
  have e2 : (a + 256 * b) / 256 = b := by omega
  rw [e1, e2]

/-- the high digit of a number in [0, 2^23) -/
theorem high_range {a : ℤ} (h0 : 0 ≤ a) (h1 : a < 2 ^ 23) : 0 ≤ a / 2 ^ 16 ∧ a / 2 ^ 16 ≤ 127 := by
  constructor <;> omega

/-! ## Part 3. Scores and gaps -/

theorem Smax_nonneg : (0 : ℤ) ≤ Smax := by unfold Smax; norm_num
theorem cutC_nonneg (sh u0 : ℕ) : (0 : ℤ) ≤ cutC sh u0 := by unfold cutC; positivity

theorem abs_dot_le (n : ℕ) (a b : ℕ → ℤ) (A : ℤ)
    (ha : ∀ k < n, |a k| ≤ A) (hb : ∀ k < n, |b k| ≤ A) :
    |∑ k ∈ range n, a k * b k| ≤ n * A ^ 2 := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ k ∈ range n, |a k * b k| ≤ A ^ 2 := fun k hk => by
    rw [abs_mul, sq]
    exact mul_le_mul (ha k (mem_range.1 hk)) (hb k (mem_range.1 hk)) (abs_nonneg _)
      ((abs_nonneg _).trans (ha k (mem_range.1 hk)))
  refine (sum_le_sum h).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]

/-- the greatest of values of absolute value at most S -/
theorem abs_maxTo_le (f : ℕ → ℤ) (n : ℕ) (S : ℤ) (h : ∀ j ≤ n, |f j| ≤ S) : |maxTo f n| ≤ S := by
  obtain ⟨-, j, hj, he⟩ := maxTo_spec f n
  rw [← he]
  exact h j hj

theorem maxTo_eq_argTo (f : ℕ → ℤ) (n : ℕ) : maxTo f n = f (argTo f n) := by
  obtain ⟨h1, j, hj, he⟩ := maxTo_spec f n
  obtain ⟨h2, h3, -⟩ := argTo_spec f n
  exact le_antisymm (he ▸ h3 j hj) (h1 _ h2)

/-- the gap of a position that is attended to -/
theorem gap_causal (f : ℕ → ℤ) (n : ℕ) (S : ℤ) (h : ∀ j ≤ n, |f j| ≤ S) {j : ℕ} (hj : j ≤ n) :
    0 ≤ maxTo f n - f j ∧ maxTo f n - f j ≤ 2 * S := by
  have h1 := (maxTo_spec f n).1 j hj
  have h2 := abs_le.1 (abs_maxTo_le f n S h)
  have h3 := abs_le.1 (h j hj)
  constructor <;> linarith

/-- the extended gap of a masked entry -/
theorem gap_masked {m s S C : ℤ} (hm : |m| ≤ S) (hs : |s| ≤ S) :
    C ≤ m - s + (2 * S + C) ∧ m - s + (2 * S + C) ≤ 4 * S + C := by
  have h2 := abs_le.1 hm
  have h3 := abs_le.1 hs
  constructor <;> linarith

/-! ## Part 4. The weight of the program -/

/-- The weight of step (PA4) is the weight of the gap. -/
theorem wOf_eq_wt (sh u0 : ℕ) (tb : Tables) (gp : ℤ) :
    wOf sh u0 tb gp = if gp / 2 ^ sh < u0 then tb.Exp (gp / 2 ^ sh) else 0 := by
  have hs : (0 : ℤ) < 2 ^ sh := by positivity
  have hiff : gp < cutC sh u0 ↔ gp / 2 ^ sh < u0 := by
    rw [Int.ediv_lt_iff_lt_mul hs]
    unfold cutC
    rw [mul_comm]
  unfold wOf
  by_cases h : gp < cutC sh u0
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

theorem wOf_dead {sh u0 : ℕ} (tb : Tables) {gp : ℤ} (h : cutC sh u0 ≤ gp) :
    wOf sh u0 tb gp = 0 := by
  unfold wOf
  rw [if_neg (not_lt.2 h)]

theorem wOf_zero {sh u0 : ℕ} {tb : Tables} (hu : 0 < u0) (hE0 : tb.Exp 0 = 2 ^ 12) :
    wOf sh u0 tb 0 = 2 ^ 12 := by
  unfold wOf cutC
  rw [if_pos (by positivity)]
  simpa using hE0

/-! ## Part 5. Bits of an index -/

/-- the bit of weight 2^k -/
def bitZ (k j : ℕ) : ℤ := if j.testBit k then 1 else 0

theorem bitZ_01 (k j : ℕ) : bitZ k j = 0 ∨ bitZ k j = 1 := by
  unfold bitZ
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem sum_bitZ (j : ℕ) : ∀ l : ℕ, ∑ k ∈ range l, 2 ^ k * bitZ k j = ((j % 2 ^ l : ℕ) : ℤ)
  | 0 => by simp [Nat.mod_one]
  | l + 1 => by
      rw [sum_range_succ, sum_bitZ j l, Nat.mod_pow_succ]
      unfold bitZ
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (j / 2 ^ l) with h | h <;> rw [h] <;> simp

theorem sum_bitZ_of_lt {j l : ℕ} (h : j < 2 ^ l) : ∑ k ∈ range l, 2 ^ k * bitZ k j = (j : ℤ) := by
  rw [sum_bitZ, Nat.mod_eq_of_lt h]

/-- For j, j' < 2^l: the product of the equality polynomials of the bits selects the index. -/
theorem prod_eq1_bitZ {l j j' : ℕ} (hj : j < 2 ^ l) (hj' : j' < 2 ^ l) :
    ∏ k ∈ range l, (bitZ k j * bitZ k j' + (1 - bitZ k j) * (1 - bitZ k j')) =
      if j' = j then 1 else 0 := by
  by_cases h : j' = j
  · subst h
    rw [if_pos rfl]
    refine prod_eq_one fun k _ => ?_
    rcases bitZ_01 k j' with e | e <;> rw [e] <;> norm_num
  · rw [if_neg h]
    have hex : ∃ k, k < l ∧ j'.testBit k ≠ j.testBit k := by
      by_contra hn
      refine h (Nat.eq_of_testBit_eq fun k => ?_)
      by_cases hk : k < l
      · exact by_contra fun hne => hn ⟨k, hk, hne⟩
      · have h2 : 2 ^ l ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.testBit_lt_two_pow (hj'.trans_le h2), Nat.testBit_lt_two_pow (hj.trans_le h2)]
    obtain ⟨k, hk, hne⟩ := hex
    refine prod_eq_zero (mem_range.2 hk) ?_
    unfold bitZ
    cases h1 : j.testBit k <;> cases h2 : j'.testBit k <;> simp_all

end Inst.Model.AttSeg.Hon
