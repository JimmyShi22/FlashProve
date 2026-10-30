-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/LedgerSound.lean: what the lookups and identities of a normalisation's ledger
imply over the integers.

The ledger (99 auxiliary bytes D), its row values, multipliers µ_n, sums W_s and 17 identities:
Inst/Model/Common/Ledger.lean. Everything here is arithmetic at one position, generic in d, M, ϵ,
the modulus p and the bound c on a cell. There is no protocol and no probability. `typed_of_keys`,
`idn_int`, `ledger_sound` assume the size conditions `Adm`; the docstrings give the other hypotheses
of the rows below.
  `Typed D`         (FL1): every key (looked-up value) µ_n D_n of the family ROW is a byte
  `typed_of_keys`   Step L1 for ROW
  `idn_int`         Steps L4 and L5, "Equality": the 17 identities hold over the integers if they
                    hold modulo p
  `sound_int`       Steps L4 and L5, "New facts": V, ς, R of the ledger are `NORM.V`, `NORM.sig`,
                    `NORM.R` of the integer model for the values that the five cells represent; V +
                    ϵ < 2^78; 1 ≤ ς < 2^39; |x[j]| < 2^39; |x[j] R| < 2^M + 2^38
`Adm` holds at p = 2^61 − 1 and the reference parameters c = 2^18, d = 5,120, M = 44, ϵ = 53,687
(`adm_ref`). The bound on W_s counts all 25 pairs (l, l'), not only the at most five with l + l' =
s; so `Adm` asks for 25 d c² + 2^56 ≤ p. Labels such as (FL1) and "Step L1" link one docstring to
another.
Notation (Inst/Model/Common/Ledger.lean):
  `D`: a map from the number of a byte to its value: "A ledger is here the function D from the
    number of a byte to its value".
  `Vlo`, `Vhi`, `cs`, `sa`, `s0`, `sb`, `sig`, `l1`, `h1`, `Blo`, `Bhi`, `kc`, `Rlo`, `Rhi`, `R`,
    `q1`, `rr`, `rq`: numbers read from bytes of D; the doc comments there tell the bytes.
  `Wsum d b s` (W_s): "W_s = Σ_j Σ_{l + l' = s} b_l[j] b_l'[j], for the five cells b_0..b_4 of the d
    values x[j]"; so b: first the cell l < 5, then j < d.
  `mu n` (µ_n): "The multiplier µ_n of byte n in the keys (looked-up values) µ_n D_n of the family
    ROW".
  (J1) to (J9): `idn`: "The 17 identities, each as "left side minus right side": number k < 9 is
    (J1) for s = k; 9..16 are (J2) to (J9)."
  `np`: a `NormPar`, "exponent of the reciprocal; shift; constant" of a normalisation: its fields M,
    K, eps, in this order (so the term of three numbers in `adm_ref`); ϵ is eps
    (Inst/Model/Program.lean).
-/
import Inst.Model.Common.Ledger
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace Inst.Model.Ledger

open Finset

/-! ## 0. Tools -/

/-- An integer that is congruent to 0 modulo p and below p in absolute value is 0. -/
theorem lift_zero {p a : ℤ} (h : a ≡ 0 [ZMOD p]) (hlt : |a| < p) : a = 0 :=
  Int.eq_zero_of_abs_lt_dvd (Int.modEq_zero_iff_dvd.mp h) hlt

/-- Two integers that are congruent modulo p and differ by less than p in absolute value are
equal. -/
theorem lift_eq {p a b : ℤ} (h : a ≡ b [ZMOD p]) (hlt : |a - b| < p) : a = b := by
  have hd : p ∣ a - b := Int.modEq_iff_dvd.mp h.symm
  have := Int.eq_zero_of_abs_lt_dvd hd hlt
  omega

private theorem abs_sum_range_le {n : ℕ} {f : ℕ → ℤ} {B : ℤ} (hf : ∀ i, i < n → |f i| ≤ B) : |∑ i ∈ range n, f i| ≤ n * B := by
  calc |∑ i ∈ range n, f i| ≤ ∑ i ∈ range n, |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range n, B := sum_le_sum (fun i hi => hf i (mem_range.mp hi))
    _ = n * B := by simp

/-- Every s ≥ 0 with s² ≤ a < (s + 1)² is isqrt(a). -/
theorem isqrt_eq {a s : ℤ} (hs : 0 ≤ s) (h1 : s * s ≤ a) (h2 : a < (s + 1) * (s + 1)) :
    isqrt a = s := by
  have ha : 0 ≤ a := le_trans (mul_nonneg hs hs) h1
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hs
  have hm : m = Nat.sqrt n := Nat.eq_sqrt.mpr ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  simp [isqrt, ← hm]

private theorem mul_bounds {a b A B : ℤ} (ha0 : 0 ≤ a) (ha : a < A) (hb0 : 0 ≤ b) (hb : b < B) :
    0 ≤ a * b ∧ a * b < A * B :=
  ⟨mul_nonneg ha0 hb0, mul_lt_mul'' ha hb ha0 hb0⟩

/-! ## 1. The size conditions, and the value that five cells represent -/

/-- the value that the five cells b_0[j], .., b_4[j] represent -/
def xOf (b : ℕ → ℕ → ℤ) (j : ℕ) : ℤ := ∑ l ∈ range 5, 256 ^ l * b l j

/-- The size conditions of the ledger: p is the modulus, c a bound on the absolute value of a
cell. -/
structure Adm (p : ℤ) (np : NormPar) (d : ℕ) (c : ℤ) : Prop where
  eps_pos : 1 ≤ np.eps
  eps_lt : np.eps < 2 ^ 48
  M_le : np.M ≤ 47
  c_pos : 0 < c
  /-- Step L1, ROW: 2^7 (c + 128), and a table entry -/
  row : 128 * (c + 128) + 255 < p
  /-- Step L4 -/
  j1 : 25 * (d : ℤ) * c ^ 2 + 2 ^ 56 ≤ p
  /-- Step L5: under `Typed` and the bounds on ϵ and M above, the value of each of the identities
  (J2) to (J9) is below 2^53 in absolute value (proof of `idn_int`) -/
  big : 2 ^ 53 ≤ p

/-- At the reference parameters, with p the numeral of the statement, the size conditions hold. -/
theorem adm_ref : Adm (2 ^ 61 - 1) ⟨44, 30, 53687⟩ 5120 (2 ^ 18) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## 2. Step L1 for ROW: the ranges of the bytes -/

/-- (FL1): µ_n D_n is a byte, for every n < 99. -/
def Typed (D : ℕ → ℤ) : Prop := ∀ n < 99, 0 ≤ mu n * D n ∧ mu n * D n ≤ 255

theorem mu_pos (n : ℕ) : 1 ≤ mu n ∧ mu n ≤ 128 := by
  unfold mu
  split_ifs <;> norm_num

/-- Step L1 for the family ROW: under `Adm`, if every cell D_n − 128 is at most c in absolute value
and every key µ_n D_n is congruent modulo p to an entry of {0, .., 255}, then `Typed D`. -/
theorem typed_of_keys {p : ℤ} {np : NormPar} {d : ℕ} {c : ℤ} (adm : Adm p np d c) {D : ℕ → ℤ}
    (hD : ∀ n < 99, |D n - 128| ≤ c)
    (hk : ∀ n < 99, ∃ t : ℤ, 0 ≤ t ∧ t < 256 ∧ mu n * D n ≡ t [ZMOD p]) : Typed D := by
  intro n hn
  obtain ⟨t, h0, h1, ht⟩ := hk n hn
  have hm := mu_pos n
  have hd := abs_le.mp (hD n hn)
  have hrow := adm.row
  have hc := adm.c_pos
  have e : mu n * D n = t := by
    refine lift_eq ht ?_
    rw [abs_lt]
    constructor <;> nlinarith
  omega

theorem Typed.byte {D : ℕ → ℤ} (h : Typed D) {n : ℕ} (hn : n < 99) : 0 ≤ D n ∧ D n ≤ 255 := by
  have := h n hn
  have hm := mu_pos n
  constructor <;> nlinarith

theorem b256_succ {K : Type} [CommRing K] (D : ℕ → K) (a n : ℕ) :
    b256 D a (n + 1) = b256 D a n + 256 ^ n * D (a + n) := by
  simp [b256, sum_range_succ]

theorem b256_bounds {D : ℕ → ℤ} (h : Typed D) (a n : ℕ) (han : a + n ≤ 99) :
    0 ≤ b256 D a n ∧ b256 D a n < 256 ^ n := by
  induction n with
  | zero => simp [b256]
  | succ n ih =>
    have ih' := ih (by omega)
    have hb := h.byte (n := a + n) (by omega)
    have hp : (0 : ℤ) < 256 ^ n := by positivity
    rw [b256_succ, pow_succ]
    constructor <;> nlinarith

/-- The ranges of the row values (Step L5, "Known before"). -/
structure Sizes (D : ℕ → ℤ) : Prop where
  s0 : 0 ≤ s0 D ∧ s0 D ≤ 1
  sa : 0 ≤ sa D ∧ sa D < 2 ^ 24
  sb : 0 ≤ sb D ∧ sb D < 2 ^ 15
  Vlo : 0 ≤ Vlo D ∧ Vlo D < 2 ^ 48
  Vhi : 0 ≤ Vhi D ∧ Vhi D < 2 ^ 30
  l1 : 0 ≤ l1 D ∧ l1 D < 2 ^ 40
  h1 : 0 ≤ h1 D ∧ h1 D < 2 ^ 40
  Blo : 0 ≤ Blo D ∧ Blo D < 2 ^ 23
  Bhi : 0 ≤ Bhi D ∧ Bhi D < 2 ^ 16
  kc : -4 ≤ kc D ∧ kc D ≤ 3
  Rlo : 0 ≤ Rlo D ∧ Rlo D < 2 ^ 24
  Rhi : 0 ≤ Rhi D ∧ Rhi D < 2 ^ 24
  q1 : 0 ≤ q1 D ∧ q1 D < 2 ^ 24
  rr : 0 ≤ rr D ∧ rr D < 2 ^ 40
  rq : 0 ≤ rq D ∧ rq D < 2 ^ 40
  /-- ς minus its parity s0 is even -/
  half : ∃ h : ℤ, sig D = 2 * h + Ledger.s0 D

theorem sizes_of_typed {D : ℕ → ℤ} (ty : Typed D) : Sizes D := by
  have b : ∀ i, i < 99 → 0 ≤ D i ∧ D i ≤ 255 := fun i hi => ty.byte hi
  have t9 := ty 9 (by norm_num); have t58 := ty 58 (by norm_num); have t59 := ty 59 (by norm_num)
  have t63 := ty 63 (by norm_num); have t76 := ty 76 (by norm_num); have t79 := ty 79 (by norm_num)
  norm_num [mu] at t9 t58 t59 t63 t76 t79
  have b60 := b 60 (by norm_num); have b61 := b 61 (by norm_num); have b62 := b 62 (by norm_num)
  have b74 := b 74 (by norm_num); have b75 := b 75 (by norm_num)
  have b6 := b 6 (by norm_num); have b7 := b 7 (by norm_num); have b8 := b 8 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Ledger.s0; omega
  · unfold Ledger.sa; omega
  · unfold Ledger.sb; omega
  · simpa [Ledger.Vlo] using b256_bounds ty 0 6 (by norm_num)
  · simp only [Ledger.Vhi, b256, sum_range_succ, sum_range_zero]; norm_num; omega
  · simpa [Ledger.l1] using b256_bounds ty 64 5 (by norm_num)
  · simpa [Ledger.h1] using b256_bounds ty 69 5 (by norm_num)
  · simp only [Ledger.Blo, b256, sum_range_succ, sum_range_zero]; norm_num; omega
  · simpa [Ledger.Bhi] using b256_bounds ty 77 2 (by norm_num)
  · unfold Ledger.kc; omega
  · simpa [Ledger.Rlo] using b256_bounds ty 80 3 (by norm_num)
  · simpa [Ledger.Rhi] using b256_bounds ty 83 3 (by norm_num)
  · simpa [Ledger.q1] using b256_bounds ty 86 3 (by norm_num)
  · simpa [Ledger.rr] using b256_bounds ty 89 5 (by norm_num)
  · simpa [Ledger.rq] using b256_bounds ty 94 5 (by norm_num)
  · exact ⟨D 58 + 2 ^ 7 * D 60 + 2 ^ 15 * D 61 + 2 ^ 23 * sb D,
      by unfold sig Ledger.sa Ledger.s0; ring⟩

/-- If `Typed D`, every carry c_s, s ≤ 9, is in [−2^47, 2^47). -/
theorem cs_bounds {D : ℕ → ℤ} (ty : Typed D) {s : ℕ} (hs : s ≤ 9) :
    -2 ^ 47 ≤ cs D s ∧ cs D s < 2 ^ 47 := by
  unfold cs
  split_ifs with h0 h9
  · norm_num
  · have := ty.byte (n := 9) (by norm_num)
    constructor <;> linarith
  · have := b256_bounds ty (10 + 6 * (s - 1)) 6 (by omega)
    norm_num at this ⊢
    constructor <;> linarith

/-! ## 3. The identities, one by one -/

section Unfold
variable {K : Type} [CommRing K] (np : NormPar) (Ws D : ℕ → K)

theorem idn_j1 {k : ℕ} (hk : k < 9) : idn np Ws D k = Ws k + cs D k - D k - 256 * cs D (k + 1) :=
  if_pos hk
theorem idn_j2 : idn np Ws D 9 = sa D * sb D - Blo D - 2 ^ 23 * Bhi D := rfl
theorem idn_j3 :
    idn np Ws D 10 = Vlo D + (np.eps : K) - sa D ^ 2 - 2 ^ 25 * Blo D - l1 D + 2 ^ 48 * kc D := rfl
theorem idn_j4 : idn np Ws D 11 = Vhi D - Bhi D - sb D ^ 2 - kc D := rfl
theorem idn_j5 : idn np Ws D 12 = l1 D + h1 D - 2 * sig D := rfl
theorem idn_j6 : idn np Ws D 13 = Rlo D * sb D + Rhi D * sa D - q1 D := rfl
theorem idn_j7 : idn np Ws D 14 = Rhi D * sb D := rfl
theorem idn_j8 :
    idn np Ws D 15 =
      2 ^ (np.M + 1) + sig D - s0 D - 2 * (Rlo D * sa D) - 2 ^ 25 * q1 D - 2 * rr D := rfl
theorem idn_j9 : idn np Ws D 16 = rr D + rq D - sig D + 1 := rfl

end Unfold

/-! ## 4. Steps L4 and L5, "Equality": from congruences to equations -/

private theorem abs_conv_le {b : ℕ → ℤ} {c : ℤ} (hb : ∀ l < 5, |b l| ≤ c) (s : ℕ) :
    |∑ l ∈ range 5, ∑ l' ∈ range 5, if l + l' = s then b l * b l' else 0| ≤ 25 * c ^ 2 := by
  have hc : 0 ≤ c := le_trans (abs_nonneg _) (hb 0 (by norm_num))
  have h : |∑ l ∈ range 5, ∑ l' ∈ range 5, if l + l' = s then b l * b l' else 0| ≤ (5 : ℕ) * ((5 : ℕ) * c ^ 2) := by
    refine abs_sum_range_le fun l hl => abs_sum_range_le fun l' hl' => ?_
    split_ifs
    · rw [abs_mul, sq]
      exact mul_le_mul (hb l hl) (hb l' hl') (abs_nonneg _) hc
    · simp only [abs_zero]; positivity
  push_cast at h
  linarith

theorem abs_Wsum_le {d : ℕ} {b : ℕ → ℕ → ℤ} {c : ℤ} (hb : ∀ l < 5, ∀ j < d, |b l j| ≤ c) (s : ℕ) :
    |Wsum d b s| ≤ d * (25 * c ^ 2) :=
  abs_sum_range_le fun j hj => abs_conv_le (b := fun l => b l j) (fun l hl => hb l hl j hj) s

/-- Steps L4 and L5, "Equality": under the hypotheses below the 17 identities hold over the integers
if they hold modulo p. -/
theorem idn_int {p : ℤ} {np : NormPar} {d : ℕ} {c : ℤ} (adm : Adm p np d c) {b : ℕ → ℕ → ℤ}
    {D : ℕ → ℤ} (hb : ∀ l < 5, ∀ j < d, |b l j| ≤ c) (ty : Typed D)
    (h : ∀ k < 17, idn np (Wsum d b) D k ≡ 0 [ZMOD p]) :
    ∀ k < 17, idn np (Wsum d b) D k = 0 := by
  obtain ⟨hs0, hsa, hsb, hVlo, hVhi, hl1, hh1, hBlo, hBhi, hkc, hRlo, hRhi, hq1, hrr, hrq, _⟩ :=
    sizes_of_typed ty
  have pab := mul_bounds hsa.1 hsa.2 hsb.1 hsb.2
  have paa := mul_bounds hsa.1 hsa.2 hsa.1 hsa.2
  have pbb := mul_bounds hsb.1 hsb.2 hsb.1 hsb.2
  have pla := mul_bounds hRlo.1 hRlo.2 hsa.1 hsa.2
  have plb := mul_bounds hRlo.1 hRlo.2 hsb.1 hsb.2
  have pha := mul_bounds hRhi.1 hRhi.2 hsa.1 hsa.2
  have phb := mul_bounds hRhi.1 hRhi.2 hsb.1 hsb.2
  have he0 := adm.eps_pos
  have he1 := adm.eps_lt
  have hbig := adm.big
  have hM : (2 : ℤ) ^ (np.M + 1) ≤ 2 ^ 48 :=
    pow_le_pow_right₀ (by norm_num) (by have := adm.M_le; omega)
  have hM0 : (0 : ℤ) < 2 ^ (np.M + 1) := by positivity
  have hsig : sig D = sa D + 2 ^ 24 * sb D := rfl
  have z : ∀ {a : ℤ}, a ≡ 0 [ZMOD p] → -2 ^ 53 < a → a < 2 ^ 53 → a = 0 :=
    fun h h1 h2 => lift_zero h (abs_lt.mpr ⟨by linarith, by linarith⟩)
  intro k hk
  by_cases hk9 : k < 9
  · refine lift_zero (h k hk) ?_
    rw [idn_j1 np _ _ hk9]
    have hW' := abs_le.mp (abs_Wsum_le hb k)
    have hl := adm.j1
    have c1 := cs_bounds ty (s := k) (by omega)
    have c2 := cs_bounds ty (s := k + 1) (by omega)
    have hD := ty.byte (n := k) (by omega)
    rw [abs_lt]
    constructor <;> nlinarith
  · have hk' := h k hk
    have hcases : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [idn_j2] at hk' ⊢
      exact z hk' (by omega) (by omega)
    · rw [idn_j3] at hk' ⊢
      rw [sq] at hk' ⊢
      simp only [Int.cast_id] at hk' ⊢
      exact z hk' (by omega) (by omega)
    · rw [idn_j4] at hk' ⊢
      rw [sq] at hk' ⊢
      exact z hk' (by omega) (by omega)
    · rw [idn_j5] at hk' ⊢
      exact z hk' (by omega) (by omega)
    · rw [idn_j6] at hk' ⊢
      exact z hk' (by omega) (by omega)
    · rw [idn_j7] at hk' ⊢
      exact z hk' (by omega) (by omega)
    · rw [idn_j8] at hk' ⊢
      generalize (2 : ℤ) ^ (np.M + 1) = tm at *
      exact z hk' (by omega) (by omega)
    · rw [idn_j9] at hk' ⊢
      exact z hk' (by omega) (by omega)

/-! ## 5. Step L4, "New facts": the sum of squares -/

/-- The generating identity of the sums W_s, in any commutative ring: Σ_s γ^s W_s = Σ_j (Σ_l γ^l
b_l[j])². At γ = 256 the right side is the sum of the squares of the values; at a challenge γ it is
the identity behind the vector of squares (`HVt`, Inst/Model/FF/Objects.lean). -/
theorem sum_pow_Wsum {K : Type} [CommRing K] (γ : K) (d : ℕ) (b : ℕ → ℕ → K) :
    ∑ s ∈ range 9, γ ^ s * Wsum d b s = ∑ j ∈ range d, (∑ l ∈ range 5, γ ^ l * b l j) ^ 2 := by
  calc ∑ s ∈ range 9, γ ^ s * Wsum d b s
      = ∑ s ∈ range 9, ∑ j ∈ range d, γ ^ s * ∑ l ∈ range 5, ∑ l' ∈ range 5, if l + l' = s then b l j * b l' j else 0 := by
        simp only [Wsum, mul_sum]
    _ = ∑ j ∈ range d, ∑ s ∈ range 9, γ ^ s * ∑ l ∈ range 5, ∑ l' ∈ range 5, if l + l' = s then
          b l j * b l' j
        else 0 := sum_comm
    _ = _ := sum_congr rfl fun j _ => by
        simp [sum_range_succ]
        ring

/-- Under (J1) over the integers the carries telescope. -/
theorem telescope {np : NormPar} {Ws D : ℕ → ℤ} (h : ∀ k < 9, idn np Ws D k = 0) :
    ∀ n ≤ 9, ∑ s ∈ range n, 256 ^ s * Ws s = b256 D 0 n + 256 ^ n * cs D n - cs D 0 := by
  intro n
  induction n with
  | zero => intro _; simp [b256]
  | succ n ih =>
    intro hn
    have h1 := h n (by omega)
    rw [idn_j1 np _ _ (by omega : n < 9)] at h1
    rw [sum_range_succ, ih (by omega), b256_succ, zero_add, pow_succ]
    linear_combination (256 : ℤ) ^ n * h1

theorem V_split (D : ℕ → ℤ) : b256 D 0 10 = Vlo D + 2 ^ 48 * Vhi D := by
  simp only [Vlo, Vhi, b256, sum_range_succ, sum_range_zero]
  norm_num
  ring

/-- (FL13), first half: under (J1) over the integers, V = Vlo + 2^48 Vhi is the sum of the squares,
whatever cells represent the values. -/
theorem V_eq {np : NormPar} {d : ℕ} {b : ℕ → ℕ → ℤ} {D : ℕ → ℤ}
    (h : ∀ k < 9, idn np (Wsum d b) D k = 0) :
    Vlo D + 2 ^ 48 * Vhi D = NORM.V d (xOf b) := by
  have h1 := telescope h 9 le_rfl
  rw [sum_pow_Wsum] at h1
  have e : b256 D 0 10 = b256 D 0 9 + 256 ^ 9 * D (0 + 9) := b256_succ D 0 9
  rw [← V_split, e]
  have e9 : cs D 9 = D 9 := by simp [cs]
  have e0 : cs D 0 = 0 := by simp [cs]
  rw [e9, e0] at h1
  unfold NORM.V xOf
  rw [h1]
  simp

/-! ## 6. Step L5, "New facts": square root and reciprocal -/

/-- Step L5, "New facts", in terms of the number V' = Vlo + 2^48 Vhi of the ledger, under the
hypotheses below: ς = isqrt(V' + ϵ), 1 ≤ ς < 2^39, V' + ϵ < (ς + 1)², R = ⌊(2^M + ⌊ς/2⌋) / ς⌋. -/
theorem root_recip {np : NormPar} {Ws D : ℕ → ℤ} (ty : Typed D)
    (h : ∀ k < 17, 9 ≤ k → idn np Ws D k = 0) :
    sig D = isqrt (Vlo D + 2 ^ 48 * Vhi D + np.eps) ∧
    1 ≤ sig D ∧ sig D < 2 ^ 39 ∧
    Vlo D + 2 ^ 48 * Vhi D + np.eps < (sig D + 1) * (sig D + 1) ∧
    R D = (2 ^ np.M + sig D / 2) / sig D := by
  obtain ⟨hs0, hsa, hsb, hVlo, hVhi, hl1, hh1, hBlo, hBhi, hkc, hRlo, hRhi,
      hq1, hrr, hrq, hf, hh⟩ :=
    sizes_of_typed ty
  have e0 := h 9 (by norm_num) le_rfl; rw [idn_j2] at e0
  have e1 := h 10 (by norm_num) (by norm_num); rw [idn_j3, sq] at e1; simp only [Int.cast_id] at e1
  have e2 := h 11 (by norm_num) (by norm_num); rw [idn_j4, sq] at e2
  have e3 := h 12 (by norm_num) (by norm_num); rw [idn_j5] at e3
  have r1 := h 13 (by norm_num) (by norm_num); rw [idn_j6] at r1
  have r2 := h 14 (by norm_num) (by norm_num); rw [idn_j7] at r2
  have r3 := h 15 (by norm_num) (by norm_num); rw [idn_j8] at r3
  have r4 := h 16 (by norm_num) (by norm_num); rw [idn_j9] at r4
  have hsig : sig D = sa D + 2 ^ 24 * sb D := rfl
  have hsig0 : 0 ≤ sig D := by omega
  have hs39 : sig D < 2 ^ 39 := by omega
  -- (J3) + 2^48 (J4), with (J2): V + ϵ = ς² + l1; kc cancels
  have hsq : sig D * sig D = sa D * sa D + 2 ^ 25 * (sa D * sb D) + 2 ^ 48 * (sb D * sb D) := by
    rw [hsig]; ring
  have hVe : Vlo D + 2 ^ 48 * Vhi D + np.eps = sig D * sig D + l1 D := by rw [hsq]; omega
  have hpos : 1 ≤ sig D := by
    by_contra hc
    have h0 : sig D = 0 := by omega
    rw [h0] at hVe e3
    omega
  have hup : Vlo D + 2 ^ 48 * Vhi D + np.eps < (sig D + 1) * (sig D + 1) := by
    have : (sig D + 1) * (sig D + 1) = sig D * sig D + 2 * sig D + 1 := by ring
    omega
  -- R ς = Rlo sa + 2^24 q1 by (J6), (J7); (J8) halves to 2^M + ⌊ς/2⌋ = R ς + rr; (J9): rr < ς
  have hRs : sig D * R D =
      Rlo D * sa D + 2 ^ 24 * (Rlo D * sb D + Rhi D * sa D) + 2 ^ 48 * (Rhi D * sb D) := by
    rw [hsig]; unfold R; ring
  have hhalf : sig D / 2 = hf := by omega
  have hpow : (2 : ℤ) ^ (np.M + 1) = 2 * 2 ^ np.M := by ring
  rw [hpow] at r3
  have key : rr D + sig D * R D = 2 ^ np.M + sig D / 2 := by
    rw [hRs, hhalf]
    generalize (2 : ℤ) ^ np.M = tm at *
    omega
  exact ⟨(isqrt_eq hsig0 (by omega) hup).symm, hpos, hs39, hup,
    ((Int.ediv_emod_unique (by omega)).mpr ⟨key, hrr.1, by omega⟩).1.symm⟩

/-- Steps L4 and L5, "New facts": under the hypotheses below, (FL13) to (FL17) hold: V, ς, R of the
ledger are `NORM.V`, `NORM.sig`, `NORM.R` of the integer model for the values that the five cells
represent; V + ϵ < 2^78; 1 ≤ ς < 2^39; |x[j]| < 2^39; |x[j] R| < 2^M + 2^38. -/
theorem sound_int {np : NormPar} {d : ℕ} {b : ℕ → ℕ → ℤ} {D : ℕ → ℤ} (he0 : 0 ≤ np.eps)
    (ty : Typed D) (h : ∀ k < 17, idn np (Wsum d b) D k = 0) :
    Vlo D + 2 ^ 48 * Vhi D = NORM.V d (xOf b) ∧
    sig D = NORM.sig np d (xOf b) ∧
    R D = NORM.R np d (xOf b) ∧
    NORM.V d (xOf b) + np.eps < 2 ^ 78 ∧
    1 ≤ sig D ∧ sig D < 2 ^ 39 ∧
    (∀ j < d, |xOf b j| < 2 ^ 39) ∧
    (∀ j < d, |xOf b j * R D| < 2 ^ np.M + 2 ^ 38) := by
  have hV := V_eq (np := np) (d := d) (b := b) (D := D) fun k hk => h k (by omega)
  obtain ⟨hroot, hpos, hs39, hup, hR⟩ := root_recip ty fun k hk _ => h k hk
  rw [hV] at hroot hup
  have hx : ∀ j < d, |xOf b j| ≤ sig D := by
    intro j hj
    have h1 : xOf b j ^ 2 ≤ NORM.V d (xOf b) :=
      single_le_sum (f := fun k => xOf b k ^ 2) (fun i _ => sq_nonneg _) (mem_range.mpr hj)
    have h2 : xOf b j ^ 2 < (sig D + 1) ^ 2 := by
      rw [sq (sig D + 1)]
      linarith
    have h3' := sq_lt_sq.mp h2
    rw [abs_of_nonneg (by linarith : (0 : ℤ) ≤ sig D + 1)] at h3'
    linarith
  have hR0 : 0 ≤ R D := by
    rw [hR]
    apply Int.ediv_nonneg _ (by linarith)
    have : 0 ≤ sig D / 2 := Int.ediv_nonneg (by linarith) (by norm_num)
    positivity
  have hRs' : R D * sig D ≤ 2 ^ np.M + sig D / 2 := by
    rw [hR]; exact Int.ediv_mul_le _ (by linarith)
  have h78 : (sig D + 1) * (sig D + 1) ≤ 2 ^ 39 * 2 ^ 39 :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  refine ⟨hV, hroot, ?_, ?_, hpos, hs39, fun j hj => lt_of_le_of_lt (hx j hj) hs39, fun j hj => ?_⟩
  · unfold NORM.R
    rw [← show sig D = NORM.sig np d (xOf b) from hroot]
    exact hR
  · have e : (2 : ℤ) ^ 39 * 2 ^ 39 = 2 ^ 78 := by norm_num
    linarith
  · have h1 : |xOf b j * R D| ≤ sig D * R D := by
      rw [abs_mul, abs_of_nonneg hR0]
      exact mul_le_mul_of_nonneg_right (hx j hj) hR0
    have h2 : sig D / 2 < 2 ^ 38 := by omega
    linarith

/-- The ledger is sound: under `Adm`, small cells and, modulo p, the keys of ROW in their table and
the 17 identities imply (N1) to (N3) of the integer model and its range condition V + ϵ < 2^78. -/
theorem ledger_sound {p : ℤ} {np : NormPar} {d : ℕ} {c : ℤ} (adm : Adm p np d c) {b : ℕ → ℕ → ℤ}
    {D : ℕ → ℤ} (hb : ∀ l < 5, ∀ j < d, |b l j| ≤ c) (hD : ∀ n < 99, |D n - 128| ≤ c)
    (hk : ∀ n < 99, ∃ t : ℤ, 0 ≤ t ∧ t < 256 ∧ mu n * D n ≡ t [ZMOD p])
    (h : ∀ k < 17, idn np (Wsum d b) D k ≡ 0 [ZMOD p]) :
    Typed D ∧
    Vlo D + 2 ^ 48 * Vhi D = NORM.V d (xOf b) ∧
    sig D = NORM.sig np d (xOf b) ∧
    R D = NORM.R np d (xOf b) ∧
    NORM.V d (xOf b) + np.eps < 2 ^ 78 ∧
    1 ≤ sig D ∧ sig D < 2 ^ 39 ∧
    (∀ j < d, |xOf b j| < 2 ^ 39) ∧
    (∀ j < d, |xOf b j * R D| < 2 ^ np.M + 2 ^ 38) :=
  have ty := typed_of_keys adm hD hk
  ⟨ty, sound_int (le_trans (by norm_num) adm.eps_pos) ty (idn_int adm hb ty h)⟩

/-! ## 7. Ring homomorphisms, and identities in a ring of characteristic p -/

section Map
variable {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (D : ℕ → K)

theorem map_b256 (a n : ℕ) : f (b256 D a n) = b256 (fun m => f (D m)) a n := by
  simp [map_ofNat, b256, map_sum, map_mul, map_pow]

theorem map_Vlo : f (Vlo D) = Vlo fun m => f (D m) := map_b256 f D _ _
theorem map_Vhi : f (Vhi D) = Vhi fun m => f (D m) := map_b256 f D _ _
theorem map_l1 : f (l1 D) = l1 fun m => f (D m) := map_b256 f D _ _
theorem map_h1 : f (h1 D) = h1 fun m => f (D m) := map_b256 f D _ _
theorem map_Blo : f (Blo D) = Blo fun m => f (D m) := map_b256 f D _ _
theorem map_Bhi : f (Bhi D) = Bhi fun m => f (D m) := map_b256 f D _ _
theorem map_Rlo : f (Rlo D) = Rlo fun m => f (D m) := map_b256 f D _ _
theorem map_Rhi : f (Rhi D) = Rhi fun m => f (D m) := map_b256 f D _ _
theorem map_q1 : f (q1 D) = q1 fun m => f (D m) := map_b256 f D _ _
theorem map_rr : f (rr D) = rr fun m => f (D m) := map_b256 f D _ _
theorem map_rq : f (rq D) = rq fun m => f (D m) := map_b256 f D _ _
theorem map_s0 : f (s0 D) = s0 fun m => f (D m) := rfl
theorem map_sa : f (sa D) = sa fun m => f (D m) := by simp [map_ofNat, sa]
theorem map_sb : f (sb D) = sb fun m => f (D m) := by simp [map_ofNat, sb]
theorem map_sig : f (sig D) = sig fun m => f (D m) := by simp [map_ofNat, sig, map_sa, map_sb]
theorem map_kc : f (kc D) = kc fun m => f (D m) := by simp [map_ofNat, kc]
theorem map_R : f (R D) = R fun m => f (D m) := by simp [map_ofNat, R, map_Rlo, map_Rhi]

theorem map_cs (s : ℕ) : f (cs D s) = cs (fun m => f (D m)) s := by
  unfold cs
  split_ifs
  · exact map_zero f
  · rfl
  · simp [map_ofNat, map_b256]

theorem map_Wsum (d : ℕ) (b : ℕ → ℕ → K) (s : ℕ) :
    f (Wsum d b s) = Wsum d (fun l j => f (b l j)) s := by
  unfold Wsum
  simp only [map_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => sum_congr rfl fun l' _ => ?_
  split_ifs
  · exact map_mul f _ _
  · exact map_zero f

/-- For k ≥ 17, `idn` is 0. -/
theorem idn_of_le (np : NormPar) (Ws : ℕ → K) {k : ℕ} (hk : 17 ≤ k) : idn np Ws D k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 17 := ⟨k - 17, by omega⟩
  unfold idn
  rw [if_neg (by omega)]
  rfl

/-- A ring homomorphism commutes with the identities. -/
theorem map_idn (np : NormPar) (Ws : ℕ → K) (k : ℕ) :
    f (idn np Ws D k) = idn np (fun s => f (Ws s)) (fun m => f (D m)) k := by
  by_cases hk9 : k < 9
  · rw [idn_j1 np _ _ hk9, idn_j1 np _ _ hk9]
    simp [map_ofNat, map_cs]
  · by_cases hk17 : 17 ≤ k
    · rw [idn_of_le D np Ws hk17, idn_of_le _ np _ hk17, map_zero]
    · have hcases : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [map_ofNat, idn_j2, map_sa, map_sb, map_Blo, map_Bhi]
      · simp [map_ofNat, idn_j3, map_Vlo, map_sa, map_Blo, map_l1, map_kc]
      · simp [idn_j4, map_Vhi, map_Bhi, map_sb, map_kc]
      · simp [map_ofNat, idn_j5, map_l1, map_h1, map_sig]
      · simp [idn_j6, map_Rlo, map_Rhi, map_sa, map_sb, map_q1]
      · simp [idn_j7, map_Rhi, map_sb]
      · simp [map_ofNat, idn_j8, map_sig, map_s0, map_Rlo, map_sa, map_q1, map_rr]
      · simp [idn_j9, map_rr, map_rq, map_sig]

end Map

/-- An identity that holds in a ring of characteristic p on the images of integers is a congruence
modulo p. -/
theorem idn_cast_eq_zero_iff
    (K : Type) [CommRing K] (p : ℕ) [CharP K p] (np : NormPar) (Ws D : ℕ → ℤ) (k : ℕ) :
    idn np (fun s => ((Ws s : ℤ) : K)) (fun m => ((D m : ℤ) : K)) k = 0 ↔
    idn np Ws D k ≡ 0 [ZMOD (p : ℤ)] := by
  have h := map_idn (Int.castRingHom K) D np Ws k
  simp only [eq_intCast] at h
  rw [← h, CharP.intCast_eq_zero_iff K p, Int.modEq_zero_iff_dvd]

/-- The same for a key of ROW and an entry of its table. -/
theorem key_cast_eq_iff (K : Type) [CommRing K] (p : ℕ) [CharP K p] (a t : ℤ) :
    ((a : ℤ) : K) = ((t : ℤ) : K) ↔ a ≡ t [ZMOD (p : ℤ)] :=
  CharP.intCast_eq_intCast K p

end Inst.Model.Ledger
