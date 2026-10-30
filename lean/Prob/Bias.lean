-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/Bias.lean: residues modulo p made from a uniform number below N.

The bias of a map φ : U → K, for finite non-empty U and K, is the statistical distance `Prob.tv`
between φ(u), for uniform u, and the uniform distribution on K.

  * Under φ(u), u uniform, an event has at most its uniform probability plus the bias of φ
    (`pr_preimage_le`), and the bias of a pair of independent components is at most the sum of the
    biases.
  * A uniform number below N, reduced modulo p, for N ≠ 0 and p ≠ 0, has bias exactly
    r (p - r) / (N p) with r = N mod p (`tv_natCast_fin_eq`), which is at most p / (4 N).
  * In multiplicative form: if every value has at most w preimages and w |K| ≤ κ |U|,
    then a count of bad values grows by at most the factor w and a probability by at most the factor
    κ.
  * Section 0 also has three bounds on (1 + x)^n (`one_add_pow_le_sq`, `one_add_pow_le`,
    `one_add_two_pow_inv_pow_le`), which sections 1 and 2 do not use.

Not here: a sampler that makes several attempts, and statements about protocols.

The count of the numbers below N in a residue class is
Mathlib's Nat.count_modEq_card.
-/
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Prob.Tv
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal

namespace Prob

/-! ## 0. Fractions of natural numbers among the extended non-negative reals; bounds on (1 + x)^n -/

/-- For b ≠ 0 and d ≠ 0, a / b ≤ c / d follows from a d ≤ c b. -/
theorem natCast_div_le_div {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d ≤ c * b) :
    (a : ℝ≥0∞) / b ≤ (c : ℝ≥0∞) / d := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd
  rw [ENNReal.div_le_iff hb0 (ENNReal.natCast_ne_top b), ← ENNReal.mul_div_right_comm,
    ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl (ENNReal.natCast_ne_top d))]
  exact_mod_cast h

/-- For b ≠ 0 and d ≠ 0, a / b < c / d follows from a d < c b. -/
theorem natCast_div_lt_div {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d < c * b) :
    (a : ℝ≥0∞) / b < (c : ℝ≥0∞) / d := by
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd
  rw [ENNReal.div_lt_iff (Or.inl hb0) (Or.inl (ENNReal.natCast_ne_top b)),
    ← ENNReal.mul_div_right_comm,
    ENNReal.lt_div_iff_mul_lt (Or.inl hd0) (Or.inl (ENNReal.natCast_ne_top d))]
  exact_mod_cast h

/-- For N ≠ 0 and p ≠ 0: a / N - 1 / p = (a p - N) / (N p), both subtractions truncated at 0. -/
theorem natCast_div_sub_inv (a : ℕ) {N p : ℕ} (hN : N ≠ 0) (hp : p ≠ 0) :
    (a : ℝ≥0∞) / N - (p : ℝ≥0∞)⁻¹ = ((a * p - N : ℕ) : ℝ≥0∞) / ((N * p : ℕ) : ℝ≥0∞) := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp
  have hNp0 : ((N * p : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hN hp
  have h1 : (a : ℝ≥0∞) / N = ((a * p : ℕ) : ℝ≥0∞) / ((N * p : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul, Nat.cast_mul, ENNReal.mul_div_mul_right _ _ hp0 (ENNReal.natCast_ne_top p)]
  have h2 : (p : ℝ≥0∞)⁻¹ = (N : ℝ≥0∞) / ((N * p : ℕ) : ℝ≥0∞) := by
    calc (p : ℝ≥0∞)⁻¹ = 1 / p := (one_div _).symm
      _ = 1 * N / (p * N) :=
        (ENNReal.mul_div_mul_right 1 (p : ℝ≥0∞) hN0 (ENNReal.natCast_ne_top N)).symm
      _ = (N : ℝ≥0∞) / ((N * p : ℕ) : ℝ≥0∞) := by rw [one_mul, mul_comm (p : ℝ≥0∞) N, Nat.cast_mul]
  rw [h1, h2, ENNReal.natCast_sub, ENNReal.sub_div fun _ _ => hNp0]

/-- (1 + x)^n ≤ 1 + n x + (n x)^2 as long as n x ≤ 1. -/
theorem one_add_pow_le_sq (x : ℝ≥0∞) :
    ∀ n : ℕ, (n : ℝ≥0∞) * x ≤ 1 → (1 + x) ^ n ≤ 1 + n * x + (n * x) ^ 2
  | 0, _ => by simp
  | n + 1, h => by
    have hn : (n : ℝ≥0∞) * x ≤ 1 :=
      le_trans (mul_le_mul' (by exact_mod_cast Nat.le_succ n) le_rfl) h
    have ih := one_add_pow_le_sq x n hn
    have h3 : ((n : ℝ≥0∞) * x) ^ 2 * x ≤ n * x * x := by
      calc ((n : ℝ≥0∞) * x) ^ 2 * x = (n * x) * (n * x * x) := by ring
        _ ≤ 1 * (n * x * x) := mul_le_mul' hn le_rfl
        _ = n * x * x := one_mul _
    calc (1 + x) ^ (n + 1) = (1 + x) ^ n * (1 + x) := pow_succ _ _
      _ ≤ (1 + n * x + (n * x) ^ 2) * (1 + x) := mul_le_mul' ih le_rfl
      _ = 1 + (n + 1) * x + (n * x) ^ 2 + n * x * x + (n * x) ^ 2 * x := by ring
      _ ≤ 1 + (n + 1) * x + (n * x) ^ 2 + n * x * x + n * x * x := add_le_add le_rfl h3
      _ ≤ 1 + (n + 1) * x + (n * x) ^ 2 + n * x * x + n * x * x + x * x := le_self_add
      _ = 1 + ((n + 1 : ℕ) : ℝ≥0∞) * x + (((n + 1 : ℕ) : ℝ≥0∞) * x) ^ 2 := by push_cast; ring

/-- (1 + x)^n ≤ 1 + 2 n x as long as n x ≤ 1. -/
theorem one_add_pow_le (x : ℝ≥0∞) (n : ℕ) (h : (n : ℝ≥0∞) * x ≤ 1) : (1 + x) ^ n ≤ 1 + 2 * n * x :=
  (one_add_pow_le_sq x n h).trans (by
    calc 1 + (n : ℝ≥0∞) * x + (n * x) ^ 2 = 1 + n * x + (n * x) * (n * x) := by ring
      _ ≤ 1 + n * x + 1 * (n * x) := add_le_add le_rfl (mul_le_mul' h le_rfl)
      _ = 1 + 2 * n * x := by ring)

/-- (1 + 2^-λ)^n ≤ 1 + 2 n 2^-λ for n ≤ 2^λ. -/
theorem one_add_two_pow_inv_pow_le (lam n : ℕ) (h : n ≤ 2 ^ lam) :
    (1 + (2 ^ lam : ℝ≥0∞)⁻¹) ^ n ≤ 1 + 2 * n * (2 ^ lam : ℝ≥0∞)⁻¹ := by
  refine one_add_pow_le _ n ?_
  calc
    (n : ℝ≥0∞) * (2 ^ lam : ℝ≥0∞)⁻¹ ≤ 2 ^ lam * (2 ^ lam : ℝ≥0∞)⁻¹ :=
      mul_le_mul' (by exact_mod_cast h) le_rfl
    _ = 1 := ENNReal.mul_inv_cancel (pow_ne_zero _ (by norm_num)) (ENNReal.pow_ne_top (by norm_num))

/-! ## 1. What a bias costs -/

section General

variable {U V K L : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V] [Fintype K] [Nonempty K]
  [Fintype L] [Nonempty L]

/-- The preimage under φ of a set of values has at most the probability of the set plus the bias of
φ. -/
theorem pr_preimage_le (φ : U → K) (S : Set K) :
    pr (unif U) (φ ⁻¹' S) ≤ pr (unif K) S + tv ((unif U).map φ) (unif K) := by
  rw [← pr_map]
  exact pr_le_pr_add_tv _ _ S

/-- If at most k values of a challenge are bad, then the challenge φ(u), u uniform, is bad with
probability at most k / |K| plus the bias β of φ (the error ε becomes ε + β). -/
theorem pr_of_cnt_le (φ : U → K) {P : K → Prop} {k : ℕ} (h : cnt P ≤ k) :
    pr (unif U) {u | P (φ u)} ≤ (k : ℝ≥0∞) / Fintype.card K + tv ((unif U).map φ) (unif K) :=
  (pr_preimage_le φ {x | P x}).trans (by gcongr; exact pr_unif_le_of_cnt_le h)

omit [Nonempty U] [Nonempty K] in
/-- If every value has at most w preimages under φ, then a set of values has at most w times as many
preimages as elements. -/
theorem cnt_comp_le (φ : U → K) {w : ℕ} (hw : ∀ c, cnt (fun a => φ a = c) ≤ w) (P : K → Prop) :
    cnt (fun a => P (φ a)) ≤ cnt P * w := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (s := Finset.univ.filter fun a => P (φ a))
      (t := Finset.univ.filter P) (fun a ha => by simpa using ha)]
  calc ∑ c ∈ Finset.univ.filter P, ((Finset.univ.filter fun a => P (φ a)).filter fun a => φ a = c).card
      ≤ ∑ _c ∈ Finset.univ.filter P, w := by
        refine Finset.sum_le_sum fun c _ => ?_
        refine (Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans ?_
        rw [← cnt_eq_card_filter]
        exact hw c
    _ = (Finset.univ.filter P).card * w := by rw [Finset.sum_const, smul_eq_mul]

/-- The bias in multiplicative form. If every value has at most w preimages under φ and w |K| ≤ κ
|U|, then the preimage of a set of values has at most κ times the probability of the set. -/
theorem pr_preimage_le_mul (φ : U → K) {w : ℕ} (hw : ∀ c, cnt (fun a => φ a = c) ≤ w) {κ : ℝ≥0∞}
    (hκ : (w : ℝ≥0∞) * Fintype.card K ≤ κ * Fintype.card U) (S : Set K) :
    pr (unif U) (φ ⁻¹' S) ≤ κ * pr (unif K) S := by
  have h1 : pr (unif U) (φ ⁻¹' S) = (cnt (fun a => φ a ∈ S) : ℝ≥0∞) / Fintype.card U :=
    pr_unif_eq fun a => φ a ∈ S
  have h2 : pr (unif K) S = (cnt (fun c => c ∈ S) : ℝ≥0∞) / Fintype.card K :=
    pr_unif_eq fun c => c ∈ S
  have h3 : (cnt (fun a => φ a ∈ S) : ℝ≥0∞) ≤ (cnt (fun c => c ∈ S) : ℝ≥0∞) * w := by
    exact_mod_cast cnt_comp_le φ hw fun c => c ∈ S
  rw [h1, h2, ENNReal.div_le_iff (card_ne_zero' U) (card_ne_top' U)]
  calc (cnt (fun a => φ a ∈ S) : ℝ≥0∞) ≤ (cnt (fun c => c ∈ S) : ℝ≥0∞) * w := h3
    _ = (cnt (fun c => c ∈ S) : ℝ≥0∞) * w * ((Fintype.card K : ℝ≥0∞)⁻¹ * Fintype.card K) := by
        rw [ENNReal.inv_mul_cancel (card_ne_zero' K) (card_ne_top' K), mul_one]
    _ = (cnt (fun c => c ∈ S) : ℝ≥0∞) / Fintype.card K * ((w : ℝ≥0∞) * Fintype.card K) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ (cnt (fun c => c ∈ S) : ℝ≥0∞) / Fintype.card K * (κ * Fintype.card U) := by gcongr
    _ = κ * ((cnt (fun c => c ∈ S) : ℝ≥0∞) / Fintype.card K) * Fintype.card U := by ring

/-- Applying one map to each of two independent draws gives two independent draws. -/
theorem map_prod_map {α β γ δ : Type} (p : PMF α) (q : PMF β) (f : α → γ) (g : β → δ) :
    (prod p q).map (Prod.map f g) = prod (p.map f) (q.map g) :=
  ext_of_expect fun F => by
    simp only [expect_map, expect_prod, Prod.map_apply]

/-- The bias of a pair of components with independent uniform inputs is at most the sum of the two
biases. -/
theorem tv_map_pair_le (φ : U → K) (ψ : V → L) :
    tv ((unif (U × V)).map (Prod.map φ ψ)) (unif (K × L))
      ≤ tv ((unif U).map φ) (unif K) + tv ((unif V).map ψ) (unif L) := by
  rw [unif_prod, unif_prod, map_prod_map]
  exact tv_prod_le _ _ _ _


end General

/-! ## 2. A uniform number below N, reduced modulo p -/

/-- A count over the numbers below N, as Mathlib's Nat.count. -/
theorem cnt_fin_eq_count (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    cnt (fun i : Fin N => Q i) = Nat.count Q N := by
  rw [cnt_eq_card_filter, Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun i _ => (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simpa using hi
  · intro i _ j _ h
    exact Fin.ext h
  · intro k hk
    have hk' : k < N ∧ Q k := by simpa using hk
    exact ⟨⟨k, hk'.1⟩, by simpa using hk'.2, rfl⟩

/-- For p > 0: of the numbers below N, ⌊N / p⌋ + 1 are congruent to v modulo p if v mod p < N mod p,
and ⌊N / p⌋ otherwise. -/
theorem cnt_fin_modEq (N : ℕ) {p : ℕ} (hp : 0 < p) (v : ℕ) :
    cnt (fun i : Fin N => (i : ℕ) ≡ v [MOD p]) = N / p + if v % p < N % p then 1 else 0 := by
  rw [cnt_fin_eq_count N (· ≡ v [MOD p]), Nat.count_modEq_card N hp v]

/-- For p ≠ 0: of the numbers below N, ⌊N / p⌋ + 1 lie in the residue class x if the representative
of x is below N mod p, and ⌊N / p⌋ otherwise. -/
theorem cnt_natCast_eq (N p : ℕ) [NeZero p] (x : ZMod p) :
    cnt (fun i : Fin N => ((i : ℕ) : ZMod p) = x) = N / p + if x.val < N % p then 1 else 0 := by
  have hiff : ∀ i : Fin N, (((i : ℕ) : ZMod p) = x ↔ (i : ℕ) ≡ x.val [MOD p]) := by
    intro i
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  rw [cnt_congr hiff, cnt_fin_eq_count N (· ≡ x.val [MOD p]),
    Nat.count_modEq_card N (NeZero.pos p) x.val, Nat.mod_eq_of_lt (ZMod.val_lt x)]

/-- For p ≠ 0 and r ≤ p, exactly r residue classes modulo p have a representative below r. -/
theorem cnt_val_lt {p r : ℕ} [NeZero p] (hr : r ≤ p) : cnt (fun x : ZMod p => x.val < r) = r := by
  rw [cnt_eq_card_filter]
  conv_rhs => rw [← Finset.card_range r]
  refine Finset.card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    simpa using hx
  · intro x _ y _ h
    exact ZMod.val_injective p h
  · intro k hk
    have hk' : k < r := by simpa using hk
    have hv : ((k : ℕ) : ZMod p).val = k := ZMod.val_cast_of_lt (hk'.trans_le hr)
    exact ⟨(k : ZMod p), by simpa [hv] using hk', hv⟩

/-- The bias of reduction modulo p on the numbers below N: r (p - r) / (N p) with r = N mod p. -/
def modBias (N p : ℕ) : ℝ≥0∞ :=
  ((N % p * (p - N % p) : ℕ) : ℝ≥0∞) / ((N * p : ℕ) : ℝ≥0∞)

/-- A uniform number below N, reduced modulo p, for N ≠ 0 and p ≠ 0, has statistical distance
exactly r (p - r) / (N p) from uniform, where r = N mod p. -/
theorem tv_natCast_fin_eq (N p : ℕ) [NeZero N] [NeZero p] :
    tv ((unif (Fin N)).map fun i : Fin N => ((i : ℕ) : ZMod p)) (unif (ZMod p)) = modBias N p := by
  have hN : N ≠ 0 := NeZero.ne N
  have hp : p ≠ 0 := NeZero.ne p
  have hlt : N % p < p := Nat.mod_lt N (NeZero.pos p)
  have hpoint : ∀ x : ZMod p, (unif (Fin N)).map (fun i : Fin N => ((i : ℕ) : ZMod p)) x -
        unif (ZMod p) x =
      if x.val < N % p then ((p - N % p : ℕ) : ℝ≥0∞) / ((N * p : ℕ) : ℝ≥0∞) else 0 := by
    intro x
    rw [map_unif_apply, cnt_natCast_eq, PMF.uniformOfFintype_apply, Fintype.card_fin, ZMod.card,
      natCast_div_sub_inv _ hN hp]
    have hdiv : p * (N / p) + N % p = N := Nat.div_add_mod N p
    split_ifs with h
    · have e : (N / p + 1) * p - N = p - N % p := by
        have e1 : (N / p + 1) * p = p * (N / p) + p := by ring
        omega
      rw [e]
    · have e : (N / p + 0) * p - N = 0 := by
        have e1 : (N / p + 0) * p = p * (N / p) := by ring
        omega
      rw [e, Nat.cast_zero, ENNReal.zero_div]
  rw [tv_eq_sum_tsub, Finset.sum_congr rfl fun x _ => hpoint x, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, ← cnt_eq_card_filter, cnt_val_lt hlt.le,
    nsmul_eq_mul, modBias, Nat.cast_mul (N % p), mul_div_assoc]

/-- For N ≠ 0 and p ≠ 0 the bias is at most p / (4 N). -/
theorem modBias_le (N p : ℕ) (hN : N ≠ 0) (hp : p ≠ 0) :
    modBias N p ≤ (p : ℝ≥0∞) / ((4 * N : ℕ) : ℝ≥0∞) := by
  have hlt : N % p < p := Nat.mod_lt N (Nat.pos_of_ne_zero hp)
  refine natCast_div_le_div (Nat.mul_ne_zero hN hp) (Nat.mul_ne_zero (by norm_num) hN) ?_
  have h4 : 4 * (N % p) * (p - N % p) ≤ p ^ 2 := by
    have h := four_mul_le_sq_add (N % p) (p - N % p)
    rwa [Nat.add_sub_cancel' hlt.le] at h
  calc N % p * (p - N % p) * (4 * N) = 4 * (N % p) * (p - N % p) * N := by ring
    _ ≤ p ^ 2 * N := Nat.mul_le_mul_right N h4
    _ = p * (N * p) := by ring

end Prob
