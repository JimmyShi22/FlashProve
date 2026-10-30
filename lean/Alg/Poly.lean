-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Alg/Poly.lean: how many values of a random challenge can satisfy a polynomial equation that does not
hold identically.

Main names:
  `count_roots_le`, `count_eval_eq_le`: polynomials in one variable
  `DegLE`: bounded degree in each variable; `DegLE.count_update_le`, `DegLE.count_zero_le`: the
    Schwartz-Zippel lemma, one coordinate at a time and for a whole tuple (the multilinear identity,
    `count_eqN_zero_le` in Alg/Mle.lean, in the generality of any degrees)
  `count_affine_le_one`, `count_affine_form_le`, `count_affine_form_le_pow`: random linear
    combinations with independent coefficients: the one bad value of the last coefficient that
    matters; the coefficients as one tuple
  `count_powers_le`: powers of one challenge as coefficients
  `count_bilinear_mul_le`: a bilinear identity

All statements hold for a finite commutative domain K. Counts are `Nat.card` of a subtype.
-/
import Alg.Count
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace Alg

open Finset Polynomial

/-! ## Roots of a polynomial in one variable -/

section Roots

variable {K : Type*} [CommRing K] [IsDomain K] [Finite K]

/-- A non-zero polynomial of degree at most d has at most d roots. -/
theorem count_roots_le {q : K[X]} (hq : q ≠ 0) {d : ℕ} (hd : q.natDegree ≤ d) :
    Nat.card {r : K // q.eval r = 0} ≤ d := by
  classical
  cases nonempty_fintype K
  rw [count_eq_card_filter]
  have hsub : (univ.filter fun r => q.eval r = 0) ⊆ q.roots.toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset, mem_roots hq]
    exact (mem_filter.mp hr).2
  exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ((card_roots' q).trans hd))

/-- Two different polynomials of degree at most d agree at no more than d points. -/
theorem count_eval_eq_le {g h : K[X]} (hne : g ≠ h) {d : ℕ}
    (hg : g.natDegree ≤ d) (hh : h.natDegree ≤ d) :
    Nat.card {r : K // g.eval r = h.eval r} ≤ d := by
  have := count_roots_le (sub_ne_zero.mpr hne) ((natDegree_sub_le g h).trans (max_le hg hh))
  refine le_trans (count_mono fun r hr => ?_) this
  rw [eval_sub, hr, sub_self]

/-- Powers of one challenge. If not all of the m values a_0, ..., a_(m-1) are 0, then
∑_j γ^(j + s) a_j = 0 for at most m - 1 + s values of γ. With s = 1 the exponents start at 1, and
γ = 0 is then a root for every choice of the a_j. -/
theorem count_powers_le {m : ℕ} (a : Fin m → K) (ha : a ≠ 0) (s : ℕ) :
    Nat.card {γ : K // ∑ j : Fin m, γ ^ ((j : ℕ) + s) * a j = 0} ≤ m - 1 + s := by
  classical
  set q : K[X] := ∑ j : Fin m, monomial ((j : ℕ) + s) (a j) with hq
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp ha
  have hcoeff : q.coeff ((j0 : ℕ) + s) = a j0 := by
    rw [hq, finset_sum_coeff, sum_eq_single j0]
    · simp
    · intro j _ hj
      rw [coeff_monomial, if_neg]
      intro h
      exact hj (Fin.ext (by omega))
    · intro h; exact absurd (mem_univ _) h
  have hne : q ≠ 0 := fun h => hj0 (by rw [← hcoeff, h]; simp)
  have hdeg : q.natDegree ≤ m - 1 + s :=
    natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (natDegree_monomial_le _).trans (by have := j.2; omega)
  refine le_trans (count_mono fun γ hγ => ?_) (count_roots_le hne hdeg)
  rw [hq, eval_finset_sum, ← hγ]
  exact sum_congr rfl fun j _ => by rw [eval_monomial, mul_comm]

/-- If (a, b) ≠ (0, 0), then a + r b = 0 holds for at most one r. In a linear combination with
independent coefficients, b is the last of the combined values that is not 0, r is its coefficient,
and a collects the terms before it. -/
theorem count_affine_le_one (a b : K) (h : a ≠ 0 ∨ b ≠ 0) :
    Nat.card {r : K // a + r * b = 0} ≤ 1 := by
  refine count_le_one fun r r' hr hr' => ?_
  have h1 : (r - r') * b = 0 := by linear_combination hr - hr'
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · subst h2
    simp only [mul_zero, add_zero] at hr
    exact absurd hr (by simpa using h)

end Roots

/-! ## Functions of bounded degree in each variable -/

section DegLE

variable {K : Type*} [CommRing K] {ι : Type*} [DecidableEq ι]

/-- g is, in each single variable v and for all fixed values of the other variables, a polynomial
function of degree at most d v. -/
def DegLE (d : ι → ℕ) (g : (ι → K) → K) : Prop :=
  ∀ (z : ι → K) (i : ι), ∃ q : K[X], q.natDegree ≤ d i ∧ ∀ t, g (Function.update z i t) = q.eval t

theorem DegLE.mono {d d' : ι → ℕ} {g : (ι → K) → K} (h : DegLE d g) (hd : ∀ i, d i ≤ d' i) :
    DegLE d' g := fun z i => by
  obtain ⟨q, hq, he⟩ := h z i
  exact ⟨q, hq.trans (hd i), he⟩

theorem DegLE.const (d : ι → ℕ) (c : K) : DegLE d (fun _ => c) := fun _ _ => ⟨C c, by simp, by simp⟩

/-- A coordinate function has degree at most 1 in each variable. -/
theorem DegLE.coord (j : ι) : DegLE (fun _ => 1) (fun z : ι → K => z j) := fun z i => by
  by_cases h : j = i
  · subst h
    exact ⟨X, natDegree_X_le, by simp⟩
  · exact ⟨C (z j), by simp, fun t => by simp [Function.update_of_ne h]⟩

theorem DegLE.add {d : ι → ℕ} {g h : (ι → K) → K} (hg : DegLE d g) (hh : DegLE d h) :
    DegLE d (fun z => g z + h z) := fun z i => by
  obtain ⟨q, hq, he⟩ := hg z i
  obtain ⟨q', hq', he'⟩ := hh z i
  exact ⟨q + q',
    (natDegree_add_le _ _).trans (max_le hq hq'),
    fun t => by simp only [he, he', eval_add]⟩

theorem DegLE.neg {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) :
    DegLE d (fun z => - g z) := fun z i => by
  obtain ⟨q, hq, he⟩ := hg z i
  exact ⟨-q, by rwa [natDegree_neg], fun t => by simp only [he, eval_neg]⟩

theorem DegLE.sub {d : ι → ℕ} {g h : (ι → K) → K} (hg : DegLE d g) (hh : DegLE d h) :
    DegLE d (fun z => g z - h z) := by
  simpa only [sub_eq_add_neg] using hg.add hh.neg

/-- The degree bounds of a product of two functions add. -/
theorem DegLE.mul {d d' : ι → ℕ} {g h : (ι → K) → K} (hg : DegLE d g) (hh : DegLE d' h) :
    DegLE (fun i => d i + d' i) (fun z => g z * h z) := fun z i => by
  obtain ⟨q, hq, he⟩ := hg z i
  obtain ⟨q', hq', he'⟩ := hh z i
  exact ⟨q * q',
    natDegree_mul_le.trans (Nat.add_le_add hq hq'),
    fun t => by simp only [he, he', eval_mul]⟩

theorem DegLE.const_mul {d : ι → ℕ} {g : (ι → K) → K} (c : K) (hg : DegLE d g) :
    DegLE d (fun z => c * g z) := by
  simpa using (DegLE.const (fun _ => 0) c).mul hg

theorem DegLE.mul_const {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (c : K) :
    DegLE d (fun z => g z * c) := by
  simpa using hg.mul (DegLE.const (fun _ => 0) c)

theorem DegLE.sum {J : Type*} (s : Finset J) {d : ι → ℕ}
    {g : J → (ι → K) → K} (hg : ∀ j ∈ s, DegLE d (g j)) :
    DegLE d (fun z => ∑ j ∈ s, g j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DegLE.const d (0 : K)
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hg a (mem_insert_self _ _)).add (ih fun j hj => hg j (mem_insert_of_mem hj))

/-- The degree bounds of a product add. -/
theorem DegLE.prod {J : Type*} (s : Finset J) {d : J → ι → ℕ}
    {g : J → (ι → K) → K} (hg : ∀ j ∈ s, DegLE (d j) (g j)) :
    DegLE (fun i => ∑ j ∈ s, d j i) (fun z => ∏ j ∈ s, g j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using DegLE.const (fun _ => 0) (1 : K)
  | insert a s ha ih =>
    simp only [prod_insert ha, sum_insert ha]
    exact (hg a (mem_insert_self _ _)).mul (ih fun j hj => hg j (mem_insert_of_mem hj))

/-- Fixing one variable at a value preserves the degree bounds. -/
theorem DegLE.update {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (j : ι) (c : K) :
    DegLE d (fun z => g (Function.update z j c)) := fun z i => by
  by_cases h : i = j
  · subst h
    exact ⟨C (g (Function.update z i c)), by simp, fun t => by simp⟩
  · obtain ⟨q, hq, he⟩ := hg (Function.update z j c) i
    exact ⟨q, hq, fun t => by simp only [← he, Function.update_comm h]⟩

/-- Fixing the variables in a set S at the values that z has there preserves the degree bounds. -/
theorem DegLE.freeze {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (S : Set ι)
    [DecidablePred (· ∈ S)] (z : ι → K) :
    DegLE d (fun w => g fun j => if j ∈ S then z j else w j) := fun w i => by
  by_cases hi : i ∈ S
  · refine ⟨C (g fun j => if j ∈ S then z j else w j), by simp, fun t => ?_⟩
    rw [eval_C]
    refine congrArg g (funext fun j => ?_)
    by_cases hj : j = i
    · subst hj; simp [hi]
    · rw [Function.update_of_ne hj]
  · obtain ⟨q, hq, he⟩ := hg (fun j => if j ∈ S then z j else w j) i
    refine ⟨q, hq, fun t => ?_⟩
    rw [← he]
    refine congrArg g (funext fun j => ?_)
    by_cases hj : j = i
    · subst hj; simp [hi]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- A function of some of the coordinates of a longer tuple. The injection e maps the variables of g
to coordinates of the tuple. The degree bound d' must be at least d at a coordinate that is used and
may be 0 at a coordinate that is not used. -/
theorem DegLE.comp {J : Type*} [DecidableEq J] {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g)
    (e : ι → J) (he : Function.Injective e) (d' : J → ℕ) (hd : ∀ v, d v ≤ d' (e v)) :
    DegLE d' (fun z : J → K => g fun v => z (e v)) := by
  intro z j
  by_cases hj : ∃ v, e v = j
  · obtain ⟨v, rfl⟩ := hj
    obtain ⟨q, hq, hev⟩ := hg (fun v => z (e v)) v
    refine ⟨q, hq.trans (hd v), fun t => ?_⟩
    rw [← hev]
    refine congrArg g (funext fun v' => ?_)
    by_cases hv : v' = v
    · subst hv; simp
    · rw [Function.update_of_ne hv, Function.update_of_ne fun h => hv (he h)]
  · refine ⟨C (g fun v => z (e v)), by simp, fun t => ?_⟩
    rw [eval_C]
    refine congrArg g (funext fun v => ?_)
    rw [Function.update_of_ne fun h => hj ⟨v, h⟩]

/-- Under `hg`, a function of degree at most 1 in the variable i (`hi`) interpolates linearly
between its values at 0 and at 1. -/
theorem DegLE.update_of_le_one
    {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (i : ι) (hi : d i ≤ 1) (z : ι → K) (t : K) :
    g (Function.update z i t) =
      (1 - t) * g (Function.update z i 0) + t * g (Function.update z i 1) := by
  obtain ⟨q, hq, he⟩ := hg z i
  rw [he, he, he, eq_X_add_C_of_natDegree_le_one (hq.trans hi)]
  simp
  ring

/-- One coordinate of a random point. If g has degree at most d v in each variable v (`hg`) and
g w ≠ 0, then at most d i values r make g vanish at the point w with coordinate i replaced by r. -/
theorem DegLE.count_update_le [IsDomain K] [Finite K] {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g)
    (w : ι → K) (hw : g w ≠ 0) (i : ι) :
    Nat.card {r : K // g (Function.update w i r) = 0} ≤ d i := by
  obtain ⟨q, hq, he⟩ := hg w i
  have hne : q ≠ 0 := by
    rintro rfl
    apply hw
    have := he (w i)
    rwa [Function.update_eq_self, eval_zero] at this
  exact le_trans (count_mono fun r hr => by rw [← he, hr]) (count_roots_le hne hq)

end DegLE

/-! ## Linear combinations with independent coefficients, the coefficients taken as one tuple -/

section Forms

variable {J : Type*} [Fintype J] [DecidableEq J] {K : Type*} [CommRing K] [IsDomain K] [Fintype K]

/-- Independent coefficients. If a0 and the a_j are not all 0, then a0 + ∑_j ρ_j a_j = 0 for at most
the fraction 1 / |K| of the tuples ρ, for any number of coefficients. In any fixed order of J let i
be the last index with a_i ≠ 0: the terms after it vanish, so the equation is c + ρ_i a_i = 0, that
of `count_affine_le_one`, with c the sum of a0 and the terms before i; if all a_j are 0 the equation
fails. -/
theorem count_affine_form_le (a0 : K) (a : J → K) (h : a0 ≠ 0 ∨ a ≠ 0) :
    Nat.card {ρ : J → K // a0 + ∑ j, ρ j * a j = 0} * Fintype.card K ≤ Fintype.card (J → K) := by
  by_cases ha : a = 0
  · subst ha
    have h0 : a0 ≠ 0 := by simpa using h
    rw [count_eq_zero fun ρ => by simpa using h0]
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
    have := count_pi_mul_le_of_fiber i (fun ρ : J → K => a0 + ∑ j, ρ j * a j = 0) 1 fun f => by
      have hs : ∀ t : K, a0 + ∑ j, Function.update f i t j * a j =
          (a0 + ∑ j ∈ univ.erase i, f j * a j) + t * a i := by
        intro t
        rw [← add_sum_erase univ _ (mem_univ i), Function.update_self]
        have : ∑ j ∈ univ.erase i, Function.update f i t j * a j = ∑ j ∈ univ.erase i, f j * a j :=
          sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
        rw [this]
        ring
      simp only [hs]
      exact count_affine_le_one _ _ (Or.inr hi)
    simpa using this

/-- `count_affine_form_le` for a linear form: ∑_j ρ_j a_j = 0 with a ≠ 0. -/
theorem count_linear_form_le (a : J → K) (h : a ≠ 0) :
    Nat.card {ρ : J → K // ∑ j, ρ j * a j = 0} * Fintype.card K ≤ Fintype.card (J → K) := by
  simpa using count_affine_form_le 0 a (Or.inr h)

/-- The bound of `count_affine_form_le` as a number of tuples: at most |K|^(|J| - 1). Under `h`, for
an empty family the true number is 0 and this bound is 1. -/
theorem count_affine_form_le_pow (a0 : K) (a : J → K) (h : a0 ≠ 0 ∨ a ≠ 0) :
    Nat.card {ρ : J → K // a0 + ∑ j, ρ j * a j = 0} ≤ Fintype.card K ^ (Fintype.card J - 1) := by
  have h1 := count_affine_form_le a0 a h
  rw [Fintype.card_fun, ← one_mul (Fintype.card K ^ Fintype.card J)] at h1
  simpa using le_mul_pow_pred Fintype.card_pos h1

/-- A bilinear identity. Let P(χ, χ') = P0 + ∑_i χ'_i Λ_i(χ) with linear forms
Λ_i(χ) = ∑_j χ_j L i j. If P0 and the L i j are not all 0, then P vanishes for at most the fraction
2 / |K| of the pairs. -/
theorem count_bilinear_mul_le
    {I : Type*} [Fintype I] [DecidableEq I] (P0 : K) (L : I → J → K) (h : P0 ≠ 0 ∨ L ≠ 0) :
    Nat.card {p : (J → K) × (I → K) // P0 + ∑ i, p.2 i * ∑ j, p.1 j * L i j = 0} * Fintype.card K ≤
      2 * Fintype.card ((J → K) × (I → K)) := by
  by_cases hL : L = 0
  · subst hL
    have h0 : P0 ≠ 0 := by simpa using h
    rw [count_eq_zero fun p => by simpa using h0]
    simp
  · obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hL
    refine count_prod_mul_le _ (fun χ : J → K => ∑ j, χ j * L i0 j = 0) (Fintype.card K) 1 1
      (by simpa using count_linear_form_le (L i0) hi0) (fun χ hχ => ?_)
    have :=
      count_affine_form_le P0 (fun i => ∑ j, χ j * L i j) (Or.inr fun h0 => hχ (congrFun h0 i0))
    simpa using this

end Forms

/-! ## The Schwartz-Zippel lemma for a whole tuple -/

section Tuple

variable {K : Type*} [CommRing K] [IsDomain K] [Fintype K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Schwartz-Zippel lemma for a tuple. If g has degree at most d i in each variable i and is not
the zero function, then g z = 0 for at most the fraction (∑ i, d i) / |K| of the tuples z. -/
theorem DegLE.count_zero_mul_le {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (hw : ∃ w, g w ≠ 0) :
    Nat.card {z : ι → K // g z = 0} * Fintype.card K ≤ (∑ i, d i) * Fintype.card (ι → K) := by
  obtain ⟨w, hw⟩ := hw
  -- the point that is z on the coordinates in S and w elsewhere
  let hyb : Finset ι → (ι → K) → ι → K := fun S z j => if j ∈ S then z j else w j
  have key : ∀ S : Finset ι, Nat.card {z : ι → K // g (hyb S z) = 0} * Fintype.card K ≤
      (∑ i ∈ S, d i) * Fintype.card (ι → K) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : ∀ z : ι → K, ¬ g (hyb ∅ z) = 0 := fun z => by
        have : hyb ∅ z = w := by funext j; simp [hyb]
        rwa [this]
      rw [count_eq_zero this]
      simp
    | insert a S ha ih =>
      have h1 : Nat.card {z : ι → K // g (hyb (insert a S) z) = 0}
          ≤ Nat.card {z : ι → K // g (hyb S z) = 0}
            + Nat.card {z : ι → K // g (hyb S z) ≠ 0 ∧ g (hyb (insert a S) z) = 0} := by
        refine le_trans (count_mono fun z hz => ?_) (count_or_le _ _)
        by_cases h0 : g (hyb S z) = 0
        · exact Or.inl h0
        · exact Or.inr ⟨h0, hz⟩
      have h2 : Nat.card {z : ι → K // g (hyb S z) ≠ 0 ∧ g (hyb (insert a S) z) = 0} *
            Fintype.card K ≤
          d a * Fintype.card (ι → K) := by
        apply count_pi_mul_le_of_fiber a
        intro f
        have e1 : ∀ t, hyb S (Function.update f a t) = hyb S f := fun t => by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hyb, ha]
          · simp [hyb, Function.update_of_ne hj]
        have e2 : ∀ t,
            hyb (insert a S) (Function.update f a t) = Function.update (hyb S f) a t := fun t => by
          funext j
          by_cases hj : j = a
          · subst hj; simp [hyb]
          · simp [hyb, hj]
        simp only [e1, e2]
        by_cases h0 : g (hyb S f) = 0
        · rw [count_eq_zero fun t ht => ht.1 h0]
          exact Nat.zero_le _
        · exact le_trans (count_mono fun t ht => ht.2) (hg.count_update_le _ h0 a)
      rw [sum_insert ha]
      calc
        Nat.card {z : ι → K // g (hyb (insert a S) z) = 0} * Fintype.card K ≤
            (Nat.card {z : ι → K // g (hyb S z) = 0} +
                Nat.card {z : ι → K // g (hyb S z) ≠ 0 ∧ g (hyb (insert a S) z) = 0}) *
              Fintype.card K :=
            Nat.mul_le_mul_right _ h1
        _ ≤ (d a + ∑ i ∈ S, d i) * Fintype.card (ι → K) := by
            rw [add_mul, add_mul]
            omega
  have hu : ∀ z : ι → K, hyb univ z = z := fun z => by funext j; simp [hyb]
  simpa [hu] using key univ

/-- The Schwartz-Zippel lemma as a number of points. If g has degree at most d i in variable i and
is not the zero function, it vanishes at no more than (∑ i, d i) |K|^(n - 1) points, where n is the
number of variables. -/
theorem DegLE.count_zero_le {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g) (hw : ∃ w, g w ≠ 0) :
    Nat.card {z : ι → K // g z = 0} ≤ (∑ i, d i) * Fintype.card K ^ (Fintype.card ι - 1) := by
  have h := hg.count_zero_mul_le hw
  rw [Fintype.card_fun] at h
  exact le_mul_pow_pred Fintype.card_pos h

/-- Two functions of degree at most d i in variable i that differ somewhere agree at no more than
(∑ i, d i) |K|^(n - 1) points, where n is the number of variables. -/
theorem DegLE.count_eq_le {d : ι → ℕ} {g h : (ι → K) → K} (hg : DegLE d g)
    (hh : DegLE d h) (hne : g ≠ h) :
    Nat.card {z : ι → K // g z = h z} ≤ (∑ i, d i) * Fintype.card K ^ (Fintype.card ι - 1) := by
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hne
  refine le_trans (count_mono fun z hz => ?_) ((hg.sub hh).count_zero_le ⟨w, sub_ne_zero.mpr hw⟩)
  exact sub_eq_zero.mpr hz

end Tuple

end Alg
