-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Circle/GRS.lean: circle codes and Reed–Solomon codes; distance and hidden positions.

K is any field in which 2 ≠ 0, and the points are any that satisfy `CirclePoints`
(Code/Circle/Basis.lean). So all statements hold over a field and its extensions.

 * Part 1: the generator `gen z k` (dimension k, points z).
 * Part 2: for odd k = 2N + 1 there is a linear bijection `toRS` of K^k, independent of the points,
   with (gen z k a)_I = η_I · P(θ_I), where P has the coefficients toRS a, θ_I = y_I / (1 + x_I) and
   η_I = (1 + θ_I²)^(-N) (`gen_eq_scaled_rs`). The θ_I are distinct and the η_I are not 0.
 * Part 3, for 2⌊k/2⌋ < n: a non-zero word has at least n - 2⌊k/2⌋ symbols that are not 0, that is
   n - k + 1 for odd and n - k for even k (`le_weight`); the generator is injective
   (`gen_injective`); for odd k the bound is attained (`exists_weight_eq_odd`).
 * Part 4 (`ontoUpTo_genShift`): assume (Alignment): a power of two 2^s ≥ r divides i0; and let
   bas_(i0) have no zero at the points; then the r coordinates from index i0 on are onto on every
   set of at most `hidden r` positions: r for odd, r - 1 for even r.

Notation: `wordPoly B k a` (Code/Circle/Poly.lean; B, k natural numbers, a a vector of k elements of
the field): a polynomial over the field, the polynomial of a codeword: `(1 + t^2)^(k/2)` times the
linear combination of the basis functions (`basis B j`) with the coefficients `a`, as a polynomial
in t, for `k ≤ 2^(B+1)`, at every t with `1 + t^2 ≠ 0`.

Not shown here: that the numbers n - k and r - 1 are optimal for even k and even r.
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Code.Circle.Basis
import Code.QueryUniform
import Code.RS
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Code.Circle

open Polynomial Function

variable {K : Type*} [Field K] {P : Type*}

/-! ## Part 1. The generator -/

/-- The generator of the circle code of dimension k at the points z: the coefficients a go to the
values of ∑_(i < k) a_i bas_i at the points. -/
def gen (z : P → Circ K) (k : ℕ) : (Fin k → K) →ₗ[K] (P → K) where
  toFun a := fun I => ∑ i : Fin k, a i * bas i (z I)
  map_add' a a' := by
    funext I
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext I
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem gen_apply (z : P → Circ K) (k : ℕ) (a : Fin k → K) (I : P) :
    gen z k a I = ∑ i : Fin k, a i * bas i (z I) := rfl

/-- The code of dimension k is the subcode a_k = 0 of the code of dimension k + 1. -/
theorem gen_snoc (z : P → Circ K) (k : ℕ) (a : Fin k → K) (I : P) :
    gen z (k + 1) (Fin.snoc (α := fun _ => K) a 0) I = gen z k a I := by
  rw [gen_apply, gen_apply, Fin.sum_univ_castSucc]
  simp

/-! ## Part 2. Odd dimension: the generalised Reed–Solomon form -/

/-- The column multipliers η_I = (1 + θ_I²)^(-N). -/
def eta (N : ℕ) (z : P → Circ K) : P → K := fun I => ((1 + theta (z I) ^ 2) ^ N)⁻¹

theorem eta_ne_zero (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) (N : ℕ) (I : P) :
    eta N z I ≠ 0 :=
  inv_ne_zero (pow_ne_zero _ (den_ne h2 _ (hz.ne I)))

/-- Under `h2`, `hz`, `hB`: symbol I of a codeword is η_I = `eta (k / 2) z I` times the value at θ_I
of the polynomial of the codeword. -/
theorem gen_eq_eval (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) {B k : ℕ}
    (hB : k ≤ 2 ^ (B + 1)) (a : Fin k → K) (I : P) :
    gen z k a I = eta (k / 2) z I * (wordPoly B k a).eval (theta (z I)) := by
  rw [wordPoly_eval_any B k hB a _ (den_ne h2 _ (hz.ne I)), eta,
    inv_mul_cancel_left₀ (pow_ne_zero _ (den_ne h2 _ (hz.ne I))), gen_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [bas_eq_basis h2 (lt_of_lt_of_le i.2 hB) (z I) (hz.ne I)]

theorem le_two_pow_aux (N : ℕ) : 2 * N + 2 ≤ 2 ^ (2 * N + 1 + 1) := Nat.lt_two_pow_self.le

/-- The coefficients of the polynomial of a codeword of odd dimension 2N + 1, as a linear map of
the coefficients of the word. -/
def coeffMap (K : Type*) [Field K] (N : ℕ) :
    (Fin (2 * N + 1) → K) →ₗ[K] (Fin (2 * N + 1) → K) where
  toFun a := fun i => (wordPoly (2 * N + 1) (2 * N + 1) a).coeff i
  map_add' a a' := by
    funext i
    simp only [wordPoly, Pi.add_apply, C_add, add_mul, Finset.sum_add_distrib, coeff_add]
  map_smul' c a := by
    funext i
    simp only [wordPoly, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, C_mul, mul_assoc,
      ← Finset.mul_sum, coeff_C_mul]

theorem degree_wordPoly_lt (N : ℕ) (a : Fin (2 * N + 1) → K) :
    (wordPoly (2 * N + 1) (2 * N + 1) a).degree < ((2 * N + 1 : ℕ) : WithBot ℕ) := by
  have h :=
    wordPoly_natDegree_le_two_mul (2 * N + 1) (2 * N + 1) (by have := le_two_pow_aux N; omega) a
  refine lt_of_le_of_lt degree_le_natDegree ?_
  exact_mod_cast (by omega : (wordPoly (2 * N + 1) (2 * N + 1) a).natDegree < 2 * N + 1)

/-- If 2 ≠ 0, the polynomial of a codeword determines its coefficients. -/
theorem coeffMap_injective (h2 : (2 : K) ≠ 0) (N : ℕ) : Injective (coeffMap K N) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  refine wordPoly_eq_zero_odd h2 (2 * N + 1) N (le_two_pow_aux N) a ?_
  ext m
  rw [coeff_zero]
  by_cases hm : m < 2 * N + 1
  · exact congrFun ha ⟨m, hm⟩
  · exact coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le (degree_wordPoly_lt N a) (by exact_mod_cast not_lt.1 hm))

/-- The bijection: from the coefficients of a word of the circle code of dimension 2N + 1 to the
coefficients of a polynomial of degree at most 2N. It does not depend on the points. -/
def toRS (h2 : (2 : K) ≠ 0) (N : ℕ) :
    (Fin (2 * N + 1) → K) ≃ₗ[K] (Fin (2 * N + 1) → K) :=
  LinearEquiv.ofInjectiveEndo (coeffMap K N) (coeffMap_injective h2 N)

/-- Under `h2`, `hz`, a circle code of odd dimension k = 2N + 1 is a generalised
Reed–Solomon code: symbol I of the word with the coefficients a is η_I P(θ_I), where P has the
coefficients toRS a; and a ↦ toRS a is a linear bijection of K^k. -/
theorem gen_eq_scaled_rs (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) (N : ℕ)
    (a : Fin (2 * N + 1) → K) (I : P) :
    gen z (2 * N + 1) a I =
      eta N z I *
        RS.gen (fun I => theta (z I)) (fun i : Fin (2 * N + 1) => (i : ℕ)) (toRS h2 N a) I := by
  have h1 : toRS h2 N a = fun i : Fin (2 * N + 1) => (wordPoly (2 * N + 1) (2 * N + 1) a).coeff i :=
    rfl
  have h3 : (2 * N + 1) / 2 = N := by omega
  rw [h1, RS.gen_coeff (degree_wordPoly_lt N a),
    gen_eq_eval h2 hz (B := 2 * N + 1) (by have := le_two_pow_aux N; omega) a I, h3]

/-! ## Part 3. Distance and rank -/

section Distance

variable [Finite P]

/-- Odd dimension k ≤ n (`h2`, `hz`): a non-zero word has at least n - k + 1 symbols
that are not 0. -/
theorem le_weight_odd (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) {N : ℕ}
    (hn : 2 * N + 1 ≤ Nat.card P) {a : Fin (2 * N + 1) → K} (ha : a ≠ 0) :
    Nat.card P - (2 * N + 1) + 1 ≤ Nat.card {I : P // gen z (2 * N + 1) a I ≠ 0} := by
  have h1 : toRS h2 N a ≠ 0 := fun h => ha ((toRS h2 N).map_eq_zero_iff.1 h)
  refine (RS.le_weight (hz.theta_injective h2) Fin.val_injective (fun i => i.2) hn h1).trans
    (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun I => ?_)))
  rw [gen_eq_scaled_rs h2 hz, mul_ne_zero_iff, and_iff_right (eta_ne_zero h2 hz N I)]

/-- Odd dimension k ≤ n (`h2`, `hz`): some word has exactly n - k + 1 symbols that are
not 0. So n - k + 1 is the minimum distance. -/
theorem exists_weight_eq_odd (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) {N : ℕ}
    (hn : 2 * N + 1 ≤ Nat.card P) : ∃ a : Fin (2 * N + 1) → K, a ≠ 0 ∧
      Nat.card {I : P // gen z (2 * N + 1) a I ≠ 0} = Nat.card P - (2 * N + 1) + 1 := by
  obtain ⟨v, hv, hw⟩ := RS.exists_weight_eq (hz.theta_injective h2) (k := 2 * N + 1) (by omega) hn
  refine ⟨(toRS h2 N).symm v, fun h => hv ?_, ?_⟩
  · rw [← (toRS h2 N).apply_symm_apply v, h, map_zero]
  · rw [← hw]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun I => ?_)
    rw [gen_eq_scaled_rs h2 hz, LinearEquiv.apply_symm_apply,
      mul_ne_zero_iff, and_iff_right (eta_ne_zero h2 hz N I)]

/-- The bound, under `h2`, `hz` and 2⌊k/2⌋ < n. A non-zero word of the circle code of
dimension k has at least n - 2⌊k/2⌋ symbols that are not 0:
n - k + 1 for odd k, and n - k for even k. -/
theorem le_weight (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) {k : ℕ}
    (hn : 2 * (k / 2) < Nat.card P) {a : Fin k → K} (ha : a ≠ 0) :
    Nat.card P - 2 * (k / 2) ≤ Nat.card {I : P // gen z k a I ≠ 0} := by
  obtain ⟨N, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h3 : 2 * N / 2 = N := by omega
    rw [h3] at hn ⊢
    have h1 : (Fin.snoc (α := fun _ => K) a 0 : Fin (2 * N + 1) → K) ≠ 0 := by
      intro h
      refine ha (funext fun i => ?_)
      have h4 := congrFun h i.castSucc
      rwa [Fin.snoc_castSucc] at h4
    have h5 := le_weight_odd h2 hz (N := N) hn h1
    simp only [gen_snoc] at h5
    omega
  · have h3 : (2 * N + 1) / 2 = N := by omega
    rw [h3] at hn ⊢
    have h5 := le_weight_odd h2 hz (N := N) hn ha
    omega

/-- The rank. Under `h2`, `hz`, `hn`: the generator is injective. -/
theorem gen_injective (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z)
    {k : ℕ} (hn : 2 * (k / 2) < Nat.card P) : Injective (gen z k) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  have h1 := le_weight h2 hz hn hne
  haveI : IsEmpty {I : P // gen z k a I ≠ 0} := ⟨fun I => I.2 (congrFun ha I)⟩
  have h3 : Nat.card {I : P // gen z k a I ≠ 0} = 0 := Nat.card_of_isEmpty
  omega

end Distance

/-! ## Part 4. Hidden positions -/

/-- The number of positions that r uniform coordinates are shown to hide: r if r is odd, r - 1 if r
is even. (not all hypotheses are named here: see `ontoUpTo_genShift`) -/
def hidden (r : ℕ) : ℕ := if r % 2 = 1 then r else r - 1

theorem hidden_le (r : ℕ) : hidden r ≤ r := by
  unfold hidden
  split_ifs <;> omega

/-- Odd r (`h2`, `hz`): any r symbols of the word of r uniform coefficients take all patterns. -/
theorem ontoUpTo_gen_odd (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) (N : ℕ) :
    OntoUpTo (gen z (2 * N + 1)) (2 * N + 1) :=
  (RS.ontoUpTo_gen (hz.theta_injective h2) (2 * N + 1)).of_scaled (gen z (2 * N + 1)) (toRS h2 N)
    (toRS h2 N).surjective (eta N z) (eta_ne_zero h2 hz N) (gen_eq_scaled_rs h2 hz N)

/-- Under `h2`, `hz`: any `hidden r` symbols of the word of r uniform coefficients take all
patterns. This is the case i0 = 0, the case of a mask. -/
theorem ontoUpTo_gen (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) (r : ℕ) :
    OntoUpTo (gen z r) (hidden r) := by
  obtain ⟨N, rfl | rfl⟩ := Nat.even_or_odd' r
  · have h3 : hidden (2 * N) = 2 * N - 1 := by
      unfold hidden
      rw [if_neg (by omega)]
    rw [h3]
    rcases N with _ | N
    · exact ontoUpTo_zero _
    · exact (ontoUpTo_gen_odd h2 hz N).of_emb
        (gen z (2 * N + 1 + 1)) (fun a => Fin.snoc (α := fun _ => K) a 0) (gen_snoc z (2 * N + 1))
  · have h3 : hidden (2 * N + 1) = 2 * N + 1 := by
      unfold hidden
      rw [if_pos (by omega)]
    rw [h3]
    exact ontoUpTo_gen_odd h2 hz N

/-- The contribution of r coefficients at the indices i0, ..., i0 + r - 1 to a codeword. -/
def genShift (z : P → Circ K) (i0 r : ℕ) : (Fin r → K) →ₗ[K] (P → K) where
  toFun ρ := fun I => ∑ t : Fin r, ρ t * bas (i0 + t) (z I)
  map_add' a a' := by
    funext I
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext I
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem genShift_apply (z : P → Circ K) (i0 r : ℕ) (ρ : Fin r → K) (I : P) :
    genShift z i0 r ρ I = ∑ t : Fin r, ρ t * bas (i0 + t) (z I) := rfl

/-- Under (Alignment), row I of the columns i0, ..., i0 + r - 1 of the generator matrix is
bas_(i0)(z_I) times row I of the first r columns. -/
theorem genShift_eq {s i0 r : ℕ} (hd : 2 ^ s ∣ i0) (hr : r ≤ 2 ^ s) (z : P → Circ K)
    (ρ : Fin r → K) (I : P) :
    genShift z i0 r ρ I = bas i0 (z I) * gen z r ρ I := by
  rw [genShift_apply, gen_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [bas_add hd (lt_of_lt_of_le t.2 hr)]
  ring

/-- Hidden positions, the linear algebra, under `h2`, `hz`. Assume (Alignment): a
power of two 2^s ≥ r divides i0; and let bas_(i0) have no zero at the points. Then the contribution
of the r coefficients at the indices i0, ..., i0 + r - 1 takes all patterns on every set of at most
`hidden r` positions. -/
theorem ontoUpTo_genShift (h2 : (2 : K) ≠ 0) {z : P → Circ K} (hz : CirclePoints z) {s i0 r : ℕ}
    (hd : 2 ^ s ∣ i0) (hr : r ≤ 2 ^ s) (h0 : ∀ I, bas i0 (z I) ≠ 0) :
    OntoUpTo (genShift z i0 r) (hidden r) :=
  (ontoUpTo_gen h2 hz r).of_scaled
    (genShift z i0 r) id surjective_id (fun I => bas i0 (z I)) h0 (genShift_eq hd hr z)

end Code.Circle
