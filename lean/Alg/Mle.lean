-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Alg/Mle.lean: the equality polynomial eq, multilinear extensions, and the Schwartz-Zippel lemma for
multilinear extensions as a count.

  `eqPt`, `eqk`   eq(x, y) at two points; `eqk`: eq(z, b) at a point z and a vertex b of the cube
  `mle`   the multilinear extension ~u(z) = ∑_b eq(z, b) u[b]
  `bits`, `num`, `cubeEquiv`, `eqN`, `mleN`   an index read as a number, with the first coordinate
      as its highest bit
  `eqN_append`   eq((a, a'), 2^v' i + i') = eq(a, i) eq(a', i') for i' < 2^v'
  `count_eqN_zero_le`   the multilinear identity; on the cube it is `count_mle_zero_le`, for two
      extensions `count_mle_eq_le`

A vector of length 2^n is indexed by the cube ι → Bool, where ι is the finite set of its variables
(Fin n, or a sum ι₁ ⊕ ι₂ for an index that is a pair). K is any commutative ring; the counts need a
finite domain.

Notation: `DegLE d g` (Alg/Poly.lean): g is, in each single variable v and for all fixed values of
the other variables, a polynomial function of degree at most d v.
-/
import Alg.Poly
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Batteries.Data.Nat.Lemmas

set_option autoImplicit false

namespace Alg

open Finset Polynomial

/-! ## Definitions -/

section Defs

variable {K : Type*} [CommRing K] {ι : Type*}

/-- A vertex of the cube as a point of K^ι. -/
def corner (b : ι → Bool) : ι → K := fun v => if b v then 1 else 0

variable [Fintype ι]

/-- eq(z, b) = ∏_v (z_v if b_v = 1, else 1 - z_v), for a point z and a vertex b of the cube. As a
vector in b this is the tensor product of the vectors (1 - z_v, z_v). -/
def eqk (z : ι → K) (b : ι → Bool) : K := ∏ v, if b v then z v else 1 - z v

/-- The multilinear extension ~u(z) = ∑_b eq(z, b) u[b]. -/
def mle [DecidableEq ι] (u : (ι → Bool) → K) (z : ι → K) : K := ∑ b, eqk z b * u b

/-- eq1(a, b) = a b + (1 - a)(1 - b). -/
def eq1 (a b : K) : K := a * b + (1 - a) * (1 - b)

/-- eq(x, y) = ∏_v (x_v y_v + (1 - x_v)(1 - y_v)) for two points. -/
def eqPt (x y : ι → K) : K := ∏ v, eq1 (x v) (y v)

end Defs

/-! ## On the cube -/

section Cube

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- eq at two vertices is 1 if they are equal and 0 otherwise. -/
theorem eqk_corner [DecidableEq (ι → Bool)] (b b' : ι → Bool) :
    eqk (corner b : ι → K) b' = if b = b' then 1 else 0 := by
  unfold eqk corner
  split_ifs with h
  · subst h
    exact prod_eq_one fun v _ => by cases b v <;> simp
  · obtain ⟨v, hv⟩ := Function.ne_iff.mp h
    refine prod_eq_zero (mem_univ v) ?_
    revert hv
    cases b v <;> cases b' v <;> simp

/-- The extension agrees with its vector on the cube. -/
theorem mle_corner (u : (ι → Bool) → K) (b : ι → Bool) : mle u (corner b) = u b := by
  classical
  unfold mle
  simp_rw [eqk_corner]
  simp

/-- The weights eq(z, ·) sum to 1. -/
theorem sum_eqk (z : ι → K) : ∑ b, eqk z b = 1 := by
  classical
  unfold eqk
  rw [← Fintype.prod_sum (fun v (β : Bool) => if β then z v else 1 - z v)]
  exact prod_eq_one fun v _ => by simp

omit [DecidableEq ι] in
/-- If the second point is a vertex of the cube, `eqPt` equals `eqk`. -/
theorem eqPt_corner (x : ι → K) (b : ι → Bool) : eqPt x (corner b) = eqk x b := by
  unfold eqPt eqk corner eq1
  exact prod_congr rfl fun v _ => by cases b v <;> simp

omit [DecidableEq ι] in
theorem eqPt_comm (x y : ι → K) : eqPt x y = eqPt y x := by
  unfold eqPt eq1
  exact prod_congr rfl fun v _ => by ring

/-- The multilinear extension of eq(x, ·) is eq at two points. -/
theorem mle_eqk (x y : ι → K) : mle (eqk x) y = eqPt x y := by
  classical
  unfold mle eqk eqPt eq1
  simp_rw [← prod_mul_distrib]
  rw [← Fintype.prod_sum
      (fun v (β : Bool) => (if β then y v else 1 - y v) * (if β then x v else 1 - x v))]
  refine prod_congr rfl fun v _ => ?_
  simp
  ring

/-! ## Linearity in the vector -/

theorem mle_add (u w : (ι → Bool) → K) (z : ι → K) : mle (u + w) z = mle u z + mle w z := by
  simp [mle, mul_add, sum_add_distrib]

theorem mle_sub (u w : (ι → Bool) → K) (z : ι → K) : mle (u - w) z = mle u z - mle w z := by
  simp [mle, mul_sub, sum_sub_distrib]

theorem mle_smul (s : K) (u : (ι → Bool) → K) (z : ι → K) :
    mle (fun b => s * u b) z = s * mle u z := by
  simp only [mle, mul_sum]
  exact sum_congr rfl fun b _ => by ring

theorem mle_sum {J : Type*} (t : Finset J) (u : J → (ι → Bool) → K) (z : ι → K) :
    mle (fun b => ∑ j ∈ t, u j b) z = ∑ j ∈ t, mle (u j) z := by
  simp only [mle, mul_sum]
  exact sum_comm

theorem mle_zero (z : ι → K) : mle (0 : (ι → Bool) → K) z = 0 := by simp [mle]

theorem mle_const (s : K) (z : ι → K) : mle (fun _ => s) z = s := by
  simp only [mle, ← sum_mul, sum_eqk, one_mul]

/-- A vector is non-zero exactly if its multilinear extension is not the zero function. -/
theorem exists_mle_ne_zero (u : (ι → Bool) → K) : u ≠ 0 ↔ ∃ w, mle u w ≠ 0 := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Function.ne_iff.mp h
    exact ⟨corner b, by rwa [mle_corner]⟩
  · rintro ⟨w, hw⟩ rfl
    exact hw (mle_zero w)

end Cube

/-! ## One coordinate -/

section Coordinate

variable {K : Type*} [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- eq(z, b) with coordinate i of z replaced by t is the factor of coordinate i times the factors of
the other coordinates. -/
theorem eqk_update (z : ι → K) (i : ι) (t : K) (b : ι → Bool) :
    eqk (Function.update z i t) b =
      (if b i then t else 1 - t) * ∏ v ∈ univ.erase i, if b v then z v else 1 - z v := by
  unfold eqk
  rw [← mul_prod_erase univ _ (mem_univ i), Function.update_self]
  congr 1
  exact prod_congr rfl fun v hv => by rw [Function.update_of_ne (ne_of_mem_erase hv)]

/-- The extension is affine in each coordinate: it interpolates linearly between its values at 0 and
at 1. -/
theorem mle_update (u : (ι → Bool) → K) (z : ι → K) (i : ι) (t : K) :
    mle u (Function.update z i t) =
      (1 - t) * mle u (Function.update z i 0) + t * mle u (Function.update z i 1) := by
  simp only [mle, eqk_update, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  cases b i <;> simp <;> ring

/-- A multilinear extension has degree at most 1 in each variable. -/
theorem DegLE.mle (u : (ι → Bool) → K) : DegLE (fun _ => 1) (mle u) := fun z i => by
  refine ⟨C (Alg.mle u (Function.update z i 0)) * (1 - X) +
      C (Alg.mle u (Function.update z i 1)) * X,
    ?_, fun t => ?_⟩
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans ?_)
      simp [natDegree_X_le]
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · rw [mle_update]
    simp
    ring

/-- eq(x, y) has degree at most 1 in each coordinate of y. -/
theorem DegLE.eqPt (x : ι → K) : DegLE (fun _ => 1) (fun y : ι → K => Alg.eqPt x y) := by
  simp only [← mle_eqk]
  exact DegLE.mle _

/-- eq(z, b) has degree at most 1 in each coordinate of z. -/
theorem DegLE.eqk (b : ι → Bool) : DegLE (fun _ => 1) (fun z : ι → K => Alg.eqk z b) := by
  simp only [← eqPt_corner, eqPt_comm _ (corner b)]
  exact DegLE.eqPt _

/-- The multilinear extension is unique. A function of degree at most 1 in each variable is the
multilinear extension of its values on the cube. -/
theorem DegLE.eq_mle {d : ι → ℕ} {g : (ι → K) → K} (hg : DegLE d g)
    (hd : ∀ i, d i ≤ 1) (z : ι → K) :
    g z = Alg.mle (fun b => g (corner b)) z := by
  classical
  have key : ∀ (S : Finset ι) (z : ι → K),
      (∀ j, j ∉ S → z j = 0 ∨ z j = 1) → g z = Alg.mle (fun b => g (corner b)) z := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro z hz
      have : z = corner fun j => decide (z j = 1) := by
        funext j
        rcases hz j (notMem_empty j) with h | h
        · by_cases h1 : z j = 1
          · simp [corner, h1]
          · simp [corner, h]
        · simp [corner, h]
      rw [this, mle_corner]
    | insert a S _ ih =>
      intro z hz
      have hb : ∀ c : K, (c = 0 ∨ c = 1) →
          ∀ j, j ∉ S → Function.update z a c j = 0 ∨ Function.update z a c j = 1 := by
        intro c hc j hj
        by_cases hja : j = a
        · subst hja; simpa using hc
        · rw [Function.update_of_ne hja]
          exact hz j (by simp [hja, hj])
      rw [← Function.update_eq_self a z, hg.update_of_le_one a (hd a), mle_update,
        ih _ (hb 0 (Or.inl rfl)), ih _ (hb 1 (Or.inr rfl))]
  exact key univ z fun j hj => absurd (mem_univ j) hj

end Coordinate

/-! ## A point and an index that are pairs -/

section Pairs

variable {K : Type*} [CommRing K] {ι ι' : Type*} [Fintype ι] [Fintype ι']
  [DecidableEq ι] [DecidableEq ι']

omit [DecidableEq ι] [DecidableEq ι'] in
/-- eq((x | y), (a | b)) = eq(x, a) eq(y, b): the vector eq((x | y), ·) is the tensor product of
eq(x, ·) and eq(y, ·). -/
theorem eqk_sumElim (x : ι → K) (y : ι' → K) (b : ι ⊕ ι' → Bool) :
    eqk (Sum.elim x y) b = eqk x (fun v => b (Sum.inl v)) * eqk y (fun v => b (Sum.inr v)) := by
  simp [eqk, Fintype.prod_sum_type]

omit [DecidableEq ι] [DecidableEq ι'] in
/-- eq is invariant under a renaming of the variables. -/
theorem eqk_equiv (e : ι ≃ ι') (z : ι' → K) (b : ι' → Bool) :
    eqk (fun v => z (e v)) (fun v => b (e v)) = eqk z b := by
  unfold eqk
  exact e.prod_comp fun v => if b v then z v else 1 - z v

theorem mle_equiv (e : ι ≃ ι') (u : (ι' → Bool) → K) (z : ι' → K) :
    mle (fun b : ι → Bool => u fun v => b (e.symm v)) (fun v => z (e v)) = mle u z := by
  unfold mle
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl Bool)) _ _ fun b => ?_
  have h := eqk_equiv e z (fun v => b (e.symm v))
  simp only [Equiv.symm_apply_apply] at h
  rw [h]
  rfl

/-- Evaluation in two steps. The extension at (x | y) is obtained by extending in the second group
of variables at y, for each value of the first group, and then in the first group at x. -/
theorem mle_sumElim (u : (ι ⊕ ι' → Bool) → K) (x : ι → K) (y : ι' → K) :
    mle u (Sum.elim x y) = mle (fun a => mle (fun b => u (Sum.elim a b)) y) x := by
  unfold mle
  simp_rw [mul_sum]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow ι ι' Bool) _ _ fun b => ?_
  rw [eqk_sumElim]
  have hb : Sum.elim (fun v => b (Sum.inl v)) (fun v => b (Sum.inr v)) = b := by
    funext s; cases s <;> rfl
  show _ = eqk x (fun v => b (Sum.inl v)) * (eqk y (fun v => b (Sum.inr v))
    * u (Sum.elim (fun v => b (Sum.inl v)) (fun v => b (Sum.inr v))))
  rw [hb]
  ring

/-- The extension of a product of a vector in the first variables and a vector in the second is the
product of the extensions. -/
theorem mle_sumElim_mul (f : (ι → Bool) → K) (g : (ι' → Bool) → K) (x : ι → K) (y : ι' → K) :
    mle (fun b : ι ⊕ ι' → Bool => f (fun v => b (Sum.inl v)) * g (fun v => b (Sum.inr v)))
        (Sum.elim x y) =
      mle f x * mle g y := by
  rw [mle_sumElim]
  simp only [Sum.elim_inl, Sum.elim_inr, mle_smul]
  unfold mle
  rw [sum_mul]
  exact sum_congr rfl fun a _ => by ring

end Pairs

/-! ## Variables numbered 0, ..., n - 1 -/

section FinVars

variable {K : Type*} [CommRing K] {n : ℕ}

/-- A sum over the cube, split at the first coordinate. -/
theorem sum_cube_succ {M : Type*} [AddCommMonoid M] (f : (Fin (n + 1) → Bool) → M) :
    ∑ b, f b = ∑ b : Fin n → Bool, (f (Fin.cons false b) + f (Fin.cons true b)) := by
  have h := (Fin.consEquiv fun _ : Fin (n + 1) => Bool).sum_comp f
  rw [← h, Fintype.sum_prod_type, Fintype.sum_bool, sum_add_distrib, add_comm]
  rfl

theorem eqk_cons (t : K) (z : Fin n → K) (β : Bool) (b : Fin n → Bool) :
    eqk (Fin.cons t z : Fin (n + 1) → K) (Fin.cons β b) = (if β then t else 1 - t) * eqk z b := by
  simp [eqk, Fin.prod_univ_succ]

/-- Folding the first variable. -/
theorem mle_cons (u : (Fin (n + 1) → Bool) → K) (t : K) (z : Fin n → K) :
    mle u (Fin.cons t z : Fin (n + 1) → K) =
      (1 - t) * mle (fun b => u (Fin.cons false b)) z +
        t * mle (fun b => u (Fin.cons true b)) z := by
  unfold mle
  rw [sum_cube_succ, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [eqk_cons, eqk_cons]
  simp
  ring

/-- eq((x, y), b) = eq(x, first part of b) eq(y, second part of b), for tuples written one after the
other. -/
theorem eqk_append {m : ℕ} (x : Fin n → K) (y : Fin m → K) (b : Fin (n + m) → Bool) :
    eqk (Fin.append x y) b =
      eqk x (fun v => b (Fin.castAdd m v)) * eqk y (fun v => b (Fin.natAdd n v)) := by
  simp [eqk, Fin.prod_univ_add]

end FinVars

/-! ## Indices as numbers

An index c < 2^n is read as a vertex of the cube with the most significant bit first: coordinate 0
of the vertex is the highest bit of c. -/

section Numbers

variable {n : ℕ}

/-- The vertex of the cube for the index c. Coordinate v is bit n - 1 - v of c. -/
def bits (n : ℕ) (c : ℕ) : Fin n → Bool := fun v => c.testBit (n - 1 - v)

/-- The number of a vertex: ∑_v b_v 2^(n - 1 - v). -/
def num (b : Fin n → Bool) : ℕ := Nat.ofBits fun i : Fin n => b i.rev

theorem num_lt (b : Fin n → Bool) : num b < 2 ^ n := Nat.ofBits_lt_two_pow _

theorem bits_num (b : Fin n → Bool) : bits n (num b) = b := by
  funext v
  have hv : n - 1 - (v : ℕ) < n := by have := v.2; omega
  unfold bits num
  rw [Nat.testBit_ofBits_lt _ _ hv]
  congr 1
  apply Fin.ext
  simp only [Fin.val_rev]
  have := v.2
  omega

theorem num_bits {c : ℕ} (hc : c < 2 ^ n) : num (bits n c) = c := by
  unfold num bits
  have : (fun i : Fin n => c.testBit (n - 1 - ((i.rev : Fin n) : ℕ))) =
      fun i : Fin n => c.testBit i := by
    funext i
    congr 1
    simp only [Fin.val_rev]
    have := i.2
    omega
  rw [this, Nat.ofBits_testBit, Nat.mod_eq_of_lt hc]

/-- The bijection between the vertices of the cube and the numbers below 2^n. -/
def cubeEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun b := ⟨num b, num_lt b⟩
  invFun c := bits n c
  left_inv b := bits_num b
  right_inv c := Fin.ext (num_bits c.2)

/-- A sum over the vertices is a sum over the numbers below 2^n. -/
theorem sum_num {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ b : Fin n → Bool, f (num b) = ∑ c ∈ range (2 ^ n), f c := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (cubeEquiv n) _ _ fun _ => rfl

/-- A sum over the indices a B + b with a < A and b < B, written as a double sum. -/
theorem sum_range_mul_add {M : Type*} [AddCommMonoid M] (A B : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (A * B), f i = ∑ a ∈ range A, ∑ b ∈ range B, f (a * B + b) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

variable {K : Type*} [CommRing K]

/-- eq(z, c) for an index c < 2^n. An index c ≥ 2^n is reduced modulo 2^n, so a sum over indices
must not go beyond 2^n. -/
def eqN (z : Fin n → K) (c : ℕ) : K := eqk z (bits n c)

/-- ~u(z) = ∑_(c < 2^n) eq(z, c) u[c] for a vector indexed by numbers. -/
def mleN (u : ℕ → K) (z : Fin n → K) : K := ∑ c ∈ range (2 ^ n), eqN z c * u c

theorem eqN_num (z : Fin n → K) (b : Fin n → Bool) : eqN z (num b) = eqk z b := by
  unfold eqN
  rw [bits_num]

/-- The two forms of the multilinear extension agree. -/
theorem mleN_eq_mle (u : ℕ → K) (z : Fin n → K) : mleN u z = mle (fun b => u (num b)) z := by
  unfold mleN mle
  rw [← sum_num fun c => eqN z c * u c]
  simp only [eqN_num]

/-- The extension of a vector indexed by vertices equals the extension of the same vector indexed by
numbers. -/
theorem mle_eq_mleN (u : (Fin n → Bool) → K) (z : Fin n → K) :
    mle u z = mleN (fun c => u (bits n c)) z := by
  rw [mleN_eq_mle]
  simp only [bits_num]

/-- `mleN_eq_mle` for a vector indexed by Fin (2^n). -/
theorem sum_fin_eqN (u : Fin (2 ^ n) → K) (z : Fin n → K) :
    ∑ c : Fin (2 ^ n), eqN z c * u c = mle (fun b => u (cubeEquiv n b)) z := by
  unfold mle
  refine (Fintype.sum_equiv (cubeEquiv n) _ _ fun b => ?_).symm
  rw [← eqN_num]
  rfl

/-- The weights eq(z, ·) sum to 1. -/
theorem sum_eqN (z : Fin n → K) : ∑ c ∈ range (2 ^ n), eqN z c = 1 := by
  rw [← sum_num fun c => eqN z c]
  simp only [eqN_num, sum_eqk]

/-- eq((a, a'), 2^v' i + i') = eq(a, i) eq(a', i') for i' < 2^v'. -/
theorem eqN_append {v v' : ℕ} (a : Fin v → K) (a' : Fin v' → K) (i : ℕ)
    {i' : ℕ} (hi' : i' < 2 ^ v') :
    eqN (Fin.append a a') (2 ^ v' * i + i') = eqN a i * eqN a' i' := by
  unfold eqN
  rw [eqk_append]
  have h1 : (fun w : Fin v => bits (v + v') (2 ^ v' * i + i') (Fin.castAdd v' w)) = bits v i := by
    funext w
    have hw := w.2
    unfold bits
    rw [Nat.testBit_two_pow_mul_add i hi', Fin.val_castAdd, if_neg (by omega)]
    congr 1
    omega
  have h2 : (fun w : Fin v' => bits (v + v') (2 ^ v' * i + i') (Fin.natAdd v w)) = bits v' i' := by
    funext w
    have hw := w.2
    unfold bits
    rw [Nat.testBit_two_pow_mul_add i hi', Fin.val_natAdd, if_pos (by omega)]
    congr 1
    omega
  rw [h1, h2]

/-- Evaluation in two steps, for a vector indexed by numbers: the high bits of the index belong to
the first part of the point. -/
theorem mleN_append {v v' : ℕ} (u : ℕ → K) (a : Fin v → K) (a' : Fin v' → K) :
    mleN u (Fin.append a a') =
      ∑ i ∈ range (2 ^ v), eqN a i * mleN (fun i' => u (2 ^ v' * i + i')) a' := by
  unfold mleN
  rw [pow_add, sum_range_mul_add]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i' hi' => ?_
  rw [mul_comm i, eqN_append a a' i (mem_range.mp hi')]
  ring

end Numbers

/-! ## The Schwartz-Zippel lemma for multilinear extensions, as counts -/

section Counts

variable {K : Type*} [CommRing K] [IsDomain K] [Fintype K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The extension of a non-zero vector vanishes at a uniform point with probability at most (number
of variables) / |K|. -/
theorem count_mle_zero_mul_le (u : (ι → Bool) → K) (hu : u ≠ 0) :
    Nat.card {z : ι → K // mle u z = 0} * Fintype.card K ≤
      Fintype.card ι * Fintype.card (ι → K) := by
  simpa using (DegLE.mle u).count_zero_mul_le ((exists_mle_ne_zero u).mp hu)

/-- Multilinear identity, on the cube and as a count: the extension of a non-zero vector in k
variables vanishes at no more than k |K|^(k - 1) points. -/
theorem count_mle_zero_le (u : (ι → Bool) → K) (hu : u ≠ 0) :
    Nat.card {z : ι → K // mle u z = 0} ≤
      Fintype.card ι * Fintype.card K ^ (Fintype.card ι - 1) := by
  simpa using (DegLE.mle u).count_zero_le ((exists_mle_ne_zero u).mp hu)

/-- Two distinct multilinear polynomials in k variables agree at no more than k |K|^(k - 1) points.
A multilinear polynomial is given by its values on the cube (DegLE.eq_mle). -/
theorem count_mle_eq_le (u w : (ι → Bool) → K) (h : u ≠ w) :
    Nat.card {z : ι → K // mle u z = mle w z} ≤
      Fintype.card ι * Fintype.card K ^ (Fintype.card ι - 1) := by
  refine le_trans (count_mono fun z hz => ?_) (count_mle_zero_le (u - w) (sub_ne_zero.mpr h))
  rw [mle_sub, hz, sub_self]

/-- `count_mle_eq_le` for two distinct functions of degree at most 1 in each variable. -/
theorem count_multilinear_eq_le
    {g h : (ι → K) → K} (hg : DegLE (fun _ => 1) g) (hh : DegLE (fun _ => 1) h) (hne : g ≠ h) :
    Nat.card {z : ι → K // g z = h z} ≤ Fintype.card ι * Fintype.card K ^ (Fintype.card ι - 1) := by
  simpa using hg.count_eq_le hh hne

/-- The multilinear identity for a vector that is placed on the cube through an injection (a vector
whose length is not a power of two, padded with zeros). If d ≠ 0 on the index set J, then ∑_y eq(θ,
enc y) d[y] = 0 for at most k |K|^(k - 1) points θ, where k is the number of variables. -/
theorem count_mle_zero_of_injective {J : Type*} [Fintype J] (enc : J → (ι → Bool))
    (henc : Function.Injective enc) (d : J → K) (hd : d ≠ 0) :
    Nat.card {θ : ι → K // ∑ y, eqk θ (enc y) * d y = 0} ≤
      Fintype.card ι * Fintype.card K ^ (Fintype.card ι - 1) := by
  classical
  let T : (ι → Bool) → K := fun x => ∑ y, if enc y = x then d y else 0
  have hTenc : ∀ y, T (enc y) = d y := by
    intro y
    simp only [T]
    rw [sum_eq_single y]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (henc h))]
    · intro h; exact absurd (mem_univ y) h
  have hT : T ≠ 0 := by
    obtain ⟨y, hy⟩ := Function.ne_iff.mp hd
    intro h
    apply hy
    rw [← hTenc y, h]; rfl
  have e : ∀ θ : ι → K, mle T θ = ∑ y, eqk θ (enc y) * d y := by
    intro θ
    unfold mle
    simp only [T, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_eq_single (enc y)]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb h.symm), mul_zero]
    · intro h; exact absurd (mem_univ _) h
  have := count_mle_zero_le T hT
  simpa only [e] using this

/-- Multilinear identity: a non-zero d ∈ K^(2^v) satisfies ∑_i eq(a, i) d[i] = 0 for at most v
|K|^(v - 1) of the |K|^v points a, that is, for at most a fraction v / |K|. -/
theorem count_eqN_zero_le {v : ℕ} (d : Fin (2 ^ v) → K) (hd : d ≠ 0) :
    Nat.card {a : Fin v → K // ∑ i : Fin (2 ^ v), eqN a i * d i = 0} ≤
      v * Fintype.card K ^ (v - 1) := by
  have := count_mle_zero_of_injective
    (K := K) (fun i : Fin (2 ^ v) => bits v i) (cubeEquiv v).symm.injective d hd
  simpa [eqN] using this

end Counts

end Alg
