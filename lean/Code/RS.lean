-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/RS.lean: Reed–Solomon codes with a randomised encoder.

Parts 1 to 3 hold over any field, Part 4 over finite fields F and E, where E is an extension of F.

An input of k symbols is read as the coefficients of a polynomial of degree below k, and its
codeword is the list of the values of that polynomial at n distinct points x j. The encoder puts the
message at the exponents 0, ..., ℓ - 1 (ℓ: `msg`) and r uniform coordinates at the
exponents i0, ..., i0 + r - 1.

 * Part 1: the generator `gen x ex` for any family `ex` of exponents.
 * Part 2, for distinct exponents below k ≤ n: a non-zero input has an image of weight at least
   n - k + 1 (`le_weight`), attained for the exponents 0, ..., k - 1 if k ≥ 1; the generator is
   injective.
 * Part 3: the contribution of the randomness to the codeword is onto on every set of at most r
   positions, if no point is 0 or i0 = 0 (`ontoUpTo_gen_shift`). If a point is 0 and i0 > 0, it is
   not onto even on one position (`not_ontoUpTo_of_zero`), so not even one position is hidden (by
   `queryUniform_iff_ontoUpTo`, Code/QueryUniform.lean). This file does not state that last step,
   nor, for general i0, that the encoder is b-query uniform exactly for b ≤ r (for i0 = ℓ: Part 4).
 * Part 4: `Enc.Props` for `RS.code`, of type `Code.Enc` (Code/Iface.lean), under hypotheses:
   `props` (among them a bound on the bad θ of mutual correlated agreement), `props_third` (without
   it, for 3e < n - k + 1), `props_natPoints` (at the points 1, ..., n, under conditions on numbers
   only). Its randomness is that of Part 3 with i0 = ℓ if msg + r ≤ k (`code_share`), and it hides
   no more than r positions (`le_of_hides`).

The labels (P1), (P2) and (P3) are those of `Enc.Props` (Code/Iface.lean).
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.CharP.Basic
import Code.Iface
import Code.QueryUniform
import Code.Facts
import Code.Third
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Code.RS

open Polynomial Function Prob

/-! ## Part 1. The generator and its polynomial -/

section Gen

variable {K : Type*} [Field K] {ι P : Type*} [Fintype ι]

/-- The polynomial with the coefficient v i at the exponent ex i. -/
def poly (ex : ι → ℕ) (v : ι → K) : K[X] := ∑ i, C (v i) * X ^ ex i

theorem eval_poly (ex : ι → ℕ) (v : ι → K) (t : K) : (poly ex v).eval t = ∑ i, v i * t ^ ex i := by
  simp [poly, eval_finset_sum]

theorem coeff_poly {ex : ι → ℕ} (hex : Injective ex) (v : ι → K) (i : ι) :
    (poly ex v).coeff (ex i) = v i := by
  classical
  simp only [poly, finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [if_neg (fun h => hb (hex h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem poly_ne_zero {ex : ι → ℕ} (hex : Injective ex) {v : ι → K} (hv : v ≠ 0) :
    poly ex v ≠ 0 := by
  intro h0
  refine hv (funext fun i => ?_)
  rw [← coeff_poly hex v i, h0, coeff_zero]
  rfl

theorem degree_poly_lt {ex : ι → ℕ} {k : ℕ} (hk : ∀ i, ex i < k) (v : ι → K) :
    (poly ex v).degree < (k : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe k)).2 fun i _ => ?_)
  have h : ((ex i : ℕ) : WithBot ℕ) < (k : WithBot ℕ) := by exact_mod_cast hk i
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) h

/-- The generator: the input v goes to the values, at the points x j, of the polynomial with the
coefficient v i at the exponent ex i. -/
def gen (x : P → K) (ex : ι → ℕ) : (ι → K) →ₗ[K] (P → K) where
  toFun v := fun j => ∑ i, v i * x j ^ ex i
  map_add' u v := by
    funext j
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem gen_apply (x : P → K) (ex : ι → ℕ) (v : ι → K) (j : P) :
    gen x ex v j = ∑ i, v i * x j ^ ex i := rfl

theorem gen_eq_eval (x : P → K) (ex : ι → ℕ) (v : ι → K) (j : P) :
    gen x ex v j = (poly ex v).eval (x j) :=
  (eval_poly ex v (x j)).symm

omit [Fintype ι] in
/-- The coefficients of a polynomial of degree below k go to its values. -/
theorem gen_coeff {k : ℕ} {p : K[X]} (hp : p.degree < (k : WithBot ℕ)) (x : P → K) (j : P) :
    gen x (fun i : Fin k => (i : ℕ)) (fun i => p.coeff i) j = p.eval (x j) := by
  rw [gen_apply, Fin.sum_univ_eq_sum_range (fun i => p.coeff i * x j ^ i) k]
  by_cases h0 : p = 0
  · simp [h0]
  · exact (eval_eq_sum_range' ((natDegree_lt_iff_degree_lt h0).2 hp) _).symm

/-- Raising all exponents by i0 multiplies the symbol at the point x j by x j ^ i0. -/
theorem gen_shift (x : P → K) (ex : ι → ℕ) (i0 : ℕ) (v : ι → K) (j : P) :
    gen x (fun i => i0 + ex i) v j = x j ^ i0 * gen x ex v j := by
  rw [gen_apply, gen_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring

end Gen

/-! ## Part 2. Distance -/

section Distance

variable {K : Type*} [Field K] {ι P : Type*} [Fintype ι] {x : P → K} {ex : ι → ℕ} {k : ℕ}

/-- With distinct exponents below k, the codeword of a non-zero input is 0 at fewer than k of the
distinct points. -/
theorem card_zeros_lt (hx : Injective x) (hex : Injective ex) (hk : ∀ i, ex i < k)
    {v : ι → K} (hv : v ≠ 0) :
    Nat.card {j : P // gen x ex v j = 0} < k := by
  classical
  have hP := poly_ne_zero hex hv
  let f : {j : P // gen x ex v j = 0} → (poly ex v).roots.toFinset := fun j =>
    ⟨x j, by
      rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, ← gen_eq_eval]
      exact j.2⟩
  have hf : Injective f := fun a b hab =>
    Subtype.ext (hx (congrArg (fun z : (poly ex v).roots.toFinset => (z : K)) hab))
  have h1 : Nat.card {j : P // gen x ex v j = 0} ≤ (poly ex v).roots.toFinset.card := by
    have h := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card (α := (poly ex v).roots.toFinset), Fintype.card_coe] at h
  have h2 : ((poly ex v).roots.toFinset.card : WithBot ℕ) ≤ (poly ex v).degree :=
    le_trans (by exact_mod_cast Multiset.toFinset_card_le _) (card_roots hP)
  have h3 : ((poly ex v).roots.toFinset.card : WithBot ℕ) < k :=
    lt_of_le_of_lt h2 (degree_poly_lt hk v)
  exact lt_of_le_of_lt h1 (by exact_mod_cast h3)

variable [Finite P]

/-- The positions split into those with the symbol 0 and the others. -/
theorem card_ne_zero_add (w : P → K) :
    Nat.card {j : P // w j ≠ 0} + Nat.card {j : P // w j = 0} = Nat.card P := by
  classical
  haveI := Fintype.ofFinite P
  have h1 : Nat.card {j : P // w j ≠ 0} = Nat.card P - Nat.card {j : P // w j = 0} := by
    simp only [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  have h2 : Nat.card {j : P // w j = 0} ≤ Nat.card P :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  omega

/-- The bound. With n distinct points and distinct exponents below k ≤ n, the codeword of a
non-zero input has at least n - k + 1 symbols that are not 0. -/
theorem le_weight (hx : Injective x) (hex : Injective ex) (hk : ∀ i, ex i < k)
    (hkn : k ≤ Nat.card P) {v : ι → K} (hv : v ≠ 0) :
    Nat.card P - k + 1 ≤ Nat.card {j : P // gen x ex v j ≠ 0} := by
  have h0 := card_zeros_lt hx hex hk hv
  have h1 := card_ne_zero_add (gen x ex v)
  omega

/-- With points and exponents as in `le_weight`, two different inputs have codewords that differ at
n - k + 1 positions or more. -/
theorem le_dist (hx : Injective x) (hex : Injective ex) (hk : ∀ i, ex i < k) (hkn : k ≤ Nat.card P)
    {u v : ι → K} (huv : u ≠ v) :
    Nat.card P - k + 1 ≤ Nat.card {j : P // gen x ex u j ≠ gen x ex v j} := by
  refine (le_weight hx hex hk hkn (sub_ne_zero.2 huv)).trans
    (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)))
  rw [map_sub, Pi.sub_apply, sub_ne_zero]

/-- The rank. With points and exponents as in `le_weight`, the generator is injective. -/
theorem gen_injective (hx : Injective x) (hex : Injective ex)
    (hk : ∀ i, ex i < k) (hkn : k ≤ Nat.card P) : Injective (gen x ex) := by
  intro u v huv
  by_contra hne
  have h1 := le_dist hx hex hk hkn hne
  haveI : IsEmpty {j : P // gen x ex u j ≠ gen x ex v j} := ⟨fun j => j.2 (congrFun huv j)⟩
  have h2 : Nat.card {j : P // gen x ex u j ≠ gen x ex v j} = 0 := Nat.card_of_isEmpty
  omega

omit [Finite P] in
/-- `le_weight` in terms of Mathlib's Hamming norm. -/
theorem le_hammingNorm [Fintype P] [DecidableEq K] (hx : Injective x) (hex : Injective ex)
    (hk : ∀ i, ex i < k) (hkn : k ≤ Fintype.card P) {v : ι → K} (hv : v ≠ 0) :
    Fintype.card P - k + 1 ≤ hammingNorm (gen x ex v) := by
  have h := le_weight hx hex hk (by rw [Nat.card_eq_fintype_card]; exact hkn) hv
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

omit [Fintype ι] in
/-- Equality. For distinct points and 1 ≤ k ≤ n some codeword of the full code has exactly n - k +
1 symbols that are not 0. So n - k + 1 is the minimum distance. -/
theorem exists_weight_eq (hx : Injective x) (hk1 : 1 ≤ k) (hkn : k ≤ Nat.card P) :
    ∃ v : Fin k → K,
      v ≠ 0 ∧ Nat.card {j : P // gen x (fun i : Fin k => (i : ℕ)) v j ≠ 0} =
        Nat.card P - k + 1 := by
  classical
  haveI := Fintype.ofFinite P
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset P)) (n := k - 1)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  let p : K[X] := ∏ j ∈ T, (X - C (x j))
  have hmon : p.Monic := monic_prod_X_sub_C x T
  have hnd : p.natDegree = k - 1 := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp [hT]
  have hdeg : p.degree < (k : WithBot ℕ) := by
    rw [degree_eq_natDegree hmon.ne_zero, hnd]
    exact_mod_cast (by omega : k - 1 < k)
  have hne : ∀ j, gen x (fun i : Fin k => (i : ℕ)) (fun i => p.coeff i) j ≠ 0 ↔ j ∉ T := by
    intro j
    rw [gen_coeff hdeg, eval_prod, Finset.prod_ne_zero_iff]
    simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
    constructor
    · intro h hj
      exact h j hj rfl
    · intro h j' hj' he
      exact h (hx he ▸ hj')
  refine ⟨fun i => p.coeff i, fun h0 => ?_, ?_⟩
  · have h1 : p.coeff (k - 1) = 0 := congrFun h0 ⟨k - 1, by omega⟩
    rw [← hnd, hmon.coeff_natDegree] at h1
    exact one_ne_zero h1
  · rw [Nat.card_congr (Equiv.subtypeEquivRight hne), Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_coe, hT, Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card] at hkn
    omega

end Distance

/-! ## Part 3. Hidden positions -/

section Hiding

variable {K : Type*} [Field K] {P : Type*} {x : P → K}

/-- Hidden positions, the linear algebra. Let the points be distinct, let the r uniform coordinates
be at the exponents i0, ..., i0 + r - 1, and let x j ^ i0 ≠ 0 for all points (no point is 0, or i0 =
0). Then on every set of at most r positions their contribution to the codeword takes all patterns:
any r rows x j ^ i0 · (1, x j, ..., x j ^ (r - 1)) are linearly independent. -/
theorem ontoUpTo_gen_shift (hx : Injective x) (i0 r : ℕ) (h0 : ∀ j, x j ^ i0 ≠ 0) :
    OntoUpTo (gen x fun t : Fin r => i0 + (t : ℕ)) r := by
  classical
  intro S hS w
  let w' : P → K := fun j => if h : j ∈ S then w ⟨j, h⟩ / x j ^ i0 else 0
  have hinj : Set.InjOn x S := hx.injOn
  have hdeg : (Lagrange.interpolate S x w').degree < (r : WithBot ℕ) :=
    lt_of_lt_of_le (Lagrange.degree_interpolate_lt w' hinj) (by exact_mod_cast hS)
  refine ⟨fun t => (Lagrange.interpolate S x w').coeff t, funext fun j => ?_⟩
  rw [restr_apply, gen_shift x (fun t : Fin r => (t : ℕ)) i0, gen_coeff hdeg,
    Lagrange.eval_interpolate_at_node w' hinj j.2]
  show x j ^ i0 * (if h : (j : P) ∈ S then w ⟨j, h⟩ / x j ^ i0 else 0) = w j
  rw [dif_pos j.2, mul_comm, div_mul_cancel₀ _ (h0 j)]

/-- The case i0 = 0, for distinct points: on every set of at most r positions the codewords of
inputs of r coordinates take all patterns. -/
theorem ontoUpTo_gen (hx : Injective x) (r : ℕ) : OntoUpTo (gen x fun t : Fin r => (t : ℕ)) r := by
  have h := ontoUpTo_gen_shift hx 0 r fun j => by rw [pow_zero]; exact one_ne_zero
  simpa only [Nat.zero_add] using h

/-- If a point is 0 and i0 > 0, the share of the randomness is 0 at that point, so it is not onto
even on one position. -/
theorem not_ontoUpTo_of_zero {j : P} (hj : x j = 0) {i0 : ℕ} (hi0 : 0 < i0) (r : ℕ) :
    ¬ OntoUpTo (gen x fun t : Fin r => i0 + (t : ℕ)) 1 := by
  intro h
  obtain ⟨μ, hμ⟩ := h {j} (by simp) (fun _ => 1)
  have h1 : gen x (fun t : Fin r => i0 + (t : ℕ)) μ j = 1 :=
    congrFun hμ ⟨j, Finset.mem_singleton_self j⟩
  rw [gen_shift x (fun t : Fin r => (t : ℕ)) i0, hj, zero_pow (by omega), zero_mul] at h1
  exact zero_ne_one h1



variable [Fintype K] [DecidableEq P]


end Hiding

/-! ## Part 4. The code as a code with encoder -/

section Interface

variable {F : Type} [Field F] {n : ℕ}

/-- The Reed–Solomon code as a code with encoder. The points are x, the dimension is k; the message
has msg symbols and is followed by r uniform coordinates. The fields d and b are set to n - k + 1
and r (`props` justifies them, under its hypotheses). The proximity parameter e and the count mca
for mutual correlated agreement are parameters. -/
def code (x : Fin n → F) (k msg r e mca : ℕ) : Enc F where
  n := n
  k := k
  msg := msg
  r := r
  G := Matrix.of fun j i => x j ^ (i : ℕ)
  d := n - k + 1
  e := e
  b := r
  mca := mca

variable (x : Fin n → F) (k msg r e mca : ℕ)

/-- The matrix of `code` acts as the generator of Part 1. -/
theorem code_mulVec (v : Fin k → F) (j : Fin n) :
    (code x k msg r e mca).G.mulVec v j = gen x (fun i : Fin k => (i : ℕ)) v j := by
  simp only [code, Matrix.mulVec, dotProduct, Matrix.of_apply, gen_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The code over E is the Reed–Solomon code over E at the same points. -/
theorem code_GE (E : Type) [Field E] [Algebra F E] :
    (code x k msg r e mca).GE E = (code (fun j => algebraMap F E (x j)) k msg r e mca).G := by
  ext j i
  simp [Enc.GE, code]

/-- If msg + r ≤ k, the contribution of the randomness (`Enc.share`) is that of Part 3, with i0 =
msg. -/
theorem code_share (hp : msg + r ≤ k) (ρ : Fin r → F) (j : Fin n) :
    (code x k msg r e mca).share ρ j = gen x (fun t : Fin r => msg + (t : ℕ)) ρ j := by
  rw [Enc.share_apply]
  have h := (code x k msg r e mca).sum_mul_fm_rand hp (fun i => (code x k msg r e mca).G j i) ρ
  refine Eq.trans h ?_
  rw [gen_apply]
  exact Finset.sum_congr rfl fun t _ => mul_comm _ _

variable {x k msg r e mca}

/-- (P1) for `code`, if the points are distinct and k ≤ n. -/
theorem code_dist (hx : Injective x) (hkn : k ≤ n) (v : Fin k → F) (hv : v ≠ 0) :
    n - k + 1 ≤ cnt (fun j => (code x k msg r e mca).G.mulVec v j ≠ 0) := by
  have h := le_weight hx (ex := fun i : Fin k => (i : ℕ)) Fin.val_injective (fun i => i.2)
    (by rw [Nat.card_fin]; exact hkn) hv
  rw [Nat.card_fin] at h
  refine h.trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun j => ?_)))
  rw [code_mulVec]

/-- The linear algebra behind (P3) for `code`, if the points are distinct and not 0 and msg + r ≤
k. -/
theorem code_ontoUpTo (hx : Injective x) (hx0 : ∀ j, x j ≠ 0) (hp : msg + r ≤ k) :
    OntoUpTo (code x k msg r e mca).share r := by
  have e1 : (code x k msg r e mca).share = gen x (fun t : Fin r => msg + (t : ℕ)) :=
    LinearMap.ext fun ρ => funext fun j => code_share x k msg r e mca hp ρ j
  rw [e1]
  exact ontoUpTo_gen_shift hx msg r fun j => pow_ne_zero _ (hx0 j)

variable [Fintype F] {E : Type} [Field E] [Finite E] [Algebra F E]

/-- Reed–Solomon codes with (P2) as a hypothesis. If the n points are distinct and not 0, msg + r ≤
k ≤ n, 2e < n - k + 1, and at most mca values of θ are bad for mutual correlated agreement at e
positions, then `code` has `Enc.Props`. -/
theorem props (hx : Injective x) (hx0 : ∀ j, x j ≠ 0) (hp : msg + r ≤ k) (hkn : k ≤ n)
    (he : 2 * e < n - k + 1) (hmca : (code x k msg r e mca).MCA E e mca) :
    (code x k msg r e mca).Props E where
  place := hp
  dist := code_dist hx hkn
  unique := he
  mca := hmca
  hides := ((code x k msg r e mca).hides_iff_ontoUpTo r).2 (code_ontoUpTo hx hx0 hp)

/-- Without the hypothesis on (P2): under the other hypotheses of `props` and 3e < n - k + 1, `code`
with mca = e + 1 has `Enc.Props`. -/
theorem props_third (hx : Injective x) (hx0 : ∀ j, x j ≠ 0) (hp : msg + r ≤ k) (hkn : k ≤ n)
    (he : 3 * e < n - k + 1) : (code x k msg r e (e + 1)).Props E :=
  props hx hx0 hp hkn (by omega) ((code x k msg r e (e + 1)).mca_third (code_dist hx hkn) he)

/-- Explicit points: 1, 2, ..., n, read in F. -/
def natPoints (F : Type) [Field F] (n : ℕ) : Fin n → F := fun j => (((j : ℕ) + 1 : ℕ) : F)

omit [Fintype F] in
/-- In characteristic p > n the points 1, ..., n are distinct. -/
theorem natPoints_injective (p : ℕ) [CharP F p] (hn : n < p) : Injective (natPoints F n) := by
  intro a b hab
  have h := CharP.natCast_injOn_Iio
    F p (show (a : ℕ) + 1 ∈ Set.Iio p from by have := a.2; simp only [Set.mem_Iio]; omega)
    (show (b : ℕ) + 1 ∈ Set.Iio p from by have := b.2; simp only [Set.mem_Iio]; omega) hab
  exact Fin.ext (by omega)

omit [Fintype F] in
/-- In characteristic p > n none of the points 1, ..., n is 0. -/
theorem natPoints_ne_zero (p : ℕ) [CharP F p] (hn : n < p) (j : Fin n) : natPoints F n j ≠ 0 := by
  intro h0
  have h1 : p ∣ (j : ℕ) + 1 := (CharP.cast_eq_zero_iff F p _).1 h0
  have h2 := Nat.le_of_dvd (Nat.succ_pos _) h1
  have := j.2
  omega

/-- A Reed–Solomon code with all properties, under conditions on numbers only. Over a field of
characteristic p > n, at the points 1, ..., n, with msg + r ≤ k ≤ n and 3e < n - k + 1: distance n -
k + 1, at most e + 1 bad values of θ, and r hidden positions. -/
theorem props_natPoints (p : ℕ) [CharP F p] (hn : n < p) (hp : msg + r ≤ k)
    (hkn : k ≤ n) (he : 3 * e < n - k + 1) :
    (code (natPoints F n) k msg r e (e + 1)).Props E :=
  props_third (natPoints_injective p hn) (natPoints_ne_zero p hn) hp hkn he

omit [Field E] [Finite E] [Algebra F E] in
/-- The encoder of `code` hides no more than r positions: if any b ≤ n positions are uniform, then
b ≤ r. -/
theorem le_of_hides {b : ℕ} (hb : b ≤ n)
    (h : ∀ S : Finset (Fin n), S.card ≤ b →
      ∀ m : Fin msg → F,
        (PMF.uniformOfFintype (Fin r → F)).map
            (fun ρ => fun j : S => (code x k msg r e mca).enc m ρ (j : Fin n)) =
          PMF.uniformOfFintype (S → F)) : b ≤ r := by
  have h1 : OntoUpTo (code x k msg r e mca).share b :=
    ((code x k msg r e mca).hides_iff_ontoUpTo b).1 h
  have h2 := h1.le_card (by rw [Fintype.card_fin]; exact hb)
  rwa [Fintype.card_fin] at h2

end Interface

end Code.RS
