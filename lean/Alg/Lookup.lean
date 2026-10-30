-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Alg/Lookup.lean: the mathematics of the look-up argument, without any protocol.

The looked-up values (keys; `key i`) are compared with the table values τ(t) (`tb t`) through two
monic polynomials:
    F(X) = ∏_i (X - key i)                        (`keySide`)
    H(X) = (X - τ⁰)^ϕ ∏_t (X - τ(t))^mult(t)      (`tableSide`)
Here τ⁰ (`tb t0`) is the padding value, ϕ (`pub`) the number of padding positions and mult(t)
(`m t`) a multiplicity. The degrees fit if ϕ plus the sum of the multiplicities is the number of
keys.

  `BadAlpha`, `count_badAlpha_le`   the bad values of the challenge α, zeros of F - H
  `forall_key_in_table`   if the degrees fit, F(α) = H(α) and α is not bad, every key is a table
      value
  `mult`, `planes_eq`   multiplicities in binary, mult(t) = ∑_π 2^π B[t, π] with bits B (`β`);
      plane π: the bits B[t, π] of all t
  `exists_bit`, `sum_mult_eq`   bits; the degree check as an equation of integers
  `chain_of_rel`   Horner's rule in the exponent
  `keySide_eq_tableSide`   for the honest prover: F = H, for the true multiplicities

E is a commutative ring (in the last section a commutative monoid); the counts need a finite domain,
and some other lemmas a nontrivial ring, a domain or a characteristic; `sum_mult_lt` a nonempty
table.

Of this list Blocks/LookupRel.lean uses all but `forall_key_in_table` and `keySide_eq_tableSide`: it
derives the conclusion of the first from `BadAlpha` (`LkPar.inTable_of_ident`) and proves the honest
prover's identity directly (`LkPar.HonB.ident`). These two are here to state the two facts directly.
The levels of a product tree are not in this file: Blocks/LookupRel.lean defines them (`Blocks.lvl`,
`lvl_step`, `lvl_zero`).

Notation: `τ`: in Lean the type of the table's rows t (in the comments τ(t) is the value `tb t`);
`ι`: the type of the keys' positions i; `al`: the challenge α; `β t j`: the bit B[t, π] at π = j;
`pl`: the number of planes.
-/
import Alg.Poly
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.CharP.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Alg.Lookup

open Polynomial Finset

/-! ## The two polynomials -/

section Identity

variable {E : Type*} [CommRing E] {ι τ : Type*} [Fintype ι] [Fintype τ]

/-- The polynomial of the keys: the monic polynomial whose roots are the keys. -/
def keySide (key : ι → E) : E[X] := ∏ i, (X - C (key i))

/-- The polynomial of the table: the monic polynomial whose roots are the table values tb t, each
with the multiplicity m t, and the padding value tb t0 another pub times. -/
def tableSide (tb : τ → E) (t0 : τ) (pub : ℕ) (m : τ → ℕ) : E[X] :=
  (X - C (tb t0)) ^ pub * ∏ t, (X - C (tb t)) ^ m t

theorem keySide_monic (key : ι → E) : (keySide key).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (key i)

theorem keySide_natDegree [Nontrivial E] (key : ι → E) :
    (keySide key).natDegree = Fintype.card ι := by
  unfold keySide
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (key i)]
  simp

theorem keySide_eval (key : ι → E) (al : E) : (keySide key).eval al = ∏ i, (al - key i) := by
  simp [keySide, eval_prod]

theorem tableSide_monic (tb : τ → E) (t0 : τ) (pub : ℕ) (m : τ → ℕ) :
    (tableSide tb t0 pub m).Monic :=
  ((monic_X_sub_C _).pow _).mul (monic_prod_of_monic _ _ fun t _ => (monic_X_sub_C (tb t)).pow _)

theorem tableSide_natDegree [Nontrivial E] (tb : τ → E) (t0 : τ) (pub : ℕ) (m : τ → ℕ) :
    (tableSide tb t0 pub m).natDegree = pub + ∑ t, m t := by
  unfold tableSide
  rw [((monic_X_sub_C (tb t0)).pow pub).natDegree_mul
        (monic_prod_of_monic _ _ fun t _ => (monic_X_sub_C (tb t)).pow _),
    (monic_X_sub_C (tb t0)).natDegree_pow,
    natDegree_prod_of_monic _ _ fun t _ => (monic_X_sub_C (tb t)).pow _]
  simp [(monic_X_sub_C _).natDegree_pow]

theorem tableSide_eval (tb : τ → E) (t0 : τ) (pub : ℕ) (m : τ → ℕ) (al : E) :
    (tableSide tb t0 pub m).eval al = (al - tb t0) ^ pub * ∏ t, (al - tb t) ^ m t := by
  simp [tableSide, eval_prod]

/-- In a domain, a key that is not a table value is a root of keySide and not a root of tableSide,
so the two polynomials differ. -/
theorem keySide_ne_tableSide [IsDomain E] (key : ι → E) (tb : τ → E) (t0 : τ) (pub : ℕ) (m : τ → ℕ)
    (i0 : ι) (h : ∀ t, key i0 ≠ tb t) :
    keySide key ≠ tableSide tb t0 pub m := by
  intro he
  have h1 : (keySide key).eval (key i0) = 0 := by
    rw [keySide_eval]
    exact prod_eq_zero (mem_univ i0) (sub_self _)
  have h2 : (tableSide tb t0 pub m).eval (key i0) ≠ 0 := by
    rw [tableSide_eval]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 (h t0)))
      (prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (sub_ne_zero.2 (h t)))
  exact h2 (he ▸ h1)

/-- If pub plus the sum of the multiplicities is the number of keys, and the two polynomials differ,
their difference has degree below the number of keys. -/
theorem natDegree_sides_sub_lt [Nontrivial E] (key : ι → E) (tb : τ → E) (t0 : τ) (pub : ℕ)
    (m : τ → ℕ) (hdeg : pub + ∑ t, m t = Fintype.card ι)
    (hne : keySide key ≠ tableSide tb t0 pub m) :
    (keySide key - tableSide tb t0 pub m).natDegree < Fintype.card ι := by
  have hnd : (keySide key).natDegree = (tableSide tb t0 pub m).natDegree := by
    rw [keySide_natDegree, tableSide_natDegree, hdeg]
  have hd : (keySide key).degree = (tableSide tb t0 pub m).degree := by
    rw [degree_eq_natDegree (keySide_monic key).ne_zero,
      degree_eq_natDegree (tableSide_monic tb t0 pub m).ne_zero, hnd]
  have hlt := degree_sub_lt hd (keySide_monic key).ne_zero
    ((keySide_monic key).leadingCoeff.trans (tableSide_monic tb t0 pub m).leadingCoeff.symm)
  have := natDegree_lt_natDegree (sub_ne_zero.2 hne) hlt
  rwa [keySide_natDegree] at this

/-- The value al of α is bad: the degrees fit, some key is not a table value, and `keySide` and
`tableSide` agree at al. -/
def BadAlpha (key : ι → E) (tb : τ → E) (t0 : τ) (pub : ℕ) (m : τ → ℕ) (al : E) : Prop :=
  pub + ∑ t, m t = Fintype.card ι ∧ (∃ i, ∀ t, key i ≠ tb t) ∧
    ∏ i, (al - key i) = (al - tb t0) ^ pub * ∏ t, (al - tb t) ^ m t

/-- The number of bad values of α is at most the number of keys minus 1. -/
theorem count_badAlpha_le [IsDomain E] [Finite E] (key : ι → E) (tb : τ → E)
    (t0 : τ) (pub : ℕ) (m : τ → ℕ) :
    Nat.card {al : E // BadAlpha key tb t0 pub m al} ≤ Fintype.card ι - 1 := by
  by_cases h : pub + ∑ t, m t = Fintype.card ι ∧ ∃ i, ∀ t, key i ≠ tb t
  · obtain ⟨hdeg, i0, hi0⟩ := h
    have hne := keySide_ne_tableSide key tb t0 pub m i0 hi0
    have hlt := natDegree_sides_sub_lt key tb t0 pub m hdeg hne
    refine le_trans (count_mono fun al hal => ?_)
      (count_roots_le (sub_ne_zero.2 hne) (d := Fintype.card ι - 1) (by omega))
    rw [eval_sub, keySide_eval, tableSide_eval, sub_eq_zero]
    exact hal.2.2
  · rw [count_eq_zero fun al hal => h ⟨hal.1, hal.2.1⟩]
    exact Nat.zero_le _

/-- If the degrees fit, the two products agree at α, and α is not bad, every key is a table
value. -/
theorem forall_key_in_table {key : ι → E} {tb : τ → E} {t0 : τ} {pub : ℕ} {m : τ → ℕ} {al : E}
    (hdeg : pub + ∑ t, m t = Fintype.card ι)
    (heq : ∏ i, (al - key i) = (al - tb t0) ^ pub * ∏ t, (al - tb t) ^ m t)
    (hbad : ¬ BadAlpha key tb t0 pub m al) (i : ι) : ∃ t, key i = tb t := by
  by_contra hi
  exact hbad ⟨hdeg, ⟨i, fun t ht => hi ⟨t, ht⟩⟩, heq⟩

/-- For the honest prover: `keySide` = `tableSide` as an identity of polynomials. The keys at
padding positions are the padding value; every other key i is the table value `tb (row i)`; the
multiplicity of t is the number of keys outside padding positions with row i = t. -/
theorem keySide_eq_tableSide [DecidableEq τ] (key : ι → E) (tb : τ → E) (t0 : τ) (pad : ι → Prop)
    [DecidablePred pad] (row : ι → τ) (h0 : ∀ i, pad i → key i = tb t0)
    (h1 : ∀ i, ¬ pad i → key i = tb (row i)) :
    keySide key =
      tableSide tb t0 (univ.filter pad).card
        (fun t => ((univ.filter fun i => ¬ pad i).filter fun i => row i = t).card) := by
  unfold keySide tableSide
  rw [← prod_filter_mul_prod_filter_not univ pad]
  congr 1
  · rw [prod_congr rfl fun i hi => by rw [h0 i (mem_filter.mp hi).2], prod_const]
  · rw [← prod_fiberwise_of_maps_to (s := univ.filter fun i => ¬ pad i) (t := univ)
        (g := row) fun _ _ => mem_univ _]
    refine prod_congr rfl fun t _ => ?_
    rw [prod_congr rfl fun i hi => by
      rw [h1 i (mem_filter.mp (mem_filter.mp hi).1).2, (mem_filter.mp hi).2], prod_const]

end Identity

/-! ## Multiplicities in binary -/

section Planes

variable {E : Type*} [CommRing E] {τ : Type*} [Fintype τ]

/-- In a domain, an element with b (b - 1) = 0 is 0 or 1. -/
theorem exists_bit [IsDomain E] {b : E} (h : b * (b - 1) = 0) :
    ∃ β : Bool, b = if β then 1 else 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact ⟨false, by simpa using h⟩
  · exact ⟨true, by simpa using sub_eq_zero.mp h⟩

/-- The leaf of the table side: 1 + b (α - 1 - r) is α - r if the bit b is 1, and 1 if it is 0. -/
theorem leaf_eq (al r : E) (β : Bool) :
    1 + (if β then (1 : E) else 0) * (al - 1 - r) = (al - r) ^ (if β then 1 else 0) := by
  cases β
  · simp
  · simp only [if_true, one_mul, pow_one]
    ring

/-- The multiplicity of t that the bits β encode: ∑_(π < pl) 2^π β[t, π]. -/
def mult (pl : ℕ) (β : τ → ℕ → Bool) (t : τ) : ℕ := ∑ j ∈ range pl, if β t j then 2 ^ j else 0

omit [Fintype τ] in
theorem mult_lt (pl : ℕ) (β : τ → ℕ → Bool) (t : τ) : mult pl β t < 2 ^ pl := by
  unfold mult
  induction pl with
  | zero => simp
  | succ pl ih =>
    rw [sum_range_succ, pow_succ]
    split_ifs <;> omega

/-- ∏_π (∏_t (1 + B[t, π] (α - 1 - τ(t))))^(2^π) = ∏_t (α - τ(t))^mult(t). -/
theorem planes_eq (pl : ℕ) (β : τ → ℕ → Bool) (tb : τ → E) (al : E) :
    ∏ j ∈ range pl, (∏ t, (1 + (if β t j then (1 : E) else 0) * (al - 1 - tb t))) ^ 2 ^ j =
      ∏ t, (al - tb t) ^ mult pl β t := by
  simp only [leaf_eq, mult, ← prod_pow, ← pow_mul]
  rw [prod_comm]
  refine prod_congr rfl fun t _ => ?_
  rw [← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun j _ => ?_
  cases β t j <;> simp

/-- The sum of all bits, each with the weight 2^π, as an element of E, is the image of the sum of
the multiplicities. -/
theorem sum_bits_eq (pl : ℕ) (β : τ → ℕ → Bool) :
    ∑ t, ∑ j ∈ range pl, (2 : E) ^ j * (if β t j then (1 : E) else 0) =
      ((∑ t, mult pl β t : ℕ) : E) := by
  simp only [mult]
  push_cast
  refine sum_congr rfl fun t _ => sum_congr rfl fun j _ => ?_
  cases β t j <;> simp

theorem sum_mult_lt [Nonempty τ] (pl : ℕ) (β : τ → ℕ → Bool) :
    ∑ t, mult pl β t < Fintype.card τ * 2 ^ pl := by
  have h :=
    sum_lt_sum_of_nonempty (s := (univ : Finset τ)) univ_nonempty (fun t _ => mult_lt pl β t)
  simpa using h

/-- The degree check as an equation of integers: in characteristic p, if the weighted sum of the
bits equals D in E, and the sum of the multiplicities and D are below p, then the multiplicities sum
to D. -/
theorem sum_mult_eq (p : ℕ) [CharP E p] (pl : ℕ) (β : τ → ℕ → Bool) (D : ℕ)
    (hS : ∑ t, ∑ j ∈ range pl, (2 : E) ^ j * (if β t j then (1 : E) else 0) = (D : E))
    (h1 : ∑ t, mult pl β t < p) (h2 : D < p) : ∑ t, mult pl β t = D := by
  rw [sum_bits_eq] at hS
  exact Nat.ModEq.eq_of_lt_of_lt ((CharP.natCast_eq_natCast E p).1 hS) h1 h2

/-- The sum of 2^j over the positions j < pl at which n has the binary digit 1 is n % 2^pl. -/
theorem sum_testBit (pl n : ℕ) :
    (∑ j ∈ range pl, if n.testBit j then 2 ^ j else 0) = n % 2 ^ pl := by
  induction pl with
  | zero => simp [Nat.mod_one]
  | succ pl ih =>
    rw [sum_range_succ, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ pl) with h | h <;> simp [h]

omit [Fintype τ] in
/-- The honest bits: the binary digits of a multiplicity below 2^pl encode it. -/
theorem mult_testBit (pl : ℕ) (m : τ → ℕ) (t : τ) (h : m t < 2 ^ pl) :
    mult pl (fun t j => (m t).testBit j) t = m t := by
  unfold mult
  rw [sum_testBit, Nat.mod_eq_of_lt h]

end Planes

/-! ## Horner's rule in the exponent: squaring and multiplying -/

section Chain

variable {E : Type*} [CommMonoid E]

/-- The chain that combines the products g 0, g 1, ... of the planes, from the highest plane down:
chainFrom g 0 j = g j, and chainFrom g (d + 1) j is the square of chainFrom g d (j + 1) times g
j. -/
def chainFrom (g : ℕ → E) : (d : ℕ) → (j : ℕ) → E
  | 0, j => g j
  | d + 1, j => chainFrom g d (j + 1) ^ 2 * g j

/-- chainFrom g d j is the product over u ≤ d of g (j + u) to the power 2^u. -/
theorem chainFrom_eq_prod (g : ℕ → E) (d j : ℕ) :
    chainFrom g d j = ∏ u ∈ range (d + 1), g (j + u) ^ 2 ^ u := by
  induction d generalizing j with
  | zero => simp [chainFrom]
  | succ d ih =>
    rw [chainFrom, ih, prod_range_succ' _ (d + 1), ← prod_pow]
    simp only [pow_zero, pow_one, Nat.add_zero]
    congr 1
    refine prod_congr rfl fun u _ => ?_
    rw [← pow_mul, pow_succ, Nat.add_assoc, Nat.add_comm 1 u]

/-- Horner's rule in the exponent. If U_P = Y_P and, for π < P, V_π = U_(π+1)² and U_π = V_π Y_π,
then U_0 = ∏_(π ≤ P) Y_π^(2^π). -/
theorem chain_of_rel (P : ℕ) (Y U V : ℕ → E) (hP : U P = Y P)
    (hV : ∀ π < P, V π = U (π + 1) ^ 2) (hU : ∀ π < P, U π = V π * Y π) :
    U 0 = ∏ π ∈ range (P + 1), Y π ^ 2 ^ π := by
  have key : ∀ d, d ≤ P → U (P - d) = chainFrom Y d (P - d) := by
    intro d
    induction d with
    | zero => intro _; simpa [chainFrom] using hP
    | succ d ih =>
      intro hd
      have h1 : P - (d + 1) < P := by omega
      have h2 : P - (d + 1) + 1 = P - d := by omega
      rw [chainFrom, hU _ h1, hV _ h1, h2, ih (by omega)]
  have h := key P le_rfl
  rw [Nat.sub_self, chainFrom_eq_prod] at h
  simpa using h

end Chain

end Alg.Lookup
