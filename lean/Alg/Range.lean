-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Alg/Range.lean: the algebra and the counts of the approximate range proof, without any protocol.

A cell is an integer. Three cells of one column are packed into one element of the ring E, at the
radix rad. The window is [-t, t); a cell is small if its absolute value is below 2 t.
  * Step 1 (`small_unique`): a column of packed elements has at most one column of small cells, if
    t > 0, 4 t - 1 ≤ rad and (4 t - 2)(1 + rad + rad²) is below the characteristic, and the packed
    elements cover the column (symRows m ≤ s).
  * Step 2 (`goodColumn_of_canPass_two`): if a random combination can pass with the coefficient 0 at
    a column and also with ±1 there, the other coefficients being the same, the column is good
    (`GoodColumn`).
  * Step 3 (`cnt_canPass_mul_le`, `cnt_allPass_mul_le`): so if some column of some matrix is not
    good, all |U| combinations can pass for at most the fraction 2^(-|U|) of the challenges. No
    union bound over columns or matrices is used.

The counts come from Prob/Window.lean and Prob/Count.lean.

Notation: `m`: the number of rows of a column of cells; `s`: the number of packed elements of a
column; `C`, `R`, `U`, `Mx`: types, the columns, the reads, the combinations, the matrices; `Ξ`: the
challenge, an array of coefficients; `Coef` (Prob/Window.lean): one coefficient, as two bits: the
support bit and the sign bit; `Coef.val`: 0 if the support bit is 0, otherwise +1 or -1 by the sign
bit; `cnt P` (Prob/Cnt.lean): the number of elements of a finite type with the property P; in the
section `Matrices`, `m`, `s`, `C`, `R` are families, one for each matrix μ.
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Prob.Window

namespace Alg

open Finset Prob

/-! ## Lanes and packing -/

/-- The number of packed rows of a matrix of m rows. -/
def symRows (m : ℕ) : ℕ := (m + 2) / 3

/-- Lane l of packed row i' of a column with m entries: the entry of row 3 i' + l, or 0 if there is
no such row. -/
def lane {A : Type} [Zero A] {m : ℕ} (a : Fin m → A) (i' l : ℕ) : A :=
  if h : 3 * i' + l < m then a ⟨3 * i' + l, h⟩ else 0

/-- The three lanes of packed row i', packed at the radix rad. -/
def pack {A : Type} [CommRing A] (rad : ℤ) {m : ℕ} (a : Fin m → A) (i' : ℕ) : A :=
  lane a i' 0 + (rad : A) * lane a i' 1 + (rad : A) ^ 2 * lane a i' 2

section Linear

variable {A : Type} [CommRing A] {m : ℕ} (rad : ℤ)

theorem lane_div_mod {B : Type} [Zero B] (a : Fin m → B) (i : Fin m) :
    lane a (i / 3) (i % 3) = a i := by
  have h : 3 * ((i : ℕ) / 3) + (i : ℕ) % 3 = i := Nat.div_add_mod _ _
  unfold lane
  rw [dif_pos (by rw [h]; exact i.2)]
  congr 1
  exact Fin.ext h

theorem lane_intCast (a : Fin m → ℤ) (i' l : ℕ) :
    lane (fun i => ((a i : ℤ) : A)) i' l = ((lane a i' l : ℤ) : A) := by
  unfold lane
  split_ifs <;> simp

theorem pack_intCast (a : Fin m → ℤ) (i' : ℕ) :
    pack rad (fun i => ((a i : ℤ) : A)) i' = ((pack rad a i' : ℤ) : A) := by
  unfold pack
  simp only [lane_intCast]
  push_cast
  ring

theorem lane_sub (a b : Fin m → A) (i' l : ℕ) :
    lane (fun i => a i - b i) i' l = lane a i' l - lane b i' l := by
  unfold lane
  split_ifs <;> simp

theorem lane_mul_left (e : A) (a : Fin m → A) (i' l : ℕ) :
    lane (fun i => e * a i) i' l = e * lane a i' l := by
  unfold lane
  split_ifs <;> simp

theorem lane_sum {U : Type} (s : Finset U) (a : U → Fin m → A) (i' l : ℕ) :
    lane (fun i => ∑ u ∈ s, a u i) i' l = ∑ u ∈ s, lane (a u) i' l := by
  unfold lane
  split_ifs <;> simp

theorem pack_sub (a b : Fin m → A) (i' : ℕ) :
    pack rad (fun i => a i - b i) i' = pack rad a i' - pack rad b i' := by
  unfold pack
  simp only [lane_sub]
  ring

theorem pack_mul_left (e : A) (a : Fin m → A) (i' : ℕ) :
    pack rad (fun i => e * a i) i' = e * pack rad a i' := by
  unfold pack
  simp only [lane_mul_left]
  ring

theorem pack_sum {U : Type} (s : Finset U) (a : U → Fin m → A) (i' : ℕ) :
    pack rad (fun i => ∑ u ∈ s, a u i) i' = ∑ u ∈ s, pack rad (a u) i' := by
  unfold pack
  simp only [lane_sum, mul_sum, sum_add_distrib]

end Linear

/-! ## Step 1: small cells are unique -/

/-- An integer multiple of rad of absolute value below rad is 0. -/
theorem eq_zero_of_add_mul_eq_zero {rad d x : ℤ} (hd : |d| < rad) (h : d + rad * x = 0) : d = 0 :=
  Int.eq_zero_of_abs_lt_dvd (m := rad) ⟨-x, by linarith⟩ hd

/-- Step 1. Under `hrad`, `hp`: if three integers of absolute value at most 4 t - 2 satisfy d0 + rad
d1 + rad² d2 = 0 in a ring of characteristic p, then all three are 0. -/
theorem eq_zero_of_writes_zero {E : Type} [CommRing E] (p : ℕ) [CharP E p] {t rad : ℤ}
    (hrad : 4 * t - 1 ≤ rad) (hp : (4 * t - 2) * (1 + rad + rad ^ 2) < p) {d0 d1 d2 : ℤ}
    (h0 : |d0| ≤ 4 * t - 2) (h1 : |d1| ≤ 4 * t - 2) (h2 : |d2| ≤ 4 * t - 2)
    (h : ((d0 + rad * d1 + rad ^ 2 * d2 : ℤ) : E) = 0) : d0 = 0 ∧ d1 = 0 ∧ d2 = 0 := by
  have hr0 : 0 < rad := by have := abs_nonneg d0; linarith
  have hdvd := (CharP.intCast_eq_zero_iff E p _).1 h
  have hbound : |d0 + rad * d1 + rad ^ 2 * d2| < p := by
    have e1 : |rad * d1| = rad * |d1| := by rw [abs_mul, abs_of_pos hr0]
    have e2 : |rad ^ 2 * d2| = rad ^ 2 * |d2| := by rw [abs_mul, abs_of_pos (by positivity)]
    have b1 : rad * |d1| ≤ rad * (4 * t - 2) := mul_le_mul_of_nonneg_left h1 hr0.le
    have b2 : rad ^ 2 * |d2| ≤ rad ^ 2 * (4 * t - 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
    calc |d0 + rad * d1 + rad ^ 2 * d2| ≤ |d0| + |rad * d1| + |rad ^ 2 * d2| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (4 * t - 2) * (1 + rad + rad ^ 2) := by rw [e1, e2]; nlinarith
      _ < p := hp
  have hz : d0 + rad * d1 + rad ^ 2 * d2 = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hbound
  have e0 : d0 = 0 := eq_zero_of_add_mul_eq_zero (rad := rad) (x := d1 + rad * d2) (by linarith)
    (by rw [← hz]; ring)
  subst e0
  have hz' : d1 + rad * d2 = 0 := by
    have : rad * (d1 + rad * d2) = 0 := by rw [← hz]; ring
    exact (mul_eq_zero.1 this).resolve_left hr0.ne'
  have e1 : d1 = 0 := eq_zero_of_add_mul_eq_zero (rad := rad) (by linarith) hz'
  subst e1
  refine ⟨rfl, rfl, ?_⟩
  have : rad * d2 = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left hr0.ne'

/-- A column of integers is small if every entry has absolute value below 2 t. -/
def Small (t : ℤ) {m : ℕ} (a : Fin m → ℤ) : Prop := ∀ i, |a i| < 2 * t

/-- Step 1. Under `ht`, `hrad`, `hp`, `hs`: two small columns with the same packed elements in a
ring of characteristic p are equal. -/
theorem small_unique {E : Type} [CommRing E] (p : ℕ) [CharP E p] {t rad : ℤ} (ht : 0 < t)
    (hrad : 4 * t - 1 ≤ rad) (hp : (4 * t - 2) * (1 + rad + rad ^ 2) < p) {m s : ℕ}
    (hs : symRows m ≤ s) {a b : Fin m → ℤ} (ha : Small t a) (hb : Small t b)
    (h : ∀ i' : Fin s, ((pack rad a i' : ℤ) : E) = ((pack rad b i' : ℤ) : E)) : a = b := by
  have hl : ∀ i' l : ℕ, |lane a i' l - lane b i' l| ≤ 4 * t - 2 := by
    intro i' l
    unfold lane
    split_ifs with hi
    · have h1 := abs_lt.1 (ha ⟨_, hi⟩)
      have h2 := abs_lt.1 (hb ⟨_, hi⟩)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · simp only [sub_self, abs_zero]; linarith
  funext i
  have hi' : (i : ℕ) / 3 < s := by
    unfold symRows at hs
    have := i.2
    omega
  have hz := h ⟨(i : ℕ) / 3, hi'⟩
  rw [← sub_eq_zero, ← Int.cast_sub] at hz
  have hz' : ((lane a (i / 3) 0 - lane b (i / 3) 0 + rad * (lane a (i / 3) 1 - lane b (i / 3) 1)
      + rad ^ 2 * (lane a (i / 3) 2 - lane b (i / 3) 2) : ℤ) : E) = 0 := by
    rw [← hz]
    congr 1
    simp only [pack, Int.cast_id]
    ring
  obtain ⟨e0, e1, e2⟩ := eq_zero_of_writes_zero p hrad hp (hl _ 0) (hl _ 1) (hl _ 2) hz'
  have hlane : lane a (i / 3) (i % 3) = lane b (i / 3) (i % 3) := by
    have h3 : (i : ℕ) % 3 = 0 ∨ (i : ℕ) % 3 = 1 ∨ (i : ℕ) % 3 = 2 := by omega
    rcases h3 with h3 | h3 | h3 <;> rw [h3] <;> linarith
  rwa [lane_div_mod, lane_div_mod] at hlane

/-! ## Steps 2 and 3: one matrix -/

section OneMatrix

variable {E : Type} [CommRing E] {m s : ℕ} {C R : Type} (t rad : ℤ)

/-- A good column: there are small cells whose packing gives the column's packed elements and whose
weighted sums give its partial evaluations. sym holds the packed elements, tab the partial
evaluations, one for each read r, and w r the weights of read r on the m rows. -/
def GoodColumn (sym : Fin s → E) (w : R → Fin m → E) (tab : R → E) : Prop :=
  ∃ a : Fin m → ℤ,
    Small t a ∧ (∀ i', sym i' = ((pack rad a i' : ℤ) : E)) ∧ ∀ r, tab r = ∑ i, w r i * (a i : E)

variable [Fintype C]

/-- A combination can pass under the coefficients cf: there are integers z in the window [-t, t)
whose packing is, in every packed row, the combination of the packed elements, and whose weighted
sum is, for every read, the combination of the partial evaluations. -/
def CanPass (Sym : Fin s → C → E) (w : R → Fin m → E) (Tab : R → C → E) (cf : C → ℤ) : Prop :=
  ∃ z : Fin m → ℤ, (∀ i, -t ≤ z i ∧ z i < t) ∧
    (∀ i', ∑ c, (cf c : E) * Sym i' c = ((pack rad z i' : ℤ) : E)) ∧
    ∀ r, ∑ c, (cf c : E) * Tab r c = ∑ i, w r i * (z i : E)

variable [DecidableEq C]

theorem sum_update_cast_mul (cf : C → ℤ) (c₀ : C) (x : ℤ) (S : C → E) :
    ∑ c, ((Function.update cf c₀ x c : ℤ) : E) * S c =
      (x : E) * S c₀ + ∑ c ∈ univ.erase c₀, (cf c : E) * S c := by
  rw [← add_sum_erase _ _ (mem_univ c₀)]
  congr 1
  · simp
  · exact sum_congr rfl fun c hc => by rw [Function.update_of_ne (ne_of_mem_erase hc)]

variable {t rad}

/-- Step 2: one column, two coefficients. -/
theorem goodColumn_of_canPass_two {Sym : Fin s → C → E} {w : R → Fin m → E} {Tab : R → C → E}
    (cf : C → ℤ) (c₀ : C) {e : ℤ} (he : e = 1 ∨ e = -1)
    (h0 : CanPass t rad Sym w Tab (Function.update cf c₀ 0))
    (h1 : CanPass t rad Sym w Tab (Function.update cf c₀ e)) :
    GoodColumn t rad (fun i' => Sym i' c₀) w (fun r => Tab r c₀) := by
  obtain ⟨z, hz, hT, hR⟩ := h0
  obtain ⟨z', hz', hT', hR'⟩ := h1
  have hee : (e : E) * (e : E) = 1 := by rcases he with rfl | rfl <;> simp
  refine ⟨fun i => e * (z' i - z i), ?_, ?_, ?_⟩
  · intro i
    have h1 := hz i
    have h2 := hz' i
    rw [abs_lt]
    rcases he with rfl | rfl <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · intro i'
    have a0 := hT i'
    have a1 := hT' i'
    rw [sum_update_cast_mul] at a0 a1
    rw [Int.cast_zero, zero_mul, zero_add] at a0
    rw [pack_mul_left, pack_sub]
    push_cast
    rw [← a0, ← a1]
    linear_combination (-Sym i' c₀) * hee
  · intro r
    have a0 := hR r
    have a1 := hR' r
    rw [sum_update_cast_mul] at a0 a1
    rw [Int.cast_zero, zero_mul, zero_add] at a0
    have : ∑ i, w r i * ((e * (z' i - z i) : ℤ) : E) =
        (e : E) * (∑ i, w r i * (z' i : E) - ∑ i, w r i * (z i : E)) := by
      rw [← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun i _ => by push_cast; ring
    rw [this, ← a0, ← a1]
    linear_combination (-Tab r c₀) * hee

/-- Step 3, one matrix: if a column is not good, all |U| combinations can pass for at most the
fraction 2^(-|U|) of the arrays of coefficients. (Of the four elements of `Coef`, Prob/Window.lean,
two have the value 0, one +1 and one -1; `cnt`, Prob/Cnt.lean, counts the arrays.) -/
theorem cnt_canPass_mul_le {U : Type} [Fintype U] [DecidableEq U] (Sym : Fin s → C → E)
    (w : R → Fin m → E) (Tab : R → C → E) (c₀ : C)
    (hbad : ¬ GoodColumn t rad (fun i' => Sym i' c₀) w (fun r => Tab r c₀)) :
    cnt (fun Ξ : U → C → Coef => ∀ u, CanPass t rad Sym w Tab fun c => (Ξ u c).val) *
        2 ^ Fintype.card U ≤
      Fintype.card (U → C → Coef) :=
  cnt_forall_pass_mul_le (CanPass t rad Sym w Tab) c₀ fun cf _ he h0 h1 =>
    hbad (goodColumn_of_canPass_two cf c₀ he h0 h1)

end OneMatrix

/-! ## Step 3: several matrices -/

section Matrices

variable {E : Type} [CommRing E] {Mx U : Type} {m s : Mx → ℕ} {C R : Mx → Type}

/-- What is determined before the challenge Ξ, for all matrices μ: the packed elements, the weights
of the reads, the partial evaluations. -/
structure Fixed (E : Type) {Mx : Type} (m s : Mx → ℕ) (C R : Mx → Type) where
  Sym : ∀ μ, Fin (s μ) → C μ → E
  w : ∀ μ, R μ → Fin (m μ) → E
  Tab : ∀ μ, R μ → C μ → E

variable (t rad : ℤ)

/-- No matrix has a bad column. -/
def Fixed.Good (X : Fixed E m s C R) : Prop :=
  ∀ μ c, GoodColumn t rad (fun i' => X.Sym μ i' c) (X.w μ) (fun r => X.Tab μ r c)

/-- Every combination Ξ_μ u of every matrix μ can pass. -/
def Fixed.AllPass [∀ μ, Fintype (C μ)] (X : Fixed E m s C R) (Ξ : ∀ μ, U → C μ → Coef) : Prop :=
  ∀ μ u, CanPass t rad (X.Sym μ) (X.w μ) (X.Tab μ) fun c => (Ξ μ u c).val

variable {t rad}
variable [Fintype Mx] [DecidableEq Mx] [∀ μ, Fintype (C μ)] [∀ μ, DecidableEq (C μ)]
  [Fintype U] [DecidableEq U]

/-- Step 3: if some matrix has a bad column, all |U| combinations of all matrices can pass for at
most the fraction 2^(-|U|) of the tuples (Ξ_μ)_μ. -/
theorem cnt_allPass_mul_le (X : Fixed E m s C R) (hbad : ¬ X.Good t rad) :
    cnt (fun Ξ : ∀ μ, U → C μ → Coef => X.AllPass t rad Ξ) * 2 ^ Fintype.card U ≤
      Fintype.card (∀ μ, U → C μ → Coef) := by
  unfold Fixed.Good at hbad
  push Not at hbad
  obtain ⟨μ₀, c₀, hc⟩ := hbad
  have h1 := cnt_canPass_mul_le (U := U) (X.Sym μ₀) (X.w μ₀) (X.Tab μ₀) c₀ hc
  have h2 := cnt_pi_coord (A := fun μ => U → C μ → Coef) μ₀ fun ξ : U → C μ₀ → Coef =>
    ∀ u, CanPass t rad (X.Sym μ₀) (X.w μ₀) (X.Tab μ₀) fun c => (ξ u c).val
  have h3 : cnt (fun Ξ : ∀ μ, U → C μ → Coef => X.AllPass t rad Ξ) ≤
      cnt (fun Ξ : ∀ μ, U → C μ →
        Coef => ∀ u, CanPass t rad (X.Sym μ₀) (X.w μ₀) (X.Tab μ₀) fun c => (Ξ μ₀ u c).val) :=
    cnt_mono fun Ξ h => h μ₀
  have hpos : 0 < Fintype.card (U → C μ₀ → Coef) := Fintype.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc
    cnt (fun Ξ : ∀ μ, U → C μ → Coef => X.AllPass t rad Ξ) *
          2 ^ Fintype.card U * Fintype.card (U → C μ₀ → Coef) ≤
        cnt (fun Ξ : ∀ μ, U → C μ →
            Coef => ∀ u, CanPass t rad (X.Sym μ₀) (X.w μ₀) (X.Tab μ₀) fun c => (Ξ μ₀ u c).val) *
          2 ^ Fintype.card U * Fintype.card (U → C μ₀ → Coef) := by gcongr
    _ = cnt (fun ξ : U → C μ₀ → Coef =>
            ∀ u, CanPass t rad (X.Sym μ₀) (X.w μ₀) (X.Tab μ₀) fun c => (ξ u c).val) *
          2 ^ Fintype.card U * Fintype.card (∀ μ, U → C μ → Coef) := by
        rw [mul_right_comm, h2]; ring
    _ ≤ Fintype.card (U → C μ₀ → Coef) * Fintype.card (∀ μ, U → C μ → Coef) := by gcongr
    _ = Fintype.card (∀ μ, U → C μ → Coef) * Fintype.card (U → C μ₀ → Coef) := mul_comm _ _

/-- `cnt_allPass_mul_le` as a bound on the number of bad challenges. -/
theorem cnt_allPass_le (X : Fixed E m s C R) (hbad : ¬ X.Good t rad) :
    cnt (fun Ξ : ∀ μ, U → C μ → Coef => X.AllPass t rad Ξ) ≤
      Fintype.card (∀ μ, U → C μ → Coef) / 2 ^ Fintype.card U :=
  (Nat.le_div_iff_mul_le (by positivity)).2 (cnt_allPass_mul_le X hbad)

end Matrices

end Alg
