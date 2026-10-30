-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngPlan.lean: lookup plans; no protocol.

A lookup plan (`Plan`) lists the calls of a range reduction (Blocks/RngCalls.lean): the keys of call
f are affine functions of the columns of the matrix W, and its table is {0, .., 2^(d f) - 1}.
`Plan.Valid` says, among other things, that a given predicate WFp holds of W if and only if every
key that is not padding is in its table. `Plan.ofPairs` is the plan for signed bytes and two-byte
weights, valid by `Plan.ofPairs_valid` under the hypotheses stated there.

Choices made here.
 (1) In every call the low k coordinates of the key hypercube are the column coordinates.
 (2) No condition on the cost of the verifier is asked: no statement depends on it.
 (3) A signed byte is "the image of an integer in [-2^7, 2^7)". For p > 2^8 this says the same
     as "a lifts into [-2^7, 2^7)".
 (4) That the pairs of rows are those of a layout is not here: the pairs are a parameter.
Matrices are functions ℕ → ℕ → F, read on h rows and 2^k columns. Hypercube indices are numbers,
first coordinate = highest bit.

Terms: lean/GLOSSARY.md.
-/
import Blocks.Ext
import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace Blocks.Rng

open Finset

/-- A lookup plan. Call f has the table {0, .., 2^(d f) - 1}, offsets off f and the matrix Γ f. -/
structure Plan (F : Type) where
  /-- the matrix W has h rows and 2^k columns -/
  h : ℕ
  k : ℕ
  /-- number of calls -/
  nc : ℕ
  /-- the key hypercube has D coordinates, the last B of which are the class -/
  D : ℕ
  B : ℕ
  /-- a multiplicity has 2^lp bits -/
  lp : ℕ
  d : ℕ → ℕ
  off : ℕ → ℕ → F
  Γ : ℕ → ℕ → ℕ → F

/-- a is in the table {0, .., 2^d - 1}. -/
def InTab {F : Type} [NatCast F] (d : ℕ) (a : F) : Prop := ∃ t : ℕ, t < 2 ^ d ∧ a = (t : F)

namespace Plan

variable {F : Type} [Field F] (P : Plan F)

/-- The keys of call f: the key number i = i_row 2^k + i_col. -/
def key (f : ℕ) (W : ℕ → ℕ → F) (i : ℕ) : F :=
  P.off f (i / 2 ^ P.k) + ∑ y ∈ range P.h, P.Γ f (i / 2 ^ P.k) y * W y (i % 2 ^ P.k)

/-- The keys of the row part i' of call f are padding. -/
def IsPad (f i' : ℕ) : Prop := P.off f i' = 0 ∧ ∀ y, y < P.h → P.Γ f i' y = 0

theorem key_of_isPad {f i : ℕ} (h : P.IsPad f (i / 2 ^ P.k)) (W : ℕ → ℕ → F) : P.key f W i = 0 := by
  unfold key
  rw [h.1, zero_add]
  exact sum_eq_zero fun y hy => by rw [h.2 y (mem_range.mp hy), zero_mul]

/-- Every key of every call that is not padding is in its table. -/
def KeysOK (W : ℕ → ℕ → F) : Prop :=
  ∀ f, f < P.nc → ∀ i, i < 2 ^ P.D → ¬ P.IsPad f (i / 2 ^ P.k) → InTab (P.d f) (P.key f W i)

/-- Every key of every call is in its table. -/
def KeysAll (W : ℕ → ℕ → F) : Prop := ∀ f, f < P.nc → ∀ i, i < 2 ^ P.D → InTab (P.d f) (P.key f W i)

/-- A padding key is 0, which is in every table. -/
theorem keysOK_iff_keysAll (W : ℕ → ℕ → F) : P.KeysOK W ↔ P.KeysAll W := by
  constructor
  · intro h f hf i hi
    by_cases hp : P.IsPad f (i / 2 ^ P.k)
    · exact ⟨0, by positivity, by rw [P.key_of_isPad hp, Nat.cast_zero]⟩
    · exact h f hf i hi hp
  · intro h f hf i hi _
    exact h f hf i hi

/-- A valid plan ((Pl1) and (Pl2) are its fields pl1 and pl2, pl2'), for the predicate WFp on
matrices and the characteristic p. -/
structure Valid (p : ℕ) (WFp : (ℕ → ℕ → F) → Prop) : Prop where
  k_le : P.k ≤ P.D
  B_le : P.B ≤ P.D
  nc_pos : 0 < P.nc
  pl1 : ∀ W, WFp W ↔ P.KeysOK W
  pl2 : ∀ f, f < P.nc → 2 ^ (P.d f + 2 ^ P.lp) ≤ p
  pl2' : 2 ^ (P.D - P.B) < 2 ^ 2 ^ P.lp

/-! ## The extension of the keys of a call -/

variable {E : Type} [Field E] [Algebra F E]

/-- ~o_f at the row part of a point (its first D - k coordinates). -/
def offExt (f : ℕ) (a : ℕ → E) : E := ext (P.D - P.k) (fun i' => algebraMap F E (P.off f i')) a

/-- g_f(a) = ∑_i' eq(a, i') Γ_f[i']. -/
def gOf (f : ℕ) (a : ℕ → E) (y : ℕ) : E := ext (P.D - P.k) (fun i' => algebraMap F E (P.Γ f i' y)) a

/-- Under `hk`, the extension of the keys of call f: ~key_f(W)(ϱ) = ~o_f(ϱ_row) + ⟨g_f(ϱ_row) ⊗
eq(ϱ_col, ·), W⟩. The row part of ϱ are its first D - k coordinates. -/
theorem ext_key (hk : P.k ≤ P.D) (f : ℕ) (W : ℕ → ℕ → F) (ϱ : ℕ → E) :
    ext P.D (fun i => algebraMap F E (P.key f W i)) ϱ =
        P.offExt f ϱ +
          ∑ y ∈ range P.h, ∑ c ∈ range (2 ^ P.k),
            P.gOf f ϱ y * eqN P.k (P.D - P.k) ϱ c * algebraMap F E (W y c) := by
  have hpos : 0 < 2 ^ P.k := by positivity
  have hD : 2 ^ P.D = 2 ^ (P.D - P.k) * 2 ^ P.k := by rw [← pow_add, Nat.sub_add_cancel hk]
  have hone : ∑ c ∈ range (2 ^ P.k), eqN P.k (P.D - P.k) ϱ c = 1 := by
    simp only [eqN_eq]
    exact Alg.sum_eqN _
  have hterm : ∀ i', ∀ c ∈ range (2 ^ P.k), eqN P.D 0 ϱ (i' * 2 ^ P.k + c) *
        algebraMap F E (P.key f W (i' * 2 ^ P.k + c)) =
      eqN (P.D - P.k) 0 ϱ i' * algebraMap F E (P.off f i') * eqN P.k (P.D - P.k) ϱ c +
        ∑ y ∈ range P.h, eqN (P.D - P.k) 0 ϱ i' * algebraMap F E (P.Γ f i' y) *
          (eqN P.k (P.D - P.k) ϱ c * algebraMap F E (W y c)) := by
    intro i' c hc
    have hc' := mem_range.mp hc
    have h1 : (i' * 2 ^ P.k + c) / 2 ^ P.k = i' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hc', Nat.zero_add]
    have h2 : (i' * 2 ^ P.k + c) % 2 ^ P.k = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc']
    have h3 := eqN_append' (P.D - P.k) P.k 0 ϱ i' hc'
    rw [Nat.sub_add_cancel hk, Nat.zero_add] at h3
    unfold key
    rw [h1, h2, h3, map_add, map_sum, mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun y _ => by rw [map_mul]; ring
  unfold ext offExt gOf
  unfold ext
  rw [hD, Alg.sum_range_mul_add]
  simp only [sum_congr rfl (hterm _), sum_add_distrib, ← mul_sum, hone, mul_one]
  congr 1
  rw [sum_congr rfl fun x _ => sum_comm, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_mul, sum_mul]
  exact sum_congr rfl fun i' _ => by ring

end Plan

/-! ## Signed bytes and two-byte weights -/

section Bytes

variable {F : Type} [Field F]

/-- a is the image of an integer in [-2^7, 2^7). -/
def IsByte (a : F) : Prop := ∃ z : ℤ, -128 ≤ z ∧ z < 128 ∧ a = (z : F)

/-- a₀, a₁ are the images of signed bytes z₀, z₁ with z₀ + 2^8 z₁ in [-2^12, 2^12). -/
def IsPair (a₀ a₁ : F) : Prop :=
  ∃ z₀ z₁ : ℤ, (-128 ≤ z₀ ∧ z₀ < 128 ∧ a₀ = (z₀ : F)) ∧ (-128 ≤ z₁ ∧ z₁ < 128 ∧ a₁ = (z₁ : F)) ∧
    -4096 ≤ z₀ + 256 * z₁ ∧ z₀ + 256 * z₁ < 4096

/-- 2^7 + a is in {0, .., 2^8 - 1} if and only if a is a signed byte. -/
theorem inTab_byte_iff (a : F) : InTab 8 (128 + a) ↔ IsByte a := by
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨(t : ℤ) - 128, by omega, by norm_num at ht; omega, ?_⟩
    push_cast
    rw [← h]
    ring
  · rintro ⟨z, h1, h2, rfl⟩
    refine ⟨(128 + z).toNat, by norm_num; omega, ?_⟩
    have h3 : (((128 + z).toNat : ℤ) : F) = ((128 + z : ℤ) : F) := by
      rw [Int.toNat_of_nonneg (by omega)]
    rw [Int.cast_natCast] at h3
    rw [h3]
    push_cast
    rfl

/-- For signed bytes a₀, a₁ and characteristic p > 2^17: 2^12 + a₀ + 2^8 a₁ is in {0, .., 2^13 - 1}
if and only if the two-byte weight is in range. -/
theorem inTab_pair_iff (p : ℕ) [CharP F p] (hp : 2 ^ 17 < p) {a₀ a₁ : F}
    (h₀ : IsByte a₀) (h₁ : IsByte a₁) :
    InTab 13 (4096 + a₀ + 256 * a₁) ↔ IsPair a₀ a₁ := by
  obtain ⟨z₀, l₀, u₀, rfl⟩ := h₀
  obtain ⟨z₁, l₁, u₁, rfl⟩ := h₁
  constructor
  · rintro ⟨t, ht, h⟩
    have ht' : t < 8192 := by norm_num at ht; exact ht
    have hz : ((4096 + z₀ + 256 * z₁ - (t : ℤ) : ℤ) : F) = 0 := by
      push_cast
      rw [h]
      ring
    have hdvd := (CharP.intCast_eq_zero_iff F p _).mp hz
    have hp' : (131072 : ℤ) < (p : ℤ) := by
      have : (2 : ℕ) ^ 17 = 131072 := by norm_num
      rw [this] at hp
      exact_mod_cast hp
    have h0 : 4096 + z₀ + 256 * z₁ - (t : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      rw [abs_lt]
      constructor <;> omega
    exact ⟨z₀, z₁, ⟨l₀, u₀, rfl⟩, ⟨l₁, u₁, rfl⟩, by omega, by omega⟩
  · rintro ⟨w₀, w₁, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, c1, c2⟩
    refine ⟨(4096 + w₀ + 256 * w₁).toNat, by norm_num; omega, ?_⟩
    have h3 : (((4096 + w₀ + 256 * w₁).toNat : ℤ) : F) = ((4096 + w₀ + 256 * w₁ : ℤ) : F) := by
      rw [Int.toNat_of_nonneg (by omega)]
    rw [Int.cast_natCast] at h3
    rw [h3, a3, b3]
    push_cast
    rfl

end Bytes

/-! ## The plan with keys of two kinds -/

section OfPairs

variable (F : Type) [Field F] (h k D B lp m2 : ℕ) (y0 y1 : ℕ → ℕ)

/-- number of calls for n rows of keys, R = 2^(D - k) rows in a call -/
def nCalls (D k n : ℕ) : ℕ := (n + 2 ^ (D - k) - 1) / 2 ^ (D - k)

theorem le_nCalls_mul (D k n : ℕ) : n ≤ nCalls D k n * 2 ^ (D - k) := by
  unfold nCalls
  have hpos : 0 < 2 ^ (D - k) := by positivity
  have e := Nat.div_add_mod (n + 2 ^ (D - k) - 1) (2 ^ (D - k))
  have m := Nat.mod_lt (n + 2 ^ (D - k) - 1) hpos
  rw [Nat.mul_comm] at e
  omega

/-- The plan with keys of two kinds, with the pairs of rows (y0 q, y1 q), q < m2, as a parameter.
The calls f < nCalls D k h are of the first kind (a key 2^7 + W[y][c] for every entry), the others
of the second kind (a key 2^12 + W[y0 q][c] + 2^8 W[y1 q][c] for every pair and every column). -/
def Plan.ofPairs : Plan F where
  h := h
  k := k
  nc := nCalls D k h + nCalls D k m2
  D := D
  B := B
  lp := lp
  d := fun f => if f < nCalls D k h then 8 else 13
  off := fun f i' =>
    if f < nCalls D k h then (if f * 2 ^ (D - k) + i' < h then 128 else 0)
    else (if (f - nCalls D k h) * 2 ^ (D - k) + i' < m2 then 4096 else 0)
  Γ := fun f i' y =>
    if f < nCalls D k h then
      (if f * 2 ^ (D - k) + i' < h then (if y = f * 2 ^ (D - k) + i' then 1 else 0) else 0)
    else (if (f - nCalls D k h) * 2 ^ (D - k) + i' < m2 then
      (if y = y0 ((f - nCalls D k h) * 2 ^ (D - k) + i') then 1 else 0) +
        (if y = y1 ((f - nCalls D k h) * 2 ^ (D - k) + i') then 256 else 0)
      else 0)

/-- Well-formed: all entries are signed bytes, and in every column of every pair of rows the
two-byte weight is in range. -/
def WFPairs {F : Type} [Field F] (h k m2 : ℕ) (y0 y1 : ℕ → ℕ) (W : ℕ → ℕ → F) : Prop :=
  (∀ y, y < h → ∀ c, c < 2 ^ k → IsByte (W y c)) ∧
  ∀ q, q < m2 → ∀ c, c < 2 ^ k → IsPair (W (y0 q) c) (W (y1 q) c)

variable {F h k D B lp m2 y0 y1}

theorem sum_ite_eq_mul {n y : ℕ} (hy : y < n) (a : F) (g : ℕ → F) :
    ∑ y' ∈ range n, (if y' = y then a else 0) * g y' = a * g y := by
  rw [sum_eq_single y]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro hn
    exact absurd (mem_range.mpr hy) hn

theorem key_first {f i : ℕ} (hf : f < nCalls D k h)
    (hy : f * 2 ^ (D - k) + i / 2 ^ k < h) (W : ℕ → ℕ → F) :
    (Plan.ofPairs F h k D B lp m2 y0 y1).key f W i =
      128 + W (f * 2 ^ (D - k) + i / 2 ^ k) (i % 2 ^ k) := by
  show (if f < nCalls D k h then (if f * 2 ^ (D - k) + i / 2 ^ k < h then (128 : F) else 0)
        else _) +
      ∑ y ∈ range h,
        (if f < nCalls D k h then
              (if f * 2 ^ (D - k) + i / 2 ^ k < h then
                  (if y = f * 2 ^ (D - k) + i / 2 ^ k then (1 : F) else 0)
                else 0)
            else _) *
          W y (i % 2 ^ k) = _
  simp only [if_pos hf, if_pos hy]
  rw [sum_ite_eq_mul hy, one_mul]

theorem isPad_first {f i' : ℕ} (hf : f < nCalls D k h) (hy : ¬ f * 2 ^ (D - k) + i' < h) :
    (Plan.ofPairs F h k D B lp m2 y0 y1).IsPad f i' := by
  constructor
  · show (if f < nCalls D k h then (if f * 2 ^ (D - k) + i' < h then (128 : F) else 0) else _) = 0
    rw [if_pos hf, if_neg hy]
  · intro y _
    show (if f < nCalls D k h then
          (if f * 2 ^ (D - k) + i' < h then (if y = f * 2 ^ (D - k) + i' then (1 : F) else 0)
            else 0)
        else _) = 0
    rw [if_pos hf, if_neg hy]

theorem key_second {f i : ℕ} (hf : ¬ f < nCalls D k h)
    (hq : (f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k < m2)
    (h0 : y0 ((f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k) < h)
    (h1 : y1 ((f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k) < h) (W : ℕ → ℕ → F) :
    (Plan.ofPairs F h k D B lp m2 y0 y1).key f W i =
      4096 + W (y0 ((f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k)) (i % 2 ^ k) +
        256 * W (y1 ((f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k)) (i % 2 ^ k) := by
  show (if f < nCalls D k h then _
        else (if (f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k < m2 then (4096 : F) else 0)) +
      ∑ y ∈ range h,
        (if f < nCalls D k h then _
            else
              (if (f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k < m2 then
                  (if y = y0 ((f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k) then (1 : F) else 0) +
                    (if y = y1 ((f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k) then 256 else 0)
                else 0)) *
          W y (i % 2 ^ k) = _
  simp only [if_neg hf, if_pos hq, add_mul, sum_add_distrib]
  rw [sum_ite_eq_mul h0, sum_ite_eq_mul h1, one_mul, add_assoc]

theorem isPad_second {f i' : ℕ} (hf : ¬ f < nCalls D k h)
    (hq : ¬ (f - nCalls D k h) * 2 ^ (D - k) + i' < m2) :
    (Plan.ofPairs F h k D B lp m2 y0 y1).IsPad f i' := by
  constructor
  · show (if f < nCalls D k h then _
        else (if (f - nCalls D k h) * 2 ^ (D - k) + i' < m2 then (4096 : F) else 0)) = 0
    rw [if_neg hf, if_neg hq]
  · intro y _
    show (if f < nCalls D k h then _ else (if (f - nCalls D k h) * 2 ^ (D - k) + i' < m2 then
      (if y = y0 ((f - nCalls D k h) * 2 ^ (D - k) + i') then (1 : F) else 0)
        + (if y = y1 ((f - nCalls D k h) * 2 ^ (D - k) + i') then 256 else 0) else 0)) = 0
    rw [if_neg hf, if_neg hq]

theorem natCast_ne_zero_of_lt_char (p : ℕ) [CharP F p] {n : ℕ} (h0 : 0 < n) (hn : n < p) :
    (n : F) ≠ 0 := by
  intro h
  exact absurd (Nat.le_of_dvd h0 ((CharP.cast_eq_zero_iff F p n).mp h)) (by omega)

/-- facts on the key number i' 2^k + c, under `hk`, `hi`, `hc` -/
theorem idx_facts {i' c : ℕ} (hk : k ≤ D) (hi : i' < 2 ^ (D - k)) (hc : c < 2 ^ k) :
    i' * 2 ^ k + c < 2 ^ D ∧ (i' * 2 ^ k + c) / 2 ^ k = i' ∧ (i' * 2 ^ k + c) % 2 ^ k = c := by
  have hpos : 0 < 2 ^ k := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have hD : 2 ^ D = 2 ^ (D - k) * 2 ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
    calc i' * 2 ^ k + c < i' * 2 ^ k + 2 ^ k := by omega
      _ = (i' + 1) * 2 ^ k := by ring
      _ ≤ 2 ^ (D - k) * 2 ^ k := Nat.mul_le_mul_right _ hi
      _ = 2 ^ D := hD.symm
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-- (Pl1) for the plan with keys of two kinds, under the hypotheses below. -/
theorem Plan.ofPairs_pl1 (p : ℕ) [CharP F p] (hp : 2 ^ 17 < p) (hk : k ≤ D)
    (h0 : ∀ q, q < m2 → y0 q < h) (h1 : ∀ q, q < m2 → y1 q < h) (W : ℕ → ℕ → F) :
    WFPairs h k m2 y0 y1 W ↔ (Plan.ofPairs F h k D B lp m2 y0 y1).KeysOK W := by
  have hR : 0 < 2 ^ (D - k) := by positivity
  have hkpos : 0 < 2 ^ k := by positivity
  have hp' : 131072 < p := by
    have : (2 : ℕ) ^ 17 = 131072 := by norm_num
    omega
  constructor
  · rintro ⟨hb, hpr⟩ f _ i _ hnp
    have hc : i % 2 ^ k < 2 ^ k := Nat.mod_lt _ hkpos
    by_cases hf : f < nCalls D k h
    · by_cases hy : f * 2 ^ (D - k) + i / 2 ^ k < h
      · rw [key_first hf hy]
        show InTab (if f < nCalls D k h then 8 else 13) _
        rw [if_pos hf]
        exact (inTab_byte_iff _).2 (hb _ hy _ hc)
      · exact absurd (isPad_first hf hy) hnp
    · by_cases hq : (f - nCalls D k h) * 2 ^ (D - k) + i / 2 ^ k < m2
      · rw [key_second hf hq (h0 _ hq) (h1 _ hq)]
        show InTab (if f < nCalls D k h then 8 else 13) _
        rw [if_neg hf]
        exact (inTab_pair_iff p hp (hb _ (h0 _ hq) _ hc) (hb _ (h1 _ hq) _ hc)).2 (hpr _ hq _ hc)
      · exact absurd (isPad_second hf hq) hnp
  · intro hK
    have hb : ∀ y, y < h → ∀ c, c < 2 ^ k → IsByte (W y c) := by
      intro y hy c hc
      obtain ⟨e1, e2, e3⟩ := idx_facts hk (Nat.mod_lt y hR) hc
      have ey : y / 2 ^ (D - k) * 2 ^ (D - k) + y % 2 ^ (D - k) = y := Nat.div_add_mod' y _
      have hf : y / 2 ^ (D - k) < nCalls D k h :=
        (Nat.div_lt_iff_lt_mul hR).2 (lt_of_lt_of_le hy (le_nCalls_mul D k h))
      have hy' : y / 2 ^ (D - k) * 2 ^ (D - k) + (y % 2 ^ (D - k) * 2 ^ k + c) / 2 ^ k < h := by
        rw [e2, ey]; exact hy
      have hnp : ¬ (Plan.ofPairs F h k D B lp m2 y0 y1).IsPad
          (y / 2 ^ (D - k)) ((y % 2 ^ (D - k) * 2 ^ k + c) / 2 ^ k) := by
        intro hpad
        have h2 : (if y / 2 ^ (D - k) < nCalls D k h then
                (if y / 2 ^ (D - k) * 2 ^ (D - k) + (y % 2 ^ (D - k) * 2 ^ k + c) / 2 ^ k < h then
                    (128 : F)
                  else 0)
              else _) = 0 := hpad.1
        rw [if_pos hf, if_pos hy'] at h2
        exact natCast_ne_zero_of_lt_char
          (F := F) p (n := 128) (by norm_num) (by omega) (by exact_mod_cast h2)
      have h3 := hK (y / 2 ^ (D - k)) (Nat.lt_add_right _ hf) _ e1 hnp
      rw [key_first hf hy', e2, e3, ey] at h3
      have h4 : InTab (if y / 2 ^ (D - k) < nCalls D k h then 8 else 13) (128 + W y c) := h3
      rw [if_pos hf] at h4
      exact (inTab_byte_iff _).1 h4
    refine ⟨hb, ?_⟩
    intro q hq c hc
    obtain ⟨e1, e2, e3⟩ := idx_facts hk (Nat.mod_lt q hR) hc
    have eq' : q / 2 ^ (D - k) * 2 ^ (D - k) + q % 2 ^ (D - k) = q := Nat.div_add_mod' q _
    have hf2 : q / 2 ^ (D - k) < nCalls D k m2 :=
      (Nat.div_lt_iff_lt_mul hR).2 (lt_of_lt_of_le hq (le_nCalls_mul D k m2))
    have hf : ¬ nCalls D k h + q / 2 ^ (D - k) < nCalls D k h := Nat.not_lt.2 (Nat.le_add_right _ _)
    have es : nCalls D k h + q / 2 ^ (D - k) - nCalls D k h = q / 2 ^ (D - k) :=
      Nat.add_sub_cancel_left _ _
    have hq' : (nCalls D k h + q / 2 ^ (D - k) - nCalls D k h) * 2 ^ (D - k) +
          (q % 2 ^ (D - k) * 2 ^ k + c) / 2 ^ k = q := by
      rw [es, e2, eq']
    have hnp : ¬ (Plan.ofPairs F h k D B lp m2 y0 y1).IsPad
        (nCalls D k h + q / 2 ^ (D - k)) ((q % 2 ^ (D - k) * 2 ^ k + c) / 2 ^ k) := by
      intro hpad
      have h2 : (if nCalls D k h + q / 2 ^ (D - k) < nCalls D k h then _
            else
              (if (nCalls D k h + q / 2 ^ (D - k) - nCalls D k h) * 2 ^ (D - k) +
                      (q % 2 ^ (D - k) * 2 ^ k + c) / 2 ^ k < m2 then (4096 : F)
                else 0)) = 0 := hpad.1
      rw [if_neg hf, hq', if_pos hq] at h2
      exact natCast_ne_zero_of_lt_char
        (F := F) p (n := 4096) (by norm_num) (by omega) (by exact_mod_cast h2)
    have h3 := hK (nCalls D k h + q / 2 ^ (D - k)) (Nat.add_lt_add_left hf2 _) _ e1 hnp
    rw [key_second hf (by rw [hq']; exact hq)
          (by rw [hq']; exact h0 q hq) (by rw [hq']; exact h1 q hq),
      hq', e3] at h3
    have h4 : InTab (if nCalls D k h + q / 2 ^ (D - k) < nCalls D k h then 8 else 13)
        (4096 + W (y0 q) c + 256 * W (y1 q) c) := h3
    rw [if_neg hf] at h4
    exact (inTab_pair_iff p hp (hb _ (h0 q hq) c hc) (hb _ (h1 q hq) c hc)).1 h4

/-- The plan with keys of two kinds is valid, under the hypotheses below. -/
theorem Plan.ofPairs_valid (p : ℕ) [CharP F p] (hp : 2 ^ 17 < p) (hk : k ≤ D) (hB : B ≤ D)
    (hh : 0 < h) (hpl : 2 ^ (13 + 2 ^ lp) ≤ p) (hm : 2 ^ (D - B) < 2 ^ 2 ^ lp)
    (h0 : ∀ q, q < m2 → y0 q < h) (h1 : ∀ q, q < m2 → y1 q < h) :
    (Plan.ofPairs F h k D B lp m2 y0 y1).Valid p (WFPairs h k m2 y0 y1) where
  k_le := hk
  B_le := hB
  nc_pos := by
    have h2 := le_nCalls_mul D k h
    have h3 : 0 < nCalls D k h := by
      rcases Nat.eq_zero_or_pos (nCalls D k h) with h4 | h4
      · rw [h4, Nat.zero_mul] at h2
        omega
      · exact h4
    exact Nat.add_pos_left h3 _
  pl1 := Plan.ofPairs_pl1 p hp hk h0 h1
  pl2 := fun f _ => by
    refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hpl
    show (if f < nCalls D k h then 8 else 13) + 2 ^ lp ≤ 13 + 2 ^ lp
    split_ifs <;> omega
  pl2' := hm

end OfPairs

end Blocks.Rng
