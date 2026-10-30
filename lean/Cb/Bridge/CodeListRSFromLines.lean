-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Bridge/CodeListRSFromLines.lean: the statement on agreement of Reed-Solomon codes below the
Johnson radius (`Cb.BCHKS46`, Cb/Gen/CodeListRS.lean; `Cb.BCHKS46At`, Cb/Gen/CodeListRSAt.lean)
follows from one fact on lines, stated in Mathlib's terms.

This file needs Mathlib and the two files named above. It proves nothing on codes by itself:
`LineFact` is a definition of a proposition. Cb/Bridge/CodeListRSProved.lean proves it from two
theorems of ArkLib's, in the files under ThirdParty/, adapted from ArkLib and Mathlib
(lean/LIMITS.md, L15).

Main names: `LineFact`, the fact on lines;
  `bchks46_of_lineFact : LineFact → Cb.BCHKS46`
  `bchks46At_of_wide : Cb.BCHKS46 → Cb.BCHKS46At F E`

How `LineFact` is applied: same field, same evaluation points, degree bound D := k (both sides speak
of polynomials of degree at most k), agreement threshold A := n - e, and slack above the Johnson
fraction eta := 1 - sqrt(k/n) - e/n (`etaOf`).

The definition `est` writes out the value of ArkLib's `johnsonComparisonEstimate`
(ThirdParty/ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/Johnson/FiniteBounds.lean).
Cb/Bridge/CodeListRSProved.lean proves that the two are equal.

This file and Cb/Bridge/CodeListRSProved.lean do not count as written independently of a file of
ArkLib that is not in ThirdParty/ArkLib:
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean
(https://github.com/Verified-zkEVM/ArkLib, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13,
Copyright ArkLib Contributors, Apache-2.0). What is alike: with that file, the division into two
files; with two further files of ArkLib, the form of `LineFact` and the steps of the proof of
`bchks46_of_lineFact`. The last two rows of ThirdParty/TAKEN-OVER.tsv tell what this file and
Cb/Bridge/CodeListRSProved.lean take over from ArkLib, and from which files.
-/
import Cb.Gen.CodeListRSAt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
noncomputable section

set_option autoImplicit false

namespace Cb.Bridge
open Prob Polynomial

/-! ## The fact taken from ArkLib, stated in Mathlib's terms -/

/-- The multiplicity that appears in the count: max (ceil (sqrt(D/n) / eta)) 3, as a natural
number. -/
def estM (n D : ℕ) (eta : ℝ) : ℕ := max ⌈Real.sqrt ((D : ℝ) / n) / eta⌉₊ 3

/-- The bound on the number of exceptional values, for length n, degree bound D and slack eta. -/
def est (n D : ℕ) (eta : ℝ) : ℝ :=
  ((2 * ((estM n D eta : ℝ) + 1 / 2) ^ 5 +
      3 * ((estM n D eta : ℝ) + 1 / 2) * (1 - (Real.sqrt ((D : ℝ) / n) + eta)) * ((D : ℝ) / n)) /
      (3 * Real.sqrt ((D : ℝ) / n) ^ 3)) * n +
    ((estM n D eta : ℝ) + 1 / 2) / Real.sqrt ((D : ℝ) / n)

/-- **The fact on lines.** Take any field, n distinct points, two words f and g, a degree bound D
with 1 ≤ D ≤ n - 2, a slack eta > 0 with sqrt(D/n) + eta ≤ 1, and a threshold A with
(sqrt(D/n) + eta) n ≤ A ≤ n. Then at most `est n D eta` field elements can be excluded, once and for
all z (the set `excl`), so that for every other z: if a polynomial of degree at most D equals
f + z g on a set S of at least A positions, then two polynomials of degree at most D equal f and g
on S. (The premise sqrt(D/n) + eta ≤ 1 follows from the others. It is listed because ArkLib's
theorem on the bound asks for it.) -/
def LineFact : Prop :=
  ∀ (K : Type) [Field K] (n D A : ℕ) (eta : ℝ) (x : Fin n → K), Function.Injective x →
    ∀ f g : Fin n → K, 1 ≤ D → D ≤ n - 2 → 0 < eta → Real.sqrt ((D : ℝ) / n) + eta ≤ 1 →
      (Real.sqrt ((D : ℝ) / n) + eta) * n ≤ A → A ≤ n →
      ∃ excl : Finset K, (excl.card : ℝ) ≤ est n D eta ∧
        ∀ z, z ∉ excl → ∀ P : K[X], P.degree < ((D + 1 : ℕ) : WithBot ℕ) →
          ∀ S : Finset (Fin n), A ≤ S.card → (∀ j ∈ S, P.eval (x j) = f j + z * g j) →
            ∃ P₀ P₁ : K[X], P₀.degree < ((D + 1 : ℕ) : WithBot ℕ) ∧
              P₁.degree < ((D + 1 : ℕ) : WithBot ℕ) ∧
              ∀ j ∈ S, P₀.eval (x j) = f j ∧ P₁.eval (x j) = g j

/-! ## Arithmetic -/

/-- The slack above the Johnson agreement fraction at the radius e / n. -/
def etaOf (n k e : ℕ) : ℝ := 1 - Real.sqrt ((k : ℝ) / n) - (e : ℝ) / n

/-- The premises of `BCHKS46` use truncated subtraction on natural numbers. They still give e < n,
k ≤ n - 2 and 2 ≤ n, so neither n - e nor n - 2 is truncated. -/
theorem side {n k e : ℕ} (he : 0 < e) (h : n * k < (n - e) ^ 2) : e < n ∧ k ≤ n - 2 ∧ 2 ≤ n := by
  have hen : e < n := by
    by_contra hc
    have h0 : n - e = 0 := by omega
    rw [h0] at h
    simp at h
  refine ⟨hen, ?_, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : (m + 2 - e) ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (m + 2) * k < (m + 1) ^ 2 := lt_of_lt_of_le h h1
  by_contra hc
  have hk' : m + 1 ≤ k := by omega
  have h3 : (m + 2) * (m + 1) ≤ (m + 2) * k := Nat.mul_le_mul_left (m + 2) hk'
  nlinarith [h2, h3]

/-- The premise n k < (n - e)^2 makes the slack positive. -/
theorem eta_pos {n k e : ℕ} (hen : e < n) (h : n * k < (n - e) ^ 2) : 0 < etaOf n k e := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n - e : ℕ) : ℝ) = (n : ℝ) - e := Nat.cast_sub hen.le
  have hR : (n : ℝ) * k < ((n : ℝ) - e) ^ 2 := by
    have h' : ((n * k : ℕ) : ℝ) < (((n - e) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_pow, hcast] at h'
    exact h'
  have hpos : 0 < 1 - (e : ℝ) / n := by
    rw [sub_pos, div_lt_one hn]; exact_mod_cast hen
  have hs : Real.sqrt ((k : ℝ) / n) < 1 - (e : ℝ) / n := by
    rw [Real.sqrt_lt' hpos, div_lt_iff₀ hn]
    have hid : (1 - (e : ℝ) / n) ^ 2 * n = ((n : ℝ) - e) ^ 2 / n := by field_simp
    rw [hid, lt_div_iff₀ hn]
    linarith [hR]
  unfold etaOf; linarith

/-- At this slack the agreement fraction is 1 - e/n. -/
theorem agreement_eq (n k e : ℕ) :
    Real.sqrt ((k : ℝ) / n) + etaOf n k e = 1 - (e : ℝ) / n := by
  unfold etaOf; ring

/-- At this slack the agreement threshold is n - e. -/
theorem threshold {n k e : ℕ} (hen : e < n) :
    (Real.sqrt ((k : ℝ) / n) + etaOf n k e) * n ≤ ((n - e : ℕ) : ℝ) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [agreement_eq, Nat.cast_sub hen.le]
  apply le_of_eq; field_simp

/-- At this slack the agreement fraction is at most 1. -/
theorem agreement_le_one (n k e : ℕ) : Real.sqrt ((k : ℝ) / n) + etaOf n k e ≤ 1 := by
  rw [agreement_eq]
  have : (0 : ℝ) ≤ (e : ℝ) / n := by positivity
  linarith

/-- The multiplicity equals `bchksM`: the natural-number ceiling and the integer ceiling agree on a
nonnegative number. -/
theorem estM_eq {n k e : ℕ} (heta : 0 < etaOf n k e) :
    ((estM n k (etaOf n k e) : ℕ) : ℝ) = bchksM n k e := by
  have h0 : 0 ≤ Real.sqrt ((k : ℝ) / n) / etaOf n k e := div_nonneg (Real.sqrt_nonneg _) heta.le
  have hceil : ((⌈Real.sqrt ((k : ℝ) / n) / etaOf n k e⌉₊ : ℕ) : ℝ) =
      ((⌈Real.sqrt ((k : ℝ) / n) / etaOf n k e⌉ : ℤ) : ℝ) :=
    natCast_ceil_eq_intCast_ceil h0
  unfold estM bchksM
  rw [Nat.cast_max, hceil, Nat.cast_ofNat]
  rfl

/-- At this slack the bound `est` equals `bchksBound`. -/
theorem est_eq_bchks {n k e : ℕ} (heta : 0 < etaOf n k e) :
    est n k (etaOf n k e) = bchksBound n k e := by
  have hg : 1 - (Real.sqrt ((k : ℝ) / n) + etaOf n k e) = (e : ℝ) / n := by
    rw [agreement_eq]; ring
  have hcube : Real.sqrt ((k : ℝ) / n) ^ 3 = ((k : ℝ) / n) * Real.sqrt ((k : ℝ) / n) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ) / n by positivity)
    calc Real.sqrt ((k : ℝ) / n) ^ 3
        = Real.sqrt ((k : ℝ) / n) ^ 2 * Real.sqrt ((k : ℝ) / n) := by ring
      _ = _ := by rw [hsq]
  unfold est bchksBound
  rw [estM_eq heta, hg, hcube]

/-! ## Counting -/

/-- If every element with the property P lies in the finite set s, then `cnt P` is at most the size
of s. -/
theorem cnt_le_card_of_mem {α : Type} [Finite α] (P : α → Prop) (s : Finset α)
    (h : ∀ a, P a → a ∈ s) : cnt P ≤ s.card := by
  have h1 : cnt P ≤ Nat.card {a : α // a ∈ s} :=
    Nat.card_le_card_of_injective (fun a : {a : α // P a} => (⟨a.1, h a.1 a.2⟩ : {a : α // a ∈ s}))
      (fun _ _ hab => Subtype.ext (congrArg (fun y : {a : α // a ∈ s} => y.1) hab))
  have h2 : Nat.card {a : α // a ∈ s} = s.card := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_coe s
  omega

/-! ## The bridge -/

/-- **The fact on lines implies `BCHKS46`, for every finite field.** -/
theorem bchks46_of_lineFact (H : LineFact) : BCHKS46 := by
  intro K _ _ n k e x hx hk he hJ u₀ u₁
  obtain ⟨hen, hkn, -⟩ := side he hJ
  have heta := eta_pos hen hJ
  obtain ⟨excl, exclCard, outside⟩ := H K n k (n - e) (etaOf n k e) x hx u₀ u₁ hk hkn heta
    (agreement_le_one n k e) (threshold hen) (Nat.sub_le _ _)
  have hsub : ∀ z : K,
      (∃ A : Finset (Fin n), n ≤ A.card + e ∧ OnRS x k (fun j => u₀ j + z * u₁ j) A ∧
        ¬ (OnRS x k u₀ A ∧ OnRS x k u₁ A)) → z ∈ excl := by
    rintro z ⟨S, hS, ⟨p, hpdeg, hp⟩, hnot⟩
    by_contra hz
    obtain ⟨P₀, P₁, h0, h1, hmem⟩ :=
      outside z hz p hpdeg S (by omega) (fun j hj => (hp j hj).symm)
    exact hnot ⟨⟨P₀, h0, fun j hj => (hmem j hj).1.symm⟩, ⟨P₁, h1, fun j hj => (hmem j hj).2.symm⟩⟩
  have hcnt := cnt_le_card_of_mem _ excl hsub
  calc ((cnt _ : ℕ) : ℝ) ≤ (excl.card : ℝ) := by exact_mod_cast hcnt
    _ ≤ est n k (etaOf n k e) := exclCard
    _ = bchksBound n k e := est_eq_bchks heta

/-- The form over one field E with points in a subfield F is a special case of the form for every
finite field. -/
theorem bchks46At_of_wide (H : BCHKS46) (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] :
    BCHKS46At F E := by
  intro n k e x hx hk he hJ u₀ u₁
  exact H E n k e (fun j => algebraMap F E (x j)) ((algebraMap F E).injective.comp hx)
    hk he hJ u₀ u₁

end Cb.Bridge
