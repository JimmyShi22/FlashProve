/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/PowerAgreement.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 33 of the 47 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Lemmas are called by their names in Lean 4.29.1 and this Mathlib: eval_finsetSum became
  eval_finset_sum (2 times).
* Lines around the declarations changed: `open Polynomial CoreDefinitions` became `open Polynomial`:
  the namespace CoreDefinitions is declared only in files of ArkLib that are not taken over.
-/

import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Rat.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.Agreement
import ThirdParty.ArkLib.Data.Polynomial.SpecializationAvoidance

/-!
# Exact power agreement for Reed–Solomon codes

A tuple `w : Fin (ℓ + 1) → ι → F` of received words is batched by one challenge `z` into
`i ↦ ∑ t, z ^ t * w t i`. A polynomial `Q` of degree below `k` close to the batched word has
*exact power agreement* if `Q = ∑ t, z ^ t • P t` for polynomials `P t` of degree below `k`, and
the coordinates where `Q` agrees with the batched word are exactly the coordinates where every
`P t` agrees with `w t`. This file states that property and its uniform version in polynomial
form, and identifies them with the code-level predicates `Code.HasExactAgreement` and
`Code.UniformExactAgreement` for the Reed–Solomon code and the batching map
`CoreDefinitions.univariatePowersGenerator F ℓ`.

The identification needs no relation between `k` and the agreement threshold or the block
length. Codeword witnesses give polynomial witnesses whose evaluations are correct; if `k`
exceeds the number of evaluation points, the polynomial identity `Q = ∑ t, z ^ t • P t` can
still fail, and it is repaired by adding the difference to `P 0`, whose weight is `z ^ 0 = 1`
(`exists_powerBatchedPolynomial_eq`).

For a fixed tuple `P`, the discrepancy at a coordinate `i` is a polynomial of degree at most `ℓ`
in the challenge, `curveDiscrepancy domain w P i`, whose coefficients are the constituent
discrepancies `(P t).eval (domain i) - w t i`. It is zero exactly at the common agreements, so
outside the roots of the nonzero discrepancies, at most `ℓ * (|ι| - L)` challenges when the tuple
has `L` common agreements, the batched polynomial gains no extra agreement. Exact power agreement
over an extension field descends to the base field with the same number of exceptional
challenges.

The code-level characterizations let the counting and transfer theorems of
`ArkLib.Data.CodingTheory.InterleavedCode.ExactAgreement` apply to Reed–Solomon statements. The
interleaved statements are in `ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement`.

## Main definitions

* `ReedSolomon.powerBatchedWord`, `ReedSolomon.powerBatchedPolynomial`: batching of received
  words and of message polynomials.
* `ReedSolomon.commonCurveAgreementSet`: coordinates where every `P t` agrees with `w t`.
* `ReedSolomon.polynomialTupleFamily`: the interpolant tuples on `k`-element samples.
* `ReedSolomon.powerBatchedCoordinate`: a coordinate vector as a polynomial in the challenge.
* `ReedSolomon.frobeniusPowerCoordinate`: a coordinate vector with challenge exponents scaled
  by a natural number.
* `ReedSolomon.curveDiscrepancy`: the discrepancy at one coordinate as a polynomial in the
  challenge.
* `ReedSolomon.HasExactPowerAgreement`: exact power agreement, with the challenge and the
  candidate polynomial in an extension field `E` given by `φ : F →+* E`.
* `ReedSolomon.UniformExactPowerAgreement`: one exceptional set of at most `e` challenges for
  every candidate with at least `L` agreements.

## Main statements

* `ReedSolomon.frobeniusPowerCoordinate_eval` and
  `ReedSolomon.frobeniusPowerCoordinate_natDegree_le`: evaluation and degree bounds for sparse
  coordinates.
* `ReedSolomon.eval₂_powerBatchedCoordinate_eq_powerBatchedWord`: coordinate evaluation commutes
  with a semiring homomorphism into the target field.
* `ReedSolomon.exists_exceptional_powerBatched_agreement` and
  `ReedSolomon.exists_exceptional_powerBatched_family`: outside at most `ℓ * (|ι| - L)`
  challenges per tuple, the agreement set of the batched polynomial is the common agreement set.
* `ReedSolomon.mem_polynomialTupleFamily_iff` and
  `ReedSolomon.mem_polynomialTupleFamily_of_commonAgreement`:
  the degree and common-agreement characterization of the interpolant family.
* `ReedSolomon.polynomialTupleFamily_card_le`: the sample-size bound for the interpolant family.
* `ReedSolomon.exists_polynomialGraph_of_sample`: a sample of `k` coordinates determines every
  batched polynomial of degree below `k` that agrees with the batched word on it, over every
  extension field.
* `ReedSolomon.HasExactPowerAgreement.descend` and
  `ReedSolomon.uniformExactPowerAgreement_of_extension`: exact power agreement descends from an
  extension field.
* `ReedSolomon.hasExactPowerAgreement_singleton`: one constituent has exact power agreement
  whenever a degree-bounded candidate has at least `k` agreements.
* `ReedSolomon.uniformExactPowerAgreement_of_all_samples`: retaining all common-sample
  interpolants gives a characteristic-free uniform recovery bound.
* `ReedSolomon.determinedByAgreement_code`: Reed–Solomon codewords of message length `k` are
  determined by `a ≥ k` agreements.
* `ReedSolomon.exists_powerBatchedPolynomial_eq`: a codeword decomposition of a polynomial's
  evaluations lifts to a polynomial decomposition.
* `ReedSolomon.uniformExactPowerAgreement_singleton`: a single received word has uniform exact
  power agreement with no exceptional challenge.
* `ReedSolomon.exists_exactPower_fullDimension` and
  `ReedSolomon.uniformExactPowerAgreement_fullDimension`: every full-agreement candidate has exact
  power agreement at full message dimension, with no exceptional challenge.
* `ReedSolomon.hasExactPowerAgreement_id_iff_hasExactAgreement` and
  `ReedSolomon.uniformExactPowerAgreement_iff_uniformExactAgreement`: the polynomial predicates
  are the code-level predicates for `univariatePowersGenerator`.

## References

* [DKT26]
-/

namespace ReedSolomon

open Polynomial

noncomputable section

section Batching

variable {F ι : Type*} [Field F] {ℓ : ℕ}

/-- The received word obtained by batching the words `w t` with the powers `z ^ t` of one
challenge: `i ↦ ∑ t, z ^ t * w t i`. -/
def powerBatchedWord (w : Fin (ℓ + 1) → ι → F) (z : F) : ι → F :=
  fun i ↦ ∑ t, z ^ t.val * w t i

/-- The combination `∑ t, z ^ t • P t` of message polynomials. -/
def powerBatchedPolynomial (P : Fin (ℓ + 1) → F[X]) (z : F) : F[X] :=
  ∑ t, z ^ t.val • P t

/-- Batching preserves the degree bound `degree < k`, including for `k = 0`. -/
theorem powerBatchedPolynomial_degree_lt (P : Fin (ℓ + 1) → F[X]) (z : F) (k : ℕ)
    (hP : ∀ t, (P t).degree < k) : (powerBatchedPolynomial P z).degree < k := by
  rw [← mem_degreeLT]
  exact Submodule.sum_mem _ fun t _ ↦ Submodule.smul_mem _ _ (mem_degreeLT.mpr (hP t))

/-- Evaluation commutes with batching. -/
theorem powerBatchedPolynomial_eval (P : Fin (ℓ + 1) → F[X]) (z x : F) :
    (powerBatchedPolynomial P z).eval x = ∑ t, z ^ t.val * (P t).eval x := by
  simp [powerBatchedPolynomial, eval_finset_sum]

/-- The coordinates where every polynomial `P t` agrees with its received word `w t`. -/
def commonCurveAgreementSet [DecidableEq F] [Fintype ι] (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) (P : Fin (ℓ + 1) → F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ ∀ t, (P t).eval (domain i) = w t i

/-- Coordinate `i` is in `commonCurveAgreementSet domain w P` exactly when every `P t` evaluates
to `w t i` at `domain i`. -/
@[simp] theorem mem_commonCurveAgreementSet [DecidableEq F] [Fintype ι] (domain : ι ↪ F)
    (w : Fin (ℓ + 1) → ι → F) (P : Fin (ℓ + 1) → F[X]) (i : ι) :
    i ∈ commonCurveAgreementSet domain w P ↔ ∀ t, (P t).eval (domain i) = w t i := by
  simp [commonCurveAgreementSet]

end Batching

section Coordinate

variable {R : Type*} [CommSemiring R] {ℓ : ℕ}

/-- The polynomial `∑ t, w t * X ^ t` in the batching challenge. Its value at `z` is the batched
coordinate `∑ t, z ^ t * w t`. -/
def powerBatchedCoordinate (w : Fin (ℓ + 1) → R) : R[X] :=
  ∑ t, monomial t.val (w t)

/-- The value of `powerBatchedCoordinate w` at `z` is `∑ t, z ^ t * w t`. -/
theorem powerBatchedCoordinate_eval (w : Fin (ℓ + 1) → R) (z : R) :
    (powerBatchedCoordinate w).eval z = ∑ t, z ^ t.val * w t := by
  simp [powerBatchedCoordinate, eval_finset_sum, mul_comm]

/-- `powerBatchedCoordinate w` has degree at most `ℓ`. -/
theorem powerBatchedCoordinate_natDegree_le (w : Fin (ℓ + 1) → R) :
    (powerBatchedCoordinate w).natDegree ≤ ℓ :=
  natDegree_sum_le_of_forall_le _ _ fun t _ ↦
    (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp t.isLt)

/-- `powerBatchedCoordinate w` is Mathlib's `ofFn (ℓ + 1) w`. -/
theorem powerBatchedCoordinate_eq_ofFn [DecidableEq R] (w : Fin (ℓ + 1) → R) :
    powerBatchedCoordinate w = ofFn (ℓ + 1) w :=
  (ofFn_eq_sum_monomial w).symm

/-- The coefficient of `X ^ t` in `powerBatchedCoordinate w` is `w t`. -/
@[simp] theorem powerBatchedCoordinate_coeff (w : Fin (ℓ + 1) → R) (t : Fin (ℓ + 1)) :
    (powerBatchedCoordinate w).coeff t = w t := by
  classical
  rw [powerBatchedCoordinate_eq_ofFn, ofFn_coeff_eq_val_of_lt w t.isLt]

/-- The polynomial coordinate whose challenge exponents are scaled by `s`. -/
def frobeniusPowerCoordinate (s : ℕ) (values : Fin (ℓ + 1) → R) : R[X] :=
  Polynomial.expand R s (powerBatchedCoordinate values)

/-- Evaluation of `frobeniusPowerCoordinate` scales each challenge exponent by `s`. -/
theorem frobeniusPowerCoordinate_eval (s : ℕ) (values : Fin (ℓ + 1) → R) (z : R) :
    (frobeniusPowerCoordinate s values).eval z =
      ∑ t, z ^ (s * t.val) * values t := by
  rw [frobeniusPowerCoordinate, Polynomial.expand_eval, powerBatchedCoordinate_eval]
  apply Finset.sum_congr rfl
  intro t _
  rw [pow_mul]

/-- The degree of `frobeniusPowerCoordinate` is at most `s * ℓ`. -/
theorem frobeniusPowerCoordinate_natDegree_le (s : ℕ) (values : Fin (ℓ + 1) → R) :
    (frobeniusPowerCoordinate s values).natDegree ≤ s * ℓ := by
  rw [frobeniusPowerCoordinate, Polynomial.natDegree_expand]
  exact (Nat.mul_le_mul_right s (powerBatchedCoordinate_natDegree_le values)).trans_eq
    (Nat.mul_comm _ _)

/-- A coordinate vector is determined by its polynomial `powerBatchedCoordinate`. -/
theorem powerBatchedCoordinate_injective :
    Function.Injective (powerBatchedCoordinate (R := R) (ℓ := ℓ)) := by
  classical
  rw [show powerBatchedCoordinate (R := R) (ℓ := ℓ) = ofFn (ℓ + 1) from
    _root_.funext powerBatchedCoordinate_eq_ofFn]
  exact injective_ofFn _

/-- `powerBatchedCoordinate w` is zero exactly when `w` is. -/
@[simp] theorem powerBatchedCoordinate_eq_zero_iff (w : Fin (ℓ + 1) → R) :
    powerBatchedCoordinate w = 0 ↔ w = 0 := by
  rw [← powerBatchedCoordinate_injective.eq_iff]
  simp [powerBatchedCoordinate]

end Coordinate

section Discrepancy

variable {F ι : Type*} [Field F] {ℓ : ℕ}

/-- The discrepancy at coordinate `i` as a polynomial in the batching challenge: the coefficient of
`X ^ t` is `(P t).eval (domain i) - w t i`. -/
def curveDiscrepancy (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (P : Fin (ℓ + 1) → F[X])
    (i : ι) : F[X] :=
  powerBatchedCoordinate fun t ↦ (P t).eval (domain i) - w t i

/-- `curveDiscrepancy domain w P i` has degree at most `ℓ`. -/
theorem curveDiscrepancy_natDegree_le (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (i : ι) : (curveDiscrepancy domain w P i).natDegree ≤ ℓ :=
  powerBatchedCoordinate_natDegree_le _

/-- At the challenge `z`, the discrepancy is the batched polynomial's value minus the batched
word at coordinate `i`. -/
theorem curveDiscrepancy_eval (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (i : ι) (z : F) :
    (curveDiscrepancy domain w P i).eval z =
      (powerBatchedPolynomial P z).eval (domain i) - powerBatchedWord w z i := by
  simp [curveDiscrepancy, powerBatchedCoordinate_eval, powerBatchedPolynomial_eval,
    powerBatchedWord, mul_sub, Finset.sum_sub_distrib]

/-- The discrepancy at `i` is the zero polynomial exactly when every `P t` agrees with `w t`
at `i`. -/
theorem curveDiscrepancy_eq_zero_iff (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (i : ι) :
    curveDiscrepancy domain w P i = 0 ↔ ∀ t, (P t).eval (domain i) = w t i := by
  simp [curveDiscrepancy, funext_iff, sub_eq_zero]

variable [DecidableEq F] [Fintype ι]

/-- **Few challenges create extra agreement.** If the `P t` agree with the `w t` simultaneously on
at least `L` coordinates, then outside a set of at most `ℓ * (|ι| - L)` challenges `z`, the
agreement set of `∑ t, z ^ t • P t` with the batched word is exactly the common agreement set
of the `P t`.

Each coordinate outside the common agreement set contributes the at most `ℓ` roots of its
discrepancy polynomial. No assumption on the characteristic is needed. -/
theorem exists_exceptional_powerBatched_agreement (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (L : ℕ) (hcommon : L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset F, exceptional.card ≤ ℓ * (Fintype.card ι - L) ∧
      ∀ z ∉ exceptional,
        polynomialAgreementSet domain (powerBatchedWord w z) (powerBatchedPolynomial P z) =
          commonCurveAgreementSet domain w P := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ := exists_card_le_forall_eval_eq_zero_iff
    (curveDiscrepancy domain w P) (Finset.univ \ commonCurveAgreementSet domain w P)
    (fun i _ ↦ curveDiscrepancy_natDegree_le domain w P i)
    (fun i hi ↦ (curveDiscrepancy_eq_zero_iff domain w P i).mpr (by simpa using hi))
  refine ⟨exceptional, hcard.trans (Nat.mul_le_mul_left _ ?_), fun z hz ↦ ?_⟩
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  · ext i
    have := hgood z hz i
    rw [curveDiscrepancy_eval, sub_eq_zero, curveDiscrepancy_eq_zero_iff] at this
    simpa using this

/-- A finite family of tuples, each with at least `L` common agreements, has one set of at most
`family.card * (ℓ * (|ι| - L))` challenges outside which no member gains extra agreement. -/
theorem exists_exceptional_powerBatched_family (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (family : Finset (Fin (ℓ + 1) → F[X])) (L : ℕ)
    (hcommon : ∀ P ∈ family, L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset F, exceptional.card ≤ family.card * (ℓ * (Fintype.card ι - L)) ∧
      ∀ P ∈ family, ∀ z ∉ exceptional,
        polynomialAgreementSet domain (powerBatchedWord w z) (powerBatchedPolynomial P z) =
          commonCurveAgreementSet domain w P := by
  classical
  choose! ex hcard hgood using fun P hP ↦
    exists_exceptional_powerBatched_agreement domain w P L (hcommon P hP)
  refine ⟨family.biUnion ex, Finset.card_biUnion_le_card_mul _ _ _ hcard,
    fun P hP z hz ↦ hgood P hP z fun hmem ↦ hz (Finset.mem_biUnion.mpr ⟨P, hP, hmem⟩)⟩

end Discrepancy

section Interpolation

variable {F ι : Type*} [Field F] {ℓ : ℕ}

/-- The finite family of tuples interpolated from received values on a common sample. -/
def polynomialTupleFamily [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (k : ℕ) :
    Finset (Fin (ℓ + 1) → F[X]) := by
  classical
  exact (Finset.univ.powersetCard k).image fun sample t ↦
    Lagrange.interpolate sample domain (w t)

/-- A degree-bounded tuple with at least `k` common agreements belongs to the interpolation
family. -/
theorem mem_polynomialTupleFamily_of_commonAgreement [Fintype ι] [DecidableEq ι]
    [DecidableEq F] (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (k : ℕ)
    (hdegree : ∀ t, (P t).degree < k)
    (hcommon : k ≤ (commonCurveAgreementSet domain w P).card) :
    P ∈ polynomialTupleFamily domain w k := by
  classical
  obtain ⟨sample, hsub, hcard⟩ := Finset.exists_subset_card_eq hcommon
  have hinj : Set.InjOn domain sample := domain.injective.injOn
  apply Finset.mem_image.mpr
  refine ⟨sample, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
  funext t
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample hinj
  · exact Lagrange.degree_interpolate_lt (w t) hinj
  · simpa only [hcard] using hdegree t
  · intro i hi
    rw [Lagrange.eval_interpolate_at_node (w t) hinj hi]
    have himem := hsub hi
    simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at himem
    exact (himem t).symm

/-- The interpolation family consists exactly of degree-bounded tuples with at least `k` common
agreements. -/
theorem mem_polynomialTupleFamily_iff [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P : Fin (ℓ + 1) → F[X]) (k : ℕ) :
    P ∈ polynomialTupleFamily domain w k ↔
      (∀ t, (P t).degree < k) ∧ k ≤ (commonCurveAgreementSet domain w P).card := by
  classical
  constructor
  · intro hP
    obtain ⟨sample, hsample, rfl⟩ := Finset.mem_image.mp hP
    have hcard := (Finset.mem_powersetCard.mp hsample).2
    have hinj : Set.InjOn domain sample := domain.injective.injOn
    constructor
    · intro t
      simpa only [hcard] using Lagrange.degree_interpolate_lt (w t) hinj
    · rw [← hcard]
      apply Finset.card_le_card
      intro i hi
      simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro t
      exact Lagrange.eval_interpolate_at_node (w t) hinj hi
  · rintro ⟨hdegree, hcommon⟩
    exact mem_polynomialTupleFamily_of_commonAgreement domain w P k hdegree hcommon

/-- Interpolating each word `w t` on a finite sample set gives polynomials `P t` of degree below
any `k ≥ samples.card` that agree with every `w t` on the samples. -/
theorem exists_polynomialTuple_interpolating (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    {k : ℕ} (samples : Finset ι) (hcard : samples.card ≤ k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      ∀ i ∈ samples, ∀ t, (P t).eval (domain i) = w t i := by
  classical
  refine ⟨fun t ↦ Lagrange.interpolate samples domain (w t), fun t ↦ ?_, fun i hi t ↦ ?_⟩
  · exact (Lagrange.degree_interpolate_lt _ domain.injective.injOn).trans_le
      (by exact_mod_cast hcard)
  · exact Lagrange.eval_interpolate_at_node (w t) domain.injective.injOn hi

/-- Two tuples of polynomials of degree below `k ≤ samples.card` that agree with the same words on
the samples are equal. -/
theorem polynomialTuple_eq_of_common_samples (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F)
    (P Q : Fin (ℓ + 1) → F[X]) {k : ℕ} (samples : Finset ι) (hcard : k ≤ samples.card)
    (hP : ∀ t, (P t).degree < k) (hQ : ∀ t, (Q t).degree < k)
    (hPs : ∀ i ∈ samples, ∀ t, (P t).eval (domain i) = w t i)
    (hQs : ∀ i ∈ samples, ∀ t, (Q t).eval (domain i) = w t i) : P = Q := by
  have hk : (k : WithBot ℕ) ≤ samples.card := by exact_mod_cast hcard
  funext t
  exact eq_of_degrees_lt_of_eval_index_eq samples domain.injective.injOn
    ((hP t).trans_le hk) ((hQ t).trans_le hk) fun i hi ↦ (hPs i hi t).trans (hQs i hi t).symm

/-- **A sample of `k` coordinates determines the batched polynomial.** For a sample set of size
`k`, the interpolating tuple `P` of degree below `k` has the property that over every field `E`
with `φ : F →+* E`, each polynomial `Q` of degree below `k` agreeing with the batched word at
`z : E` on the samples equals `∑ t, z ^ t • (P t).map φ`. -/
theorem exists_polynomialGraph_of_sample (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) {k : ℕ}
    (samples : Finset ι) (hcard : samples.card = k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ samples, ∀ t, (P t).eval (domain i) = w t i) ∧
      ∀ {E : Type*} [Field E] (φ : F →+* E) (z : E) (Q : E[X]), Q.degree < k →
        (∀ i ∈ samples, Q.eval (φ (domain i)) = ∑ t, z ^ t.val * φ (w t i)) →
        Q = powerBatchedPolynomial (fun t ↦ (P t).map φ) z := by
  obtain ⟨P, hP, hs⟩ := exists_polynomialTuple_interpolating domain w samples hcard.le
  refine ⟨P, hP, hs, fun φ z Q hQ hQs ↦ ?_⟩
  subst hcard
  refine eq_of_degrees_lt_of_eval_index_eq samples
    (fun _ _ _ _ h ↦ domain.injective (φ.injective h)) hQ
    (powerBatchedPolynomial_degree_lt _ z _ fun t ↦ degree_map_le.trans_lt (hP t))
    fun i hi ↦ ?_
  rw [powerBatchedPolynomial_eval, hQs i hi]
  simp [eval_map, eval₂_at_apply, hs i hi]

end Interpolation

section ScalarExtension

variable {F E ι : Type*} [Field F] [Field E] {ℓ : ℕ}

/-- Applying `φ : F →+* E` to the words and the challenge batches to `φ` of the batched word. -/
theorem powerBatchedWord_map (w : Fin (ℓ + 1) → ι → F) (φ : F →+* E) (z : F) :
    powerBatchedWord (fun t i ↦ φ (w t i)) (φ z) = fun i ↦ φ (powerBatchedWord w z i) := by
  funext i
  simp [powerBatchedWord]

/-- Mapping the batched polynomial along `φ : F →+* E` batches the mapped polynomials at `φ z`. -/
theorem powerBatchedPolynomial_map (P : Fin (ℓ + 1) → F[X]) (φ : F →+* E) (z : F) :
    (powerBatchedPolynomial P z).map φ =
      powerBatchedPolynomial (fun t ↦ (P t).map φ) (φ z) := by
  simp [powerBatchedPolynomial, smul_eq_C_mul, Polynomial.map_sum]

end ScalarExtension

section Exact

variable {F E ι : Type*} [Field F] [Field E] [Fintype ι] [DecidableEq F] [DecidableEq E] {ℓ : ℕ}

/-- **Exact power agreement.** The polynomial `Q` over `E` is `∑ t, z ^ t • (P t).map φ` for
message polynomials `P t` over `F` of degree below `k`, and the coordinates where `Q` agrees with
the batched received word are exactly those where every `P t` agrees with `w t`.

The equality of agreement sets is the substance: it says that `Q` has no agreement beyond the
common agreement of the constituents. The embedding `φ` allows the challenge and `Q` to live in an
extension field while the messages and received words stay over `F`; the Reed–Solomon statements
in this file use `φ = RingHom.id F`. -/
def HasExactPowerAgreement (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (φ : F →+* E) (k : ℕ)
    (z : E) (Q : E[X]) : Prop :=
  ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
    Q = powerBatchedPolynomial (fun t ↦ (P t).map φ) z ∧
    polynomialAgreementSet (domain.trans ⟨φ, φ.injective⟩)
        (powerBatchedWord (fun t i ↦ φ (w t i)) z) Q =
      commonCurveAgreementSet domain w P

/-- With `φ = RingHom.id F`, exact power agreement is stated over `F` directly: `Q` is
`∑ t, z ^ t • P t` and its agreement set with `powerBatchedWord w z` is the common agreement set
of the `P t`. -/
theorem hasExactPowerAgreement_id_iff (domain : ι ↪ F) (w : Fin (ℓ + 1) → ι → F) (k : ℕ) (z : F)
    (Q : F[X]) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q ↔
      ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧ Q = powerBatchedPolynomial P z ∧
        polynomialAgreementSet domain (powerBatchedWord w z) Q =
          commonCurveAgreementSet domain w P := by
  have hdomain : domain.trans ⟨RingHom.id F, (RingHom.id F).injective⟩ = domain :=
    Function.Embedding.ext fun _ ↦ rfl
  simp only [HasExactPowerAgreement, Polynomial.map_id, RingHom.id_apply, hdomain]

end Exact

section Descent

variable {F E ι : Type*} [Field F] [Field E] [Fintype ι] [DecidableEq F] [DecidableEq E] {ℓ : ℕ}

/-- Exact power agreement over an extension descends: if `Q.map φ` has exact power agreement at
the challenge `φ z`, then `Q` has exact power agreement at `z` over `F`. The same tuple `P` is a
witness. -/
theorem HasExactPowerAgreement.descend {domain : ι ↪ F} {w : Fin (ℓ + 1) → ι → F}
    {φ : F →+* E} {k : ℕ} {z : F} {Q : F[X]}
    (h : HasExactPowerAgreement domain w φ k (φ z) (Q.map φ)) :
    HasExactPowerAgreement domain w (RingHom.id F) k z Q := by
  obtain ⟨P, hP, heq, hagree⟩ := h
  refine (hasExactPowerAgreement_id_iff domain w k z Q).mpr ⟨P, hP, ?_, ?_⟩
  · exact map_injective φ φ.injective (heq.trans (powerBatchedPolynomial_map P φ z).symm)
  · rwa [powerBatchedWord_map, polynomialAgreementSet_map] at hagree

end Descent

section AllSamples

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F] {ℓ k L : ℕ}

end AllSamples

section CodeLevel

variable {F : Type} {ι : Type*} [Field F] {ℓ : ℕ}

variable [Fintype ι] [DecidableEq F]

end CodeLevel

end

end ReedSolomon
