/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/Ideal/MinimalPrime/Noetherian.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 6 of the 11 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Minimal primes of a Noetherian ideal as a finset

In a Noetherian commutative semiring the minimal primes over an ideal form a finite set
(`Ideal.finite_minimalPrimes_of_isNoetherianRing`). This file packages that set as a `Finset`,
so that it can index finite sums and unions, and defines the minimal primes *retained* by an
element `s`: those that do not contain `s`.

For a polynomial ideal `I`, the retained minimal primes index the algebraic components on which
`s` is not identically zero. This does not assert that each component has a point over a given
field extension. The point-cover statements for `MvPolynomial.zeroLocus` are in
`ArkLib.ToMathlib.RingTheory.Nullstellensatz`. The principal-cut Krull-dimension consequences of
this finite family are in `ArkLib.ToMathlib.RingTheory.Ideal.PrincipalCut`.

## Main definitions

* `Ideal.minimalPrimesFinset I`: the minimal primes over `I`, as a `Finset`.
* `Ideal.retainedMinimalPrimes I s`: the minimal primes over `I` that do not contain `s`,
  defined as a filter of `Ideal.minimalPrimesFinset I`.

## Main statements

* `Ideal.mem_minimalPrimesFinset` and `Ideal.mem_retainedMinimalPrimes`: membership laws.
* `Ideal.exists_mem_retainedMinimalPrimes_le`: every prime `Q` over `I` with `s ∉ Q` contains a
  retained minimal prime. This is the algebraic content of the regular-point cover.
* `Ideal.retainedMinimalPrimes_eq_empty_iff`: no minimal prime is retained exactly when `s` lies
  in the radical of `I`.
* `Ideal.retainedMinimalPrimes_of_isUnit`: a unit retains every minimal prime.

## Proof outline

Membership reduces to `Set.Finite.mem_toFinset` and `Finset.mem_filter`. The existence statement
applies `Ideal.exists_minimalPrimes_le` to `Q` and observes that a prime below `Q` cannot contain
`s`. The emptiness criterion uses `Ideal.sInf_minimalPrimes`: the radical is the intersection of
the minimal primes.
-/

namespace Ideal

variable {R : Type*} [CommSemiring R] [IsNoetherianRing R]

/-- The minimal primes over an ideal `I` of a Noetherian commutative semiring, as a `Finset`.

The underlying set is `I.minimalPrimes`, which is finite by
`Ideal.finite_minimalPrimes_of_isNoetherianRing`. The Noetherian hypothesis is what makes the
set finite: in the non-Noetherian product ring `ℕ → ℤ`, the zero ideal has the infinitely many
minimal primes `{f | f n = 0}`, one for each `n`. For `I = ⊤` the finset is empty. -/
noncomputable def minimalPrimesFinset (I : Ideal R) : Finset (Ideal R) :=
  (I.finite_minimalPrimes_of_isNoetherianRing R).toFinset

/-- An ideal belongs to `I.minimalPrimesFinset` exactly when it is a minimal prime over `I`. -/
@[simp]
theorem mem_minimalPrimesFinset {I P : Ideal R} :
    P ∈ I.minimalPrimesFinset ↔ P ∈ I.minimalPrimes := by
  simp [minimalPrimesFinset]

/-- The minimal primes over `I` retained by `s`: those that do not contain `s`.

For an ideal `I` of polynomials, these index the algebraic components on which `s` is not
identically zero; this does not require a point over any particular field extension.
The family is defined as a filter of `I.minimalPrimesFinset`. It equals `I.minimalPrimesFinset`
when `s` is a unit (`retainedMinimalPrimes_of_isUnit`) and is empty exactly when `s` lies in the
radical of `I` (`retainedMinimalPrimes_eq_empty_iff`). -/
noncomputable def retainedMinimalPrimes (I : Ideal R) (s : R) : Finset (Ideal R) := by
  classical
  exact I.minimalPrimesFinset.filter (fun P ↦ s ∉ P)

/-- An ideal is retained by `s` exactly when it is a minimal prime over `I` not containing `s`. -/
@[simp]
theorem mem_retainedMinimalPrimes {I P : Ideal R} {s : R} :
    P ∈ I.retainedMinimalPrimes s ↔ P ∈ I.minimalPrimes ∧ s ∉ P := by
  classical
  simp [retainedMinimalPrimes]

/-- The retained minimal primes form a subfamily of all minimal primes. -/
theorem retainedMinimalPrimes_subset (I : Ideal R) (s : R) :
    I.retainedMinimalPrimes s ⊆ I.minimalPrimesFinset := fun _ hP ↦
  mem_minimalPrimesFinset.mpr (mem_retainedMinimalPrimes.mp hP).1

/-- Every prime `Q` over `I` that does not contain `s` contains a minimal prime over `I` retained
by `s`.

Both hypotheses are needed. Every minimal prime over `I` contains `I`, so if `I ≰ Q` none lies
below `Q`; for `I = ⊤` there are no minimal primes at all. If `s ∈ Q`, take `I = Q`: the only
minimal prime over `Q` is `Q` itself, which contains `s`, so nothing is retained. -/
theorem exists_mem_retainedMinimalPrimes_le {I Q : Ideal R} [Q.IsPrime] {s : R}
    (hIQ : I ≤ Q) (hsQ : s ∉ Q) :
    ∃ P ∈ I.retainedMinimalPrimes s, P ≤ Q := by
  obtain ⟨P, hP, hPQ⟩ := I.exists_minimalPrimes_le hIQ
  exact ⟨P, mem_retainedMinimalPrimes.mpr ⟨hP, fun hsP ↦ hsQ (hPQ hsP)⟩, hPQ⟩

end Ideal
