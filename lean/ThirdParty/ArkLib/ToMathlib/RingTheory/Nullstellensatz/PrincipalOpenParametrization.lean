/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/Nullstellensatz/PrincipalOpenParametrization.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 4 of the 8 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpen

/-!
# Principal open subsets covered by polynomial parametrizations

Let `k` be a field, `σ` a finite type, `I` an ideal of `MvPolynomial σ k` and `s` a polynomial
whose class is a non-zero-divisor modulo `I`. Write `H(I)` for `affineHilbertPolynomial I` and
`U(I) = {x ∈ V(I) | s(x) ≠ 0}` for the principal open subset of the zero locus cut out by `s`.

Suppose `U(I)` is covered by a polynomial parametrization, that is, every point of `U(I)` has the
form `x = (w i (t))ᵢ` for some parameter `t`, where `w : σ → MvPolynomial τ k`. Then the dimension
`natDegree H(I)` is at most `Nat.card τ`. For a one-parameter family `w : σ → k[X]` the bound is
`1`, and if `I` has positive dimension, then every polynomial vanishing on `U(I)` vanishes
identically after substituting the parametrization.

The dimension bound comes from the kernel `J` of the substitution `aeval w`. Every polynomial in
`J` vanishes on `U(I)`, so by the Nullstellensatz for principal open subsets
(`mem_radical_of_forall_principalOpen`) it lies in `I.radical`. Hence `H(I)` has natural degree at
most that of `H(J)`, and the quotient by `J` embeds into `MvPolynomial τ k`, whose Hilbert
polynomial has natural degree `Nat.card τ`. No image closure is constructed.

The vanishing statement uses only that `U(I)` is infinite when `I` has positive dimension: the
parameters of an infinite set of points form an infinite set of roots of the substituted
polynomial.

## Main statements

* `MvPolynomial.polynomial_eval_aeval`: substituting univariate polynomials and then evaluating
  at `z` is evaluation at the point `(w i (z))ᵢ`.
* `MvPolynomial.aeval_eq_zero_of_infinite`: over a domain, a polynomial vanishing on an infinite
  subset of a one-parameter polynomial curve vanishes after substitution.
* `MvPolynomial.mem_radical_of_forall_principalOpen`: a polynomial vanishing on `U(I)`, with
  points in an algebraically closed extension, lies in `I.radical`.
* `MvPolynomial.ker_aeval_le_radical_of_principalOpen_subset_range` and
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_principalOpen_subset_range`: a
  parametrization of `U(I)` by `τ`-tuples bounds the dimension of `I` by `Nat.card τ`.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_one_of_principalOpen_subset_range`: the
  one-parameter case.
* `MvPolynomial.aeval_eq_zero_of_principalOpen_subset_range`: polynomial identities along a
  one-parameter family covering a positive-dimensional `U(I)`.
* `MvPolynomial.regular_principalOpen_graph_restriction`: ideal restriction and cut
  nonvanishing for a positive-dimensional prime principal open covered by a polynomial graph.
-/

namespace MvPolynomial

/-- Substituting univariate polynomials `w i` into a multivariate polynomial and evaluating the
result at `z` is evaluation at the point `(w i (z))ᵢ`. -/
theorem polynomial_eval_aeval {R σ : Type*} [CommSemiring R] (w : σ → Polynomial R) (z : R)
    (p : MvPolynomial σ R) :
    (aeval w p).eval z = eval (fun i ↦ (w i).eval z) p := by
  have h := comp_aeval_apply (f := w) (Polynomial.aeval z) p
  simp only [Polynomial.coe_aeval_eq_eval] at h
  exact h

/-- Over a domain `R`, let `S` be an infinite set of points of the curve `z ↦ (w i (z))ᵢ`. A
polynomial `p` vanishing on `S` vanishes after substituting `w`: `aeval w p = 0`.

Distinct points of `S` have distinct parameters, so the univariate polynomial `aeval w p` has
infinitely many roots. Infiniteness is needed: for `σ = Unit`, `w = X`, `p = X ()` and `S = {0}`,
`p` vanishes on `S` but `aeval w p = X`. The domain hypothesis is needed for a nonzero
univariate polynomial to have finitely many roots. -/
theorem aeval_eq_zero_of_infinite {R σ : Type*} [CommRing R] [IsDomain R] (w : σ → Polynomial R)
    {S : Set (σ → R)} (hS : S.Infinite) (hcurve : ∀ x ∈ S, ∃ z, x = fun i ↦ (w i).eval z)
    {p : MvPolynomial σ R} (hp : ∀ x ∈ S, eval x p = 0) : aeval w p = 0 := by
  let T : Set R := {z | (fun i ↦ (w i).eval z) ∈ S}
  have hT : T.Infinite := fun hT ↦ hS <| (hT.image fun z i ↦ (w i).eval z).subset fun x hx ↦ by
    obtain ⟨z, rfl⟩ := hcurve x hx
    exact ⟨z, hx, rfl⟩
  refine Polynomial.eq_zero_of_infinite_isRoot _ (hT.mono fun z hz ↦ ?_)
  change (aeval w p).eval z = 0
  rw [polynomial_eval_aeval]
  exact hp _ hz

variable {k K σ τ : Type*} [Field k] [Field K] [Algebra k K]

/-- **Polynomial identities along a one-parameter family.** Over an algebraically closed field
`k`, let the class of `s` be a non-zero-divisor modulo `I`, let `I` have positive dimension, and
suppose every point of `U(I)` has the form `(w i (z))ᵢ` for some `z ∈ k`, where `w : σ → k[X]`.
Then every polynomial `p` vanishing on `U(I)`, in particular every `p ∈ I`, satisfies
`aeval w p = 0`.

Positive dimension and regularity make `U(I)` infinite
(`finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero`), and
`aeval_eq_zero_of_infinite` applies. Positive dimension is needed: for `I = (X ())` in one
variable, `s = 1` and `w = X`, the set `U(I) = {0}` is covered, but `p = X ()` gives
`aeval w p = X ≠ 0`. -/
theorem aeval_eq_zero_of_principalOpen_subset_range [IsAlgClosed k] [Finite σ]
    {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (w : σ → Polynomial k)
    (hrange : ∀ x : σ → k, x ∈ zeroLocus k I → aeval x s ≠ 0 →
      ∃ z : k, x = fun i ↦ (w i).eval z)
    {p : MvPolynomial σ k} (hp : ∀ x : σ → k, x ∈ zeroLocus k I → aeval x s ≠ 0 → aeval x p = 0) :
    aeval w p = 0 := by
  have hinf : {x : σ → k | x ∈ zeroLocus k I ∧ aeval x s ≠ 0}.Infinite := fun hfin ↦
    hd.ne' ((finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero hs).mp hfin)
  exact aeval_eq_zero_of_infinite w hinf (fun x hx ↦ hrange x hx.1 hx.2)
    fun x hx ↦ by simpa using hp x hx.1 hx.2

/-- If a one-parameter polynomial graph covers the regular principal open of a positive-dimensional
prime component, every polynomial in the component ideal vanishes on the graph, while the defining
cut stays nonzero after restriction. -/
theorem regular_principalOpen_graph_restriction [IsAlgClosed k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (s : MvPolynomial σ k) (hs : s ∉ I)
    (hd : 0 < (affineHilbertPolynomial I).natDegree) (w : σ → Polynomial k)
    (hrange : ∀ x : σ → k, x ∈ zeroLocus k I → aeval x s ≠ 0 →
      ∃ z : k, x = fun i ↦ (w i).eval z) :
    IsLeftRegular (Ideal.Quotient.mk I s) ∧ (∀ p ∈ I, aeval w p = 0) ∧
      aeval w s ≠ 0 := by
  have hregular : IsLeftRegular (Ideal.Quotient.mk I s) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  have hvanish : ∀ p ∈ I, aeval w p = 0 := by
    intro p hp
    apply aeval_eq_zero_of_principalOpen_subset_range hregular hd w hrange
    intro x hx hxs
    exact hx p hp
  have hinfinite : {x | x ∈ zeroLocus k I ∧ aeval x s ≠ 0}.Infinite := by
    intro hfinite
    have hzero := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero
      hregular).mp hfinite
    omega
  have hnonzero : aeval w s ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := hinfinite.nonempty
    obtain ⟨z, hxw⟩ := hrange x hx.1 hx.2
    have heval : aeval x s = (aeval w s).eval z := by
      rw [polynomial_eval_aeval]
      rw [← hxw]
      simp only [aeval_eq_eval]
    rw [hzero, Polynomial.eval_zero] at heval
    exact hx.2 heval
  exact ⟨hregular, hvanish, hnonzero⟩

end MvPolynomial
