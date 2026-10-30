/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 2 of the 27 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree
import ThirdParty.ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap

/-!
# Polynomials of bounded bidegree with a capped variable

As in `ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree`, split the variables of
`MvPolynomial (Option σ) R` into `none` and the variables `some j`. Fix `i : σ`. The exponents
`cappedBidegreeExponents σ i a b c` are those of bidegree at most `(a, b)` whose exponent in
`some i` is at most `c`, and the polynomials supported on them form the submodule
`restrictCappedBidegree σ R i a b c`. For `b ≤ c` the cap is no condition, and these are the
exponents of bidegree at most `(a, b)`.

The three bounds add under addition of exponents, so the capped polynomials are closed under
multiplication, and the monomial map `monomialMap R (cappedBidegreeExponents σ i a b c)` sends
polynomials of total degree at most `N` to polynomials with bounds `(a * N, b * N, c * N)`. For
positive `a`, `b` and `c` the exponents `Finsupp.single v 1` are capped exponents, so the monomial
map is surjective.

Splitting off the `none`-coordinate identifies the capped exponents with pairs of an integer in
`[0, a]` and a capped exponent in `cappedDegreeExponents σ i b c`. For `σ = Fin 2`, `i = 1` and
`c ≤ b` their convex hull is the prism `[0, a] × T` over the truncated triangle `T` of
`cappedDegreeExponents (Fin 2) 1 b c`, and `cappedBidegreeMixedVolume h j r a b c` is the mixed
volume of one prism for `(h, j, r)` and two prisms for `(a, b, c)`, normalized so that the mixed
volume of a prism with itself is `3!` times its volume. It bounds the affine degree of the pullback
of a hypersurface with bounds `(h, j, r)` along the monomial map
(`ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedBidegree`).

The bidegree map `bidegreeMap σ R a b` is the monomial map of `bidegreeExponents σ a b`, and the
exponents `Finsupp.single v 1` are exponents of bidegree at most `(a, b)` for positive `a` and `b`,
so the statements on points in `ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap` apply to it.

## Main statements

* `MvPolynomial.bidegreeMap_eq_monomialMap`, `MvPolynomial.single_mem_bidegreeExponents`: the
  bidegree map as a surjective monomial map.
* `MvPolynomial.cappedBidegreeExponents`, `MvPolynomial.restrictCappedBidegree`: the capped
  exponents and polynomials.
* `MvPolynomial.mem_restrictCappedBidegree_of_mem_restrictBidegree`: a bidegree rectangle and a
  separate variable-degree bound give a capped bidegree bound.
* `MvPolynomial.mul_mem_restrictCappedBidegree`: the bounds add under multiplication.
* `MvPolynomial.monomialMap_mem_restrictCappedBidegree`: total degree `N` maps to bounds
  `(a * N, b * N, c * N)`.
* `MvPolynomial.monomialMap_cappedBidegreeExponents_surjective`: the monomial map is surjective
  for positive bounds.
* `MvPolynomial.ncard_cappedBidegreeExponents`, `MvPolynomial.finrank_restrictCappedBidegree`: the
  count `(a + 1) * (cappedDegreeExponents σ i b c).ncard`.
* `MvPolynomial.cappedBidegreeMixedVolume`: the mixed volume of the prisms, with its
  monotonicity.
-/

noncomputable section

open scoped Pointwise

namespace MvPolynomial

variable {σ R : Type*}

section BidegreeMap

/-- `bidegreeMap σ R a b` is the monomial map of the exponents of bidegree at most `(a, b)`. -/
theorem bidegreeMap_eq_monomialMap [CommSemiring R] (a b : ℕ) :
    bidegreeMap σ R a b = monomialMap R (bidegreeExponents σ a b) :=
  rfl

/-- For positive `a` and `b`, the exponent `Finsupp.single v 1` has bidegree at most `(a, b)`. -/
theorem single_mem_bidegreeExponents {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (v : Option σ) :
    Finsupp.single v 1 ∈ bidegreeExponents σ a b := by
  rw [mem_bidegreeExponents]
  cases v with
  | none => simp [Finsupp.some_single_none]; omega
  | some j => simp [Finsupp.some_single_some]; omega

end BidegreeMap

section Exponents

variable {i : σ} {a b c : ℕ}

end Exponents

section Submodule

variable [CommSemiring R] {i : σ} {a b c : ℕ}

end Submodule

section MixedVolume

variable {h j r h' j' r' a b c a' b' c' : ℕ}

end MixedVolume

end MvPolynomial
