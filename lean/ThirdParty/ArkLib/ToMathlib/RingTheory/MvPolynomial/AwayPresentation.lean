/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/MvPolynomial/AwayPresentation.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 14 of the 22 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Proof changed, X_none_mul_rename_some_sub_one_mem_awayPresentationIdeal: `set_option
  synthInstance.maxHeartbeats 400000` added: instance search on the quotient ring needs more steps
  than the default allows; the last rewrite, by sub_self, became `exact sub_self _`, because `rw`
  did not match `1 - 1`.
-/

import ThirdParty.ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom

/-!
# A presentation of a principal localization and its affine Hilbert function

Let `R` be a commutative ring, `I` an ideal of `MvPolynomial σ R` and `s` a polynomial, and write
`A = MvPolynomial σ R ⧸ I` and `A_s` for the localization of `A` away from the class of `s`. The
algebra map `awayPresentation I s : MvPolynomial (Option σ) R →ₐ[R] A_s` sends the variable
`some i` to the class of `X i` and the new variable `none` to the inverse of the class of `s`. It
is surjective, so `A_s` is the quotient of `MvPolynomial (Option σ) R` by its kernel
`awayPresentationIdeal I s` (`awayPresentationEquiv`).

Over a field `k`, write `H(I, N)` for `affineHilbertFunction I N` and `K` for
`awayPresentationIdeal I s`. With `d = totalDegree s`:

* `H(K, N) ≤ H(I, (d + 1) * N)` for every `I` and `s`. Multiplying a fraction of presentation
  degree at most `N` by `s ^ N` clears the denominators and leaves the class of a polynomial of
  total degree at most `(d + 1) * N`, and multiplication by the unit `s ^ N` is injective.
* `H(I, N) ≤ H(K, N)` when the class of `s` is a non-zero-divisor on `A`. Then `A → A_s` is
  injective and sends the class of `X i` to the class of the variable `some i`, of degree `1`.

So the Hilbert polynomials of `I` and `K` have the same natural degree when `s` is regular on
`A`. A consequence is that a surjection onto `A_s` from the coordinate ring of an ideal `J`
bounds the natural degree for `I` by the natural degree for `J`; in particular a surjection from a
polynomial ring in `τ` bounds it by `Nat.card τ`.

The regularity hypothesis is needed for the lower bounds: for `I = ⊥` in one variable and `s = 0`,
the localization is the zero ring, `K = ⊤`, and `H(K, N) = 0 < N + 1 = H(I, N)`.

## Main statements

* `IsLocalization.Away.algebraMap_injective_of_isLeftRegular`: localizing away from a regular
  element is injective.
* `MvPolynomial.awayPresentation`, `MvPolynomial.awayPresentation_surjective`,
  `MvPolynomial.awayPresentationIdeal`, `MvPolynomial.awayPresentationEquiv`: the presentation.
* `MvPolynomial.affineHilbertFunction_awayPresentationIdeal_le`,
  `MvPolynomial.affineHilbertFunction_le_awayPresentationIdeal`: the two Hilbert-function bounds.
* `MvPolynomial.natDegree_affineHilbertPolynomial_awayPresentationIdeal`: equality of natural
  degrees for a regular `s`.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_surjective_away`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_surjective_away_away`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_away_range`: bounds from localized
  polynomial presentations.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_card_of_surjective_away`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_card_of_adjoin_eq_top_away`: dimension
  bounds from surjections onto a principal localization.
-/

noncomputable section

open Filter

namespace IsLocalization.Away

/-- Localizing away from a regular element `x` is injective: if `x ^ n * a = x ^ n * b` then
`a = b`, because every power of a regular element is regular. -/
theorem algebraMap_injective_of_isLeftRegular {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] {x : R} [IsLocalization.Away x S] (hx : IsLeftRegular x) :
    Function.Injective (algebraMap R S) :=
  IsLocalization.injectiveₛ S fun _ hm ↦ by
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hm
    exact (isLeftRegular_iff_isRegular.mp hx).pow n

end IsLocalization.Away

namespace MvPolynomial

section Presentation

variable {R σ : Type*} [CommRing R] (I : Ideal (MvPolynomial σ R)) (s : MvPolynomial σ R)

/-- The presentation of the localization of `MvPolynomial σ R ⧸ I` away from the class of `s`: the
variable `some i` goes to the class of `X i`, and the new variable `none` goes to the inverse of
the class of `s`. -/
def awayPresentation :
    MvPolynomial (Option σ) R →ₐ[R] Localization.Away (Ideal.Quotient.mk I s) :=
  aeval fun o ↦ o.elim (IsLocalization.Away.invSelf (Ideal.Quotient.mk I s))
    fun i ↦ algebraMap (MvPolynomial σ R ⧸ I) _ (Ideal.Quotient.mk I (X i))

/-- The new variable goes to the inverse of the class of `s`. -/
@[simp]
theorem awayPresentation_X_none :
    awayPresentation I s (X none) = IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) :=
  aeval_X _ _

/-- The variable `some i` goes to the class of `X i`. -/
@[simp]
theorem awayPresentation_X_some (i : σ) :
    awayPresentation I s (X (some i)) =
      algebraMap (MvPolynomial σ R ⧸ I) _ (Ideal.Quotient.mk I (X i)) :=
  aeval_X _ _

/-- A polynomial in the original variables goes to the image of its class in the localization. -/
theorem awayPresentation_rename_some (p : MvPolynomial σ R) :
    awayPresentation I s (rename some p) =
      algebraMap (MvPolynomial σ R ⧸ I) (Localization.Away (Ideal.Quotient.mk I s))
        (Ideal.Quotient.mk I p) := by
  have h : (awayPresentation I s).comp (rename some) =
      (IsScalarTower.toAlgHom R (MvPolynomial σ R ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I s))).comp (Ideal.Quotient.mkₐ R I) := by
    refine algHom_ext fun i ↦ ?_
    simp
  exact DFunLike.congr_fun h p

/-- The presentation is surjective: a fraction `a / s ^ n` with `a` the class of `p` is the image
of `rename some p * X none ^ n`. -/
theorem awayPresentation_surjective : Function.Surjective (awayPresentation I s) := by
  intro z
  obtain ⟨n, a, hz⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk I s) z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨rename some p * X none ^ n, ?_⟩
  rw [map_mul, map_pow, awayPresentation_rename_some, awayPresentation_X_none, ← hz, mul_assoc,
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- The kernel of the presentation: `MvPolynomial (Option σ) R` modulo this ideal is the
localization (`awayPresentationEquiv`). -/
def awayPresentationIdeal : Ideal (MvPolynomial (Option σ) R) :=
  RingHom.ker (awayPresentation I s)

/-- Membership in the presentation ideal is vanishing under the presentation. -/
theorem mem_awayPresentationIdeal {p : MvPolynomial (Option σ) R} :
    p ∈ awayPresentationIdeal I s ↔ awayPresentation I s p = 0 :=
  RingHom.mem_ker

/-- The image of an element of `I` in the original variables lies in the presentation ideal. -/
theorem rename_some_mem_awayPresentationIdeal {p : MvPolynomial σ R} (hp : p ∈ I) :
    rename some p ∈ awayPresentationIdeal I s := by
  rw [mem_awayPresentationIdeal, awayPresentation_rename_some,
    Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

set_option synthInstance.maxHeartbeats 400000 in
/-- The relation saying that the new variable inverts `s` lies in the presentation ideal. -/
theorem X_none_mul_rename_some_sub_one_mem_awayPresentationIdeal :
    X none * rename some s - 1 ∈ awayPresentationIdeal I s := by
  rw [mem_awayPresentationIdeal, map_sub, map_mul, awayPresentation_X_none,
    awayPresentation_rename_some, map_one, mul_comm, IsLocalization.Away.mul_invSelf]
  exact sub_self _

/-- The localization of `MvPolynomial σ R ⧸ I` away from the class of `s` is the quotient of
`MvPolynomial (Option σ) R` by the presentation ideal. -/
def awayPresentationEquiv :
    (MvPolynomial (Option σ) R ⧸ awayPresentationIdeal I s) ≃ₐ[R]
      Localization.Away (Ideal.Quotient.mk I s) :=
  Ideal.quotientKerAlgEquivOfSurjective (awayPresentation_surjective I s)

/-- The equivalence sends the class of `p` to its image under the presentation. -/
@[simp]
theorem awayPresentationEquiv_mk (p : MvPolynomial (Option σ) R) :
    awayPresentationEquiv I s (Ideal.Quotient.mk _ p) = awayPresentation I s p :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ p

end Presentation

section Hilbert

variable {k σ τ : Type*} [Field k]

variable {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}

/-- If the class of `s` is a non-zero-divisor on `MvPolynomial σ k ⧸ I`, the presentation ideal
`K` of the localization away from `s` satisfies `H(I, N) ≤ H(K, N)`.

The map from the quotient to the localization is injective
(`IsLocalization.Away.algebraMap_injective_of_isLeftRegular`) and sends the class of `X i` to the
class of the variable `some i`, which has degree `1`. Regularity is needed: for `I = ⊥` in one
variable and `s = 0`, the localization is zero and `H(K, N) = 0`. -/
theorem affineHilbertFunction_le_awayPresentationIdeal [Finite σ]
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) (N : ℕ) :
    affineHilbertFunction I N ≤ affineHilbertFunction (awayPresentationIdeal I s) N := by
  let g : (MvPolynomial σ k ⧸ I) →ₐ[k]
      (MvPolynomial (Option σ) k ⧸ awayPresentationIdeal I s) :=
    (awayPresentationEquiv I s).symm.toAlgHom.comp (IsScalarTower.toAlgHom k _ _)
  have hg : Function.Injective g := (awayPresentationEquiv I s).symm.injective.comp
    (IsLocalization.Away.algebraMap_injective_of_isLeftRegular hs)
  have hX : ∀ i, g (Ideal.Quotient.mk I (X i)) ∈
      quotientDegreeLE (awayPresentationIdeal I s) 1 := by
    intro i
    have h : g (Ideal.Quotient.mk I (X i)) = Ideal.Quotient.mk _ (X (some i)) := by
      apply (awayPresentationEquiv I s).injective
      simp [g]
    rw [h]
    exact mk_X_mem_quotientDegreeLE _ _
  simpa using affineHilbertFunction_le_of_injective g hg hX N

/-- If the class of `s` is a non-zero-divisor on the quotient, the Hilbert polynomial of `I` has
natural degree at most that of the presentation ideal of the localization away from `s`. -/
theorem natDegree_affineHilbertPolynomial_le_awayPresentationIdeal [Finite σ]
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) :
    (affineHilbertPolynomial I).natDegree ≤
      (affineHilbertPolynomial (awayPresentationIdeal I s)).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_eventually_le_mul (m := 1) (c := 1) one_pos
    (Eventually.of_forall fun N ↦ by
      simpa using affineHilbertFunction_le_awayPresentationIdeal hs N)

end Hilbert

end MvPolynomial
