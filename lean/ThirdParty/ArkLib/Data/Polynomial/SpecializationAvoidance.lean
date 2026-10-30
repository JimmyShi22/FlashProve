/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/SpecializationAvoidance.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 3 of the 7 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.Polynomial.Roots

/-!
# Specialization points that avoid a polynomial's roots

A nonzero polynomial over a domain has at most `natDegree` roots. This file turns that bound into
existence statements for specialization points: from a finite candidate set that is larger than a
forbidden set plus the degree of a polynomial `c`, some candidate is neither forbidden nor a root
of `c`. Taking `c` to be the leading coefficient of `A : R[X][X]` gives a specialization
`A.map (evalRingHom t)` of the coefficient variable that keeps the outer degree of `A`.

## Main statements

* `card_le_natDegree_of_injOn_of_eval_eq_zero`: if a nonzero `p` vanishes at `x w` for every
  `w ∈ s`, and `x` is injective on `s`, then `s.card ≤ p.natDegree`.
* `exists_forall_eval_ne_zero`: finitely many nonzero polynomials have a common nonvanishing
  evaluation over an infinite domain.
* `exists_mem_eval_ne_zero_of_card_add_natDegree_lt_card`: if
  `forbidden.card + c.natDegree < T.card`, some `t ∈ T` is not forbidden and `c.eval t ≠ 0`.
* `exists_mem_map_evalRingHom_ne_zero_of_card_add_natDegree_lt_card`: the degree-preserving
  specialization of the coefficient variable of `A : R[X][X]`, chosen from a finite candidate set.
* `exists_map_evalRingHom_ne_zero_avoiding` and `exists_map_evalRingHom_ne_zero`: the same over an
  infinite domain, with no candidate set.
* `exists_card_le_forall_eval_eq_zero_iff`: a family of polynomials of degree at most `d`, all
  zero outside an index set `s`, has an exceptional set of at most `d * s.card` points outside
  which each member vanishes only if it is the zero polynomial.

The finite candidate forms apply over finite fields, where the infinite forms do not.

## Proof outline

The counting statement maps `s` injectively into the roots of `p` and applies Mathlib's
`card_le_degree_of_subset_roots`. For the avoidance statement, if every non-forbidden candidate
were a root of `c`, the set `T \ forbidden`, of size at least `T.card - forbidden.card`, would
exceed `c.natDegree`. For `A : R[X][X]`, a point `t` with `A.leadingCoeff.eval t ≠ 0` keeps the
leading coefficient under `evalRingHom t`, so `natDegree_map_of_leadingCoeff_ne_zero` applies.
Over an infinite domain, `Infinite.exists_subset_card_eq` supplies a candidate set of any size.

Mathlib's `eq_zero_of_natDegree_lt_card_of_eval_eq_zero` is the contrapositive of the counting
statement for a map that is injective on a whole `Fintype` index. The counting statement here
takes a finset, a map injective on that finset, and concludes a cardinality bound; the avoidance
statements below use it in that form.
-/

namespace Polynomial

variable {R α : Type*} [CommRing R] [IsDomain R]

/-- In an infinite domain, finitely many nonzero polynomials have a common nonvanishing point. -/
theorem exists_forall_eval_ne_zero {ι : Type*} [Infinite R] (T : Finset ι)
    (P : ι → Polynomial R) (hT : ∀ i ∈ T, P i ≠ 0) :
    ∃ center : R, ∀ i ∈ T, (P i).eval center ≠ 0 := by
  classical
  have hprod : ∏ i ∈ T, P i ≠ 0 := Finset.prod_ne_zero_iff.mpr hT
  obtain ⟨center, hc⟩ :
      ∃ center : R, (∏ i ∈ T, P i).eval center ≠ 0 := by
    by_contra! h
    exact hprod (Polynomial.funext (by simpa using h))
  refine ⟨center, fun P hP ↦ ?_⟩
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff] at hc
  exact hc P hP

/-- A nonzero polynomial `p` over a domain vanishes at no more than `p.natDegree` of the points
`x w`, `w ∈ s`, when `x` is injective on `s`.

`hp` is necessary because the zero polynomial vanishes everywhere. `hx` is necessary because a
root hit by several `w` is counted once among the roots. The domain assumption is necessary:
over `ZMod 8`, the polynomial `X ^ 2 - 1` of degree `2` has the four roots `1, 3, 5, 7`. With
`x := id` this is Mathlib's `card_le_degree_of_subset_roots`; with `R := F[X]` and `x := C` it
bounds the number of constants `w` with `p.eval (C w) = 0`. -/
theorem card_le_natDegree_of_injOn_of_eval_eq_zero {p : R[X]} (hp : p ≠ 0) {x : α → R}
    {s : Finset α} (hx : Set.InjOn x s) (hroot : ∀ w ∈ s, p.eval (x w) = 0) :
    s.card ≤ p.natDegree := by
  classical
  rw [← Finset.card_image_of_injOn hx]
  refine card_le_degree_of_subset_roots fun r hr ↦ ?_
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
  exact (mem_roots hp).mpr (hroot w hw)

/-- **Simultaneous non-vanishing of a family.** Let `p i` be polynomials over a domain, with
`(p i).natDegree ≤ d` for `i ∈ s` and `p i = 0` for `i ∉ s`. Some set of at most `d * s.card`
points, the union of the roots of the nonzero `p i`, contains every `z` at which a nonzero member
vanishes: outside it, `(p i).eval z = 0` holds exactly when `p i = 0`.

The index type need not be finite; only the members indexed by `s` can be nonzero. -/
theorem exists_card_le_forall_eval_eq_zero_iff {ι : Type*} (p : ι → R[X]) {d : ℕ}
    (s : Finset ι) (hp : ∀ i ∈ s, (p i).natDegree ≤ d) (hs : ∀ i ∉ s, p i = 0) :
    ∃ exceptional : Finset R, exceptional.card ≤ d * s.card ∧
      ∀ z ∉ exceptional, ∀ i, (p i).eval z = 0 ↔ p i = 0 := by
  classical
  refine ⟨s.biUnion fun i ↦ (p i).roots.toFinset, ?_, fun z hz i ↦ ?_⟩
  · rw [mul_comm]
    refine Finset.card_biUnion_le_card_mul _ _ _ fun i hi ↦ ?_
    exact ((Multiset.toFinset_card_le _).trans (card_roots' _)).trans (hp i hi)
  · refine ⟨fun heval ↦ ?_, fun h ↦ by simp [h]⟩
    by_contra hne
    exact hz (Finset.mem_biUnion.mpr ⟨i, by_contra fun hi ↦ hne (hs i hi),
      Multiset.mem_toFinset.mpr ((mem_roots hne).mpr heval)⟩)

end Polynomial
