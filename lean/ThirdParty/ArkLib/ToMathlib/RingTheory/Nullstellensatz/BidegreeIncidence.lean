/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/Nullstellensatz/BidegreeIncidence.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 15 of the 20 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Proof changed, bidegreeHypersurface_transportPrime: `.le` on a member of minimalPrimes became
  `.1.2`: this Mathlib has no Ideal.IsMinimalPrime.
* Proof changed, bidegreeHypersurface_incidence_off_excluded_sharp: `.isPrime` on a member of
  minimalPrimes became `.1.1`: this Mathlib has no Ideal.IsMinimalPrime.
-/

import Mathlib.LinearAlgebra.Vandermonde
import ThirdParty.ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ThirdParty.ArkLib.ToMathlib.RingTheory.MvPolynomial.CappedBidegree
import ThirdParty.ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence

/-!
# Bidegree hypersurface incidence

Bidegree presentations turn bounded-bidegree equations into linear equations in a polynomial
ring. Incidence bounds on retained components of a presented hypersurface can then be transferred
to the original coordinate ring, together with dimension-sensitive and terminal-component
hypotheses.

## Main statements

* `bidegreeHypersurface_incidence_off_excluded_sharp`: a sharp off-excluded incidence estimate
  for bounded-bidegree hypersurfaces in any finite set of coordinates.
* `bidegreeHypersurface_incidence_off_excluded_hybrid` and
  `bidegreeHypersurface_incidence_off_excluded_hybrid_two`: hybrid incidence estimates using
  dimension-sensitive component budgets.
* `bidegreeHypersurface_incidence_off_excluded_sharp_one` and
  `bidegreeHypersurface_incidence_off_excluded_sharp_two`: one- and two-coordinate degree bounds.

## References

* [BCPZZ26]
-/

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace MvPolynomial

variable {F σ : Type*} [Field F]

private abbrev bidegreeIdeal (a b : ℕ) : Ideal (MvPolynomial (bidegreeExponents σ a b) F) :=
  RingHom.ker (bidegreeMap σ F a b)

private abbrev bidegreeHypersurfaceIdeal (a b : ℕ) (g : MvPolynomial (Option σ) F) :=
  (Ideal.span {g}).comap (bidegreeMap σ F a b)

private theorem bidegreeHypersurfaceIdeal_eq_sup_of_map_eq (a b : ℕ)
    (g : MvPolynomial (Option σ) F) (gl : MvPolynomial (bidegreeExponents σ a b) F)
    (hgl : bidegreeMap σ F a b gl = g) (ha : 0 < a) (hb : 0 < b) :
    bidegreeHypersurfaceIdeal (F := F) (σ := σ) a b g =
      bidegreeIdeal a b ⊔ Ideal.span {gl} := by
  change (Ideal.span {g}).comap (bidegreeMap σ F a b) = _
  conv_lhs => rw [← hgl]
  exact comap_bidegreeMap_span_singleton ha hb

private theorem bidegreeHypersurface_affineDegree_le_one {a b h v : ℕ} (ha : 0 < a)
    (hb : 0 < b) {g : MvPolynomial (Option (Fin 1)) F} (hg0 : g ≠ 0)
    (_hproper : Ideal.span {g} ≠ ⊤) (hg : g ∈ restrictBidegree (Fin 1) F h v) :
    affineDegree ((Ideal.span {g}).comap (bidegreeMap (Fin 1) F a b)) ≤ h * b + v * a := by
  have hbound := affineDegree_comap_bidegreeMap_span_singleton_le ha hb hg0 hg
  simpa [Nat.card_eq_fintype_card, Fintype.card_fin] using hbound

private def bidegreePoint (a b : ℕ) (x : Option σ → F) :
    bidegreeExponents σ a b → F :=
  monomialPoint (bidegreeExponents σ a b) x

private theorem bidegreePoint_injective (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Function.Injective (bidegreePoint (F := F) (σ := σ) a b) :=
  monomialPoint_injective fun i ↦ single_mem_bidegreeExponents ha hb i

private theorem aeval_bidegreePoint (a b : ℕ) (x : Option σ → F)
    (p : MvPolynomial (bidegreeExponents σ a b) F) :
    aeval (bidegreePoint a b x) p = aeval x (bidegreeMap σ F a b p) := by
  change aeval (monomialPoint (bidegreeExponents σ a b) x) p =
    aeval x (bidegreeMap σ F a b p)
  rw [aeval_monomialPoint, ← bidegreeMap_eq_monomialMap]

private theorem aeval_bidegreeLift_iff (a b : ℕ) (x : Option σ → F)
    (p : MvPolynomial (Option σ) F) (hp : p ∈ restrictBidegree σ F a b) :
    aeval (bidegreePoint a b x) (bidegreeLift p hp) = 0 ↔ aeval x p = 0 := by
  rw [aeval_bidegreePoint, bidegreeMap_bidegreeLift]

private theorem mem_zeroLocus_bidegreeHypersurfaceIdeal_iff (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (g : MvPolynomial (Option σ) F) (x : Option σ → F) :
    bidegreePoint a b x ∈ zeroLocus F (bidegreeHypersurfaceIdeal a b g) ↔ aeval x g = 0 := by
  change monomialPoint (bidegreeExponents σ a b) x ∈
      zeroLocus F ((Ideal.span {g}).comap
        (monomialMap F (bidegreeExponents σ a b))) ↔ aeval x g = 0
  rw [monomialPoint_mem_zeroLocus_comap_iff
    (fun i ↦ single_mem_bidegreeExponents ha hb i)]
  rw [mem_zeroLocus_iff_le_ker_aeval]
  simp [RingHom.mem_ker]

private theorem exists_bidegreePoint_of_mem_zeroLocus_bidegreeIdeal (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) {z : bidegreeExponents σ a b → F}
    (hz : z ∈ zeroLocus F (bidegreeIdeal (F := F) (σ := σ) a b)) :
    ∃ x : Option σ → F, bidegreePoint a b x = z := by
  change z ∈ zeroLocus F (RingHom.ker (monomialMap F (bidegreeExponents σ a b))) at hz
  exact exists_monomialPoint_eq_of_mem_zeroLocus_ker
    (fun i ↦ single_mem_bidegreeExponents ha hb i) hz

private def cutsInIdeal {n : ℕ} {τ : Type*} (J : Ideal (MvPolynomial τ F))
    (cuts : Fin n → MvPolynomial τ F) : Set (Fin n) :=
  {i | cuts i ∈ J}

private def agreementIndices {n : ℕ} {τ : Type*} (cuts : Fin n → MvPolynomial τ F)
    (x : τ → F) : Set (Fin n) :=
  {i | aeval x (cuts i) = 0}

private theorem bidegreeHypersurface_transportPrime
    {a b n : ℕ} [Finite σ] (ha : 0 < a) (hb : 0 < b)
    (g s : MvPolynomial (Option σ) F)
    (gl : MvPolynomial (bidegreeExponents σ a b) F)
    (hgl_map : bidegreeMap σ F a b gl = g)
    (sl : MvPolynomial (bidegreeExponents σ a b) F)
    (hsl_map : bidegreeMap σ F a b sl = s)
    (highCuts : List (MvPolynomial (Option σ) F))
    (highCuts' : List (MvPolynomial (bidegreeExponents σ a b) F))
    (hliftHighCuts : ∀ f ∈ highCuts,
      ∃ f' ∈ highCuts', bidegreeMap σ F a b f' = f)
    (cuts : Fin n → MvPolynomial (Option σ) F)
    (cuts' : Fin n → MvPolynomial (bidegreeExponents σ a b) F)
    (hliftCuts : ∀ i, bidegreeMap σ F a b (cuts' i) = cuts i)
    (P : Ideal (MvPolynomial (bidegreeExponents σ a b) F))
    (hPT₀ : P ∈ (bidegreeHypersurfaceIdeal a b g).retainedMinimalPrimes sl)
    (Q : Ideal (MvPolynomial (bidegreeExponents σ a b) F)) (hPQ : P ≤ Q)
    (hQ : Q.IsPrime) (hsQ : sl ∉ Q) (hhighQ : ∀ f ∈ highCuts', f ∈ Q) :
    let K : Ideal (MvPolynomial (Option σ) F) :=
      Q.map (bidegreeMap σ F a b).toRingHom
    RingHom.ker (bidegreeMap σ F a b) ≤ Q ∧ K.IsPrime ∧ s ∉ K ∧ g ∈ K ∧
      (∀ f ∈ highCuts, f ∈ K) ∧
      (affineHilbertPolynomial K).natDegree = (affineHilbertPolynomial Q).natDegree ∧
      cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
  dsimp only
  have hPJ : bidegreeHypersurfaceIdeal a b g ≤ P :=
    ((Ideal.mem_retainedMinimalPrimes).mp hPT₀).1.1.2
  have hbaseJ : RingHom.ker (bidegreeMap σ F a b) ≤ bidegreeHypersurfaceIdeal a b g := by
    rw [bidegreeHypersurfaceIdeal_eq_sup_of_map_eq a b g gl hgl_map ha hb]
    exact le_sup_left
  have hbaseQ : RingHom.ker (bidegreeMap σ F a b) ≤ Q := hbaseJ.trans (hPJ.trans hPQ)
  let K : Ideal (MvPolynomial (Option σ) F) := Q.map (bidegreeMap σ F a b).toRingHom
  have hK : K.IsPrime := Ideal.map_isPrime_of_surjective
    (f := (bidegreeMap σ F a b).toRingHom)
    (bidegreeMap_surjective (a := a) (b := b) ha hb) hbaseQ
  have hcomap : K.comap (bidegreeMap σ F a b).toRingHom = Q := by
    change (Q.map (bidegreeMap σ F a b).toRingHom).comap (bidegreeMap σ F a b).toRingHom = Q
    rw [Ideal.comap_map_of_surjective (bidegreeMap σ F a b).toRingHom
      (bidegreeMap_surjective (a := a) (b := b) ha hb) Q]
    apply sup_eq_left.mpr
    rw [← RingHom.ker_eq_comap_bot]
    exact hbaseQ
  have hsK : s ∉ K := by
    intro hsK
    have hslQ : sl ∈ K.comap (bidegreeMap σ F a b).toRingHom := by
      change bidegreeMap σ F a b sl ∈ K
      rw [hsl_map]
      exact hsK
    rw [hcomap] at hslQ
    exact hsQ hslQ
  have hglJ : gl ∈ bidegreeHypersurfaceIdeal a b g := by
    change bidegreeMap σ F a b gl ∈ Ideal.span {g}
    rw [hgl_map]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hgK : g ∈ K := by
    rw [← hgl_map]
    exact Ideal.mem_map_of_mem (bidegreeMap σ F a b).toRingHom (hPQ (hPJ hglJ))
  have hhighK : ∀ f ∈ highCuts, f ∈ K := by
    intro f hf
    obtain ⟨f', hf', hmap⟩ := hliftHighCuts f hf
    rw [← hmap]
    exact Ideal.mem_map_of_mem (bidegreeMap σ F a b).toRingHom (hhighQ f' hf')
  have hdeg : (affineHilbertPolynomial K).natDegree =
      (affineHilbertPolynomial Q).natDegree := by
    have hQK : Q ≤ K.comap (bidegreeMap σ F a b).toRingHom := by
      intro q hq
      exact Ideal.mem_map_of_mem (bidegreeMap σ F a b).toRingHom hq
    let qmap :
        (MvPolynomial (bidegreeExponents σ a b) F ⧸ Q) →ₐ[F]
          (MvPolynomial (Option σ) F ⧸ K) :=
      Ideal.quotientMapₐ K (bidegreeMap σ F a b) hQK
    have hqinj : Function.Injective qmap := by
      intro x y hxy
      rw [← sub_eq_zero]
      have hz : qmap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := Q) (x - y)
      rw [← hp] at hz ⊢
      change Ideal.Quotient.mk K (bidegreeMap σ F a b p) = 0 at hz
      rw [Ideal.Quotient.eq_zero_iff_mem] at hz ⊢
      have hpQ : p ∈ K.comap (bidegreeMap σ F a b).toRingHom := hz
      rwa [hcomap] at hpQ
    have hqsurj : Function.Surjective qmap := by
      intro y
      obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := K) y
      obtain ⟨q, hq⟩ := bidegreeMap_surjective (a := a) (b := b) ha hb p
      refine ⟨Ideal.Quotient.mk Q q, ?_⟩
      rw [← hp, ← hq]
      exact Ideal.quotientMap_mk (H := hQK)
    let e :
        (MvPolynomial (bidegreeExponents σ a b) F ⧸ Q) ≃ₐ[F]
          (MvPolynomial (Option σ) F ⧸ K) :=
      AlgEquiv.ofBijective qmap ⟨hqinj, hqsurj⟩
    have hfinite : e.symm.toAlgHom.Finite :=
      AlgHom.Finite.of_surjective _ e.symm.surjective
    exact (natDegree_affineHilbertPolynomial_eq_of_finite_of_injective
      e.symm.toAlgHom hfinite e.symm.injective).symm
  have hcutsEq : cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
    ext i
    change cuts i ∈ K ↔ cuts' i ∈ Q
    constructor
    · intro hi
      have hil : cuts' i ∈ K.comap (bidegreeMap σ F a b).toRingHom := by
        change bidegreeMap σ F a b (cuts' i) ∈ K
        rw [hliftCuts i]
        exact hi
      rwa [hcomap] at hil
    · intro hi
      rw [← hliftCuts i]
      exact Ideal.mem_map_of_mem (bidegreeMap σ F a b).toRingHom hi
  exact ⟨hbaseQ, hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩

/-- Let `g` and `s` have bidegree at most `(a, b)`, and let each fixed and agreement equation
have the same bound. If every positive-dimensional prime containing `g` and the fixed equations,
avoiding `s`, and containing at least `L` agreement equations has its principal open locus in
`excluded`, then a finite set of their common zeros outside `excluded`, each agreeing with at least
`A` equations, has cardinality at most the affine degree of the bidegree pullback of `g` times
`((n - L + 1) / (A - L + 1))` raised to the dimension of the hypersurface `g`. -/
theorem bidegreeHypersurface_incidence_off_excluded_sharp
    {a b n A L : ℕ} [Finite σ] (ha : 0 < a) (hb : 0 < b) (hLA : L ≤ A)
    (g s : MvPolynomial (Option σ) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option σ) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree σ F a b)
    (hs : s ∈ restrictBidegree σ F a b)
    (highCuts : List (MvPolynomial (Option σ) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictBidegree σ F a b)
    (cuts : Fin n → MvPolynomial (Option σ) F)
    (hcuts : ∀ i, cuts i ∈ restrictBidegree σ F a b)
    (excluded : Set (Option σ → F))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option σ) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ ({i | cuts i ∈ J}.ncard) →
        {x : Option σ → F | x ∈ zeroLocus F J ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (Option σ → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ ({i | aeval x (cuts i) = 0}.ncard)) :
    (S.card : ℚ) ≤ affineDegree ((Ideal.span {g}).comap (bidegreeMap σ F a b)) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
        (affineHilbertPolynomial (Ideal.span {g})).natDegree := by
  classical
  let J := (Ideal.span {g}).comap (bidegreeMap σ F a b)
  let gl := bidegreeLift (a := a) (b := b) g hg
  let sl := bidegreeLift (a := a) (b := b) s hs
  have hgl_map : bidegreeMap σ F a b gl = g := by
    dsimp only [gl]
    exact bidegreeMap_bidegreeLift (a := a) (b := b) g hg
  have hsl_map : bidegreeMap σ F a b sl = s := by
    dsimp only [sl]
    exact bidegreeMap_bidegreeLift (a := a) (b := b) s hs
  let highCuts' : List (MvPolynomial (bidegreeExponents σ a b) F) :=
    highCuts.attach.map fun f ↦ bidegreeLift (a := a) (b := b) f.1 (hhigh f.1 f.2)
  let cuts' : Fin n → MvPolynomial (bidegreeExponents σ a b) F :=
    fun i ↦ bidegreeLift (a := a) (b := b) (cuts i) (hcuts i)
  let T₀ := J.retainedMinimalPrimes sl
  let S' := S.image (bidegreePoint a b)
  let excluded' : Set (bidegreeExponents σ a b → F) :=
    bidegreePoint a b '' excluded
  let d := (affineHilbertPolynomial (Ideal.span {g})).natDegree
  have hT₀prime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes).mp hP).1.1.1
  have hsum : ∑ P ∈ T₀, affineDegree P ≤ affineDegree J := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (sum_affineDegree_minimalPrimes_comap_bidegreeMap_span_singleton_le ha hb g)
    · intro P hP
      exact Ideal.mem_minimalPrimesFinset.mpr ((Ideal.mem_retainedMinimalPrimes).mp hP).1
    · intro P _ _
      exact affineDegree_nonneg P
  have hdim : ∀ P ∈ T₀, (affineHilbertPolynomial P).natDegree = d := by
    intro P hP
    have hmin := ((Ideal.mem_retainedMinimalPrimes).mp hP).1
    have hbase := natDegree_affineHilbertPolynomial_ker_bidegreeMap
      (k := F) (σ := σ) (a := a) (b := b) ha hb
    have hsource := natDegree_affineHilbertPolynomial_span_singleton_add_one hg0 hproper
    have hglNot : gl ∉ RingHom.ker (bidegreeMap σ F a b) := by
      intro h
      change bidegreeMap σ F a b gl = 0 at h
      dsimp only [gl] at h
      rw [bidegreeMap_bidegreeLift] at h
      exact hg0 h
    have hp := @principalCut_natDegree_affineHilbertPolynomial_add_one
      F (bidegreeExponents σ a b) inferInstance inferInstance
      (RingHom.ker (bidegreeMap σ F a b)) P
      (RingHom.ker_isPrime _) gl hglNot (by
        rw [← bidegreeHypersurfaceIdeal_eq_sup_of_map_eq a b g gl hgl_map ha hb]
        exact hmin)
    dsimp only [d]
    rw [hbase, ← hsource] at hp
    omega
  have hhighDegree : ∀ f ∈ highCuts', f.totalDegree ≤ 1 := by
    intro f hf
    simp only [highCuts', List.mem_map, List.mem_attach] at hf
    obtain ⟨q, _, rfl⟩ := hf
    exact totalDegree_bidegreeLift_le_one (a := a) (b := b) q.1 (hhigh q.1 q.2)
  have hliftHighCuts : ∀ f ∈ highCuts,
      ∃ f' ∈ highCuts', bidegreeMap σ F a b f' = f := by
    intro f hf
    refine ⟨bidegreeLift (a := a) (b := b) f (hhigh f hf), ?_, ?_⟩
    · simp only [highCuts', List.mem_map, List.mem_attach]
      exact ⟨⟨f, hf⟩, trivial, rfl⟩
    · exact bidegreeMap_bidegreeLift (a := a) (b := b) f (hhigh f hf)
  have hliftCuts : ∀ i, bidegreeMap σ F a b (cuts' i) = cuts i := by
    intro i
    dsimp only [cuts']
    exact bidegreeMap_bidegreeLift (a := a) (b := b) (cuts i) (hcuts i)
  have hcardS : S'.card = S.card := Finset.card_image_of_injective _
    (bidegreePoint_injective a b ha hb)
  have hV : ∑ P ∈ T₀, affineDegree P * (1 : ℚ) ^
      (affineHilbertPolynomial P).natDegree ≤ affineDegree J := by
    simpa only [one_pow, mul_one] using hsum
  have hbound := card_le_of_agreement_off_excluded_sharp_of_iteratedRetainedCutFamily
    hT₀prime (fun P hP ↦ (hdim P hP).le) sl (by norm_num) hhighDegree
    (V := affineDegree J) hV cuts' (fun i ↦ totalDegree_bidegreeLift_le_one
      (a := a) (b := b) _ (hcuts i)) (by norm_num) hLA excluded' ?_ S' ?_ ?_
  · rw [hcardS] at hbound
    simpa only [Nat.mul_one, J, d, Fintype.card_fin] using hbound
  · intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ hcutsQ
    let K : Ideal (MvPolynomial (Option σ) F) := Q.map (bidegreeMap σ F a b).toRingHom
    obtain ⟨hbaseQ, hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
      bidegreeHypersurface_transportPrime ha hb g s gl hgl_map sl hsl_map
        highCuts highCuts' hliftHighCuts cuts cuts' hliftCuts P hPT₀ Q hPQ hQ hsQ hhighQ
    have hdK : 0 < (affineHilbertPolynomial K).natDegree := by rw [hdeg]; exact hdQ
    have hcutsCard := congrArg Set.ncard hcutsEq
    have hcutsK : L ≤ (cutsInIdeal K cuts).ncard := by
      rw [hcutsCard]
      exact hcutsQ
    have hsource := hterminal K hK hsK hgK hhighK hdK hcutsK
    intro z hz
    have hzbase : z ∈ zeroLocus F (bidegreeIdeal (F := F) (σ := σ) a b) :=
      zeroLocus_anti_mono hbaseQ hz.1
    obtain ⟨x, rfl⟩ := exists_bidegreePoint_of_mem_zeroLocus_bidegreeIdeal
      a b ha hb hzbase
    have hxK : x ∈ zeroLocus F K := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (bidegreeMap σ F a b).toRingHom
          (bidegreeMap_surjective (a := a) (b := b) ha hb)).mp hp
      change aeval x (bidegreeMap σ F a b q) = 0
      rw [← aeval_bidegreePoint]
      exact hz.1 q hq
    have hxs : aeval x s ≠ 0 := by
      rw [← bidegreeMap_bidegreeLift (a := a) (b := b) s hs, ← aeval_bidegreePoint]
      exact hz.2
    exact ⟨x, hsource ⟨hxK, hxs⟩, rfl⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxJ := (mem_zeroLocus_bidegreeHypersurfaceIdeal_iff a b ha hb g x).2
      (hS x hx).1
    have hxsl : aeval (bidegreePoint a b x) sl ≠ 0 := by
      exact (not_congr (aeval_bidegreeLift_iff a b x s hs)).mpr (hS x hx).2.1
    refine ⟨?_, hxsl, ?_, ?_⟩
    · obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J sl
        (bidegreePoint a b x) hxJ hxsl
      exact ⟨P, hP, hxP⟩
    · intro f hf
      simp only [highCuts', List.mem_map, List.mem_attach] at hf
      obtain ⟨q, _, rfl⟩ := hf
      exact (aeval_bidegreeLift_iff a b x q.1 (hhigh q.1 q.2)).2
        ((hS x hx).2.2.1 q.1 q.2)
    · rintro ⟨y, hy, hxy⟩
      have heq := bidegreePoint_injective a b ha hb hxy
      exact (hS x hx).2.2.2 (heq ▸ hy)
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have heq : agreementIndices cuts' (bidegreePoint a b x) =
        agreementIndices cuts x := by
      ext i
      change aeval (bidegreePoint a b x) (cuts' i) = 0 ↔ aeval x (cuts i) = 0
      exact aeval_bidegreeLift_iff a b x (cuts i) (hcuts i)
    change A ≤ (agreementIndices cuts' (bidegreePoint a b x)).ncard
    rw [heq]
    exact hA x hx

/-- In one coordinate, the sharp bidegree incidence bound is at most the mixed-degree bound
`h * b + v * a` times the first incidence ratio. -/
theorem bidegreeHypersurface_incidence_off_excluded_sharp_one
    {a b h v n A L : ℕ} (ha : 0 < a) (hb : 0 < b) (hLA : L ≤ A)
    (g s : MvPolynomial (Option (Fin 1)) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 1)) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (Fin 1) F h v)
    (hgAB : g ∈ restrictBidegree (Fin 1) F a b)
    (hs : s ∈ restrictBidegree (Fin 1) F a b)
    (highCuts : List (MvPolynomial (Option (Fin 1)) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictBidegree (Fin 1) F a b)
    (cuts : Fin n → MvPolynomial (Option (Fin 1)) F)
    (hcuts : ∀ i, cuts i ∈ restrictBidegree (Fin 1) F a b)
    (excluded : Set (Option (Fin 1) → F))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin 1)) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ ({i | cuts i ∈ J}.ncard) →
        {x : Option (Fin 1) → F | x ∈ zeroLocus F J ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (Option (Fin 1) → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ ({i | aeval x (cuts i) = 0}.ncard)) :
    (S.card : ℚ) ≤ (h * b + v * a : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
  have hc := bidegreeHypersurface_incidence_off_excluded_sharp ha hb hLA
    g s hg0 hproper hgAB hs highCuts hhigh cuts hcuts excluded hterminal S hS hA
  have hd := natDegree_affineHilbertPolynomial_span_singleton_add_one hg0 hproper
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hd
  have hd' : (affineHilbertPolynomial (Ideal.span {g})).natDegree = 1 := by omega
  rw [hd', pow_one] at hc
  have hdegree : affineDegree ((Ideal.span {g}).comap (bidegreeMap (Fin 1) F a b)) ≤
      (h * b + v * a : ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      bidegreeHypersurface_affineDegree_le_one ha hb hg0 hproper hg
  exact hc.trans (mul_le_mul_of_nonneg_right hdegree (by positivity))

end MvPolynomial
