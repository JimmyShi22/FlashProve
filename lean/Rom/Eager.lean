-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Eager.lean: measure-theoretic lemmas for a random oracle that is sampled all at once
("eagerly"), as a measure on all functions.

ZKCP/Defs.lean samples f ← U(λ), the uniform distribution on all functions {0,1}* → {0,1}^λ, as the
first step of every experiment that has the oracle f (all but `idealExp`). Proofs argue query by
query, with lazily sampled oracles: the answer to a new query is uniform
in the range and independent of all earlier events. This file has lemmas on averages over discrete
distributions, on product spaces and on product measures. Rom/Measure.lean uses
`infinitePi_resample`; Rom/Prefix.lean and Rom/CutDown.lean use `infinitePi_map_reindex`. That eager
and lazy sampling agree is not proved here: Rom/EagerLazy.lean (`eager_eq_lazy`).

Everything is stated on Mathlib's types only: an index type ι (the possible queries; for a family of
oracles, the pairs of an oracle and a point of its domain) and a finite non-empty set D i of
possible answers at each of them. No type of algorithms occurs. The type β of section 0 need not be
countable.

Main statements, by section:
  0  `measurable_expect`, `lintegral_expect`.
  1  `measurable_of_dependsOn`: a function of finitely many values of f is measurable.
     `measurableSet_iUnion_of_dependsOn`: for countable ι, any union of events that each depend on
     finitely many values is measurable.
     `infinitePi_resample`: resampling one value does not change the distribution.
     `infinitePi_map_reindex`: reading f through an injection gives a product-distributed function
     again.
  2  `measurableSet_cylinder`: cylinders are measurable.

Section 1 generalises, from the single oracle of ZKCP/Defs.lean to any family D, lemmas of
ZKCP/Lemmas.lean (resampling), ZKCP/Finite.lean (restriction to a finite set) and
ZKCP/Open.lean (the union lemma is its open-set argument without topology).

Shared with VCV-io (with Rom/EagerLazy.lean): lean/CREDITS.md, section 4.

Notation: `Prob.expect p F` (Prob/Basic.lean): E[ F(a) | a ← p ], the average of a non-negative
(possibly infinite) quantity: `∑' a, p a * F a`.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Logic.Function.DependsOn
import Prob.Count

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace Rom

open Prob (expect pr)

/-! ## 0. Averages over a discrete distribution -/

section Expect

variable {β : Type*}

/-- The average only sees the (countable) support of the distribution. -/
theorem expect_eq_tsum_support (p : PMF β) (F : β → ℝ≥0∞) :
    expect p F = ∑' b : p.support, p b * F b := by
  unfold Prob.expect
  refine (tsum_subtype_eq_of_support_subset fun b hb => ?_).symm
  rw [Function.mem_support] at hb
  exact (p.mem_support_iff b).2 fun h => hb (by simp [h])

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An average of measurable functions is measurable.  The type β may be uncountable: a discrete
distribution has countable support. -/
theorem measurable_expect (p : PMF β) {G : β → Ω → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) :
    Measurable fun ω => expect p fun b => G b ω := by
  haveI : Countable p.support := p.support_countable.to_subtype
  simp only [expect_eq_tsum_support]
  exact Measurable.ennreal_tsum fun b => (hG b).const_mul _

/-- For measurable G b, integral and average may be exchanged (Tonelli), for any type β. -/
theorem lintegral_expect (μ : Measure Ω) (p : PMF β) {G : β → Ω → ℝ≥0∞}
    (hG : ∀ b, Measurable (G b)) :
    ∫⁻ ω, expect p (fun b => G b ω) ∂μ = expect p fun b => ∫⁻ ω, G b ω ∂μ := by
  haveI : Countable p.support := p.support_countable.to_subtype
  simp only [expect_eq_tsum_support]
  rw [lintegral_tsum (f := fun (b : p.support) (ω : Ω) => p b * G b ω)
    fun b => ((hG b).const_mul _).aemeasurable]
  exact tsum_congr fun b => lintegral_const_mul _ (hG b)

/-- On a finite type, the integral against a discrete distribution is its average. -/
theorem lintegral_toMeasure_fintype {C : Type*} [Fintype C] [MeasurableSpace C]
    [MeasurableSingletonClass C] (p : PMF C) (F : C → ℝ≥0∞) :
    ∫⁻ c, F c ∂p.toMeasure = expect p F := by
  rw [lintegral_fintype, Prob.expect, tsum_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton c), mul_comm]

theorem uniform_toMeasure_singleton {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C]
    [MeasurableSingletonClass C] (c : C) :
    (PMF.uniformOfFintype C).toMeasure {c} = (Fintype.card C : ℝ≥0∞)⁻¹ := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton c), PMF.uniformOfFintype_apply]

end Expect

/-! ## 1. The uniform distribution on a product of finite sets: product spaces and product
measures -/

section UniformPi

variable {ι : Type*} {D : ι → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
  [∀ i, MeasurableSpace (D i)] [∀ i, MeasurableSingletonClass (D i)]



omit [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] [∀ i, MeasurableSpace (D i)]
  [∀ i, MeasurableSingletonClass (D i)] in
theorem dependsOn_updateFinset_restrict [DecidableEq ι] {γ : Type*} {g : (∀ i, D i) → γ}
    {s : Finset ι} (hg : DependsOn g s) (x f : ∀ i, D i) :
    g (Function.updateFinset x s (s.restrict f)) = g f :=
  hg fun i hi => by simp [Function.updateFinset, Finset.mem_coe.1 hi]

/-- A function of finitely many coordinates is measurable, whatever its values are (each D i finite
and non-empty). -/
theorem measurable_of_dependsOn {γ : Type*} [MeasurableSpace γ] {g : (∀ i, D i) → γ}
    {s : Finset ι} (hg : DependsOn g s) : Measurable g := by
  classical
  let x : ∀ i, D i := fun i => Classical.arbitrary _
  have e : g = (fun t => g (Function.updateFinset x s t)) ∘ s.restrict :=
    funext fun f => (dependsOn_updateFinset_restrict hg x f).symm
  rw [e]
  exact (measurable_of_finite _).comp (Finset.measurable_restrict s)

omit [∀ i, Nonempty (D i)] in
/-- Any union, also an uncountable one, of sets that each depend on finitely many coordinates is
measurable when there are countably many coordinates.  (Such sets are open in the product topology,
which has a countable base: the cylinders.  The proof writes the union as a union of cylinders.) -/
theorem measurableSet_iUnion_of_dependsOn [Countable ι] {κ : Sort*} (A : κ → Set (∀ i, D i))
    (hA : ∀ k, ∃ s : Finset ι, DependsOn (fun f => f ∈ A k) s) : MeasurableSet (⋃ k, A k) := by
  classical
  let Cyl : (Σ s : Finset ι, ∀ i : s, D i) → Set (∀ i, D i) := fun c => {f | c.1.restrict f = c.2}
  have hCyl : ∀ c, MeasurableSet (Cyl c) := fun c =>
    (Finset.measurable_restrict c.1) (measurableSet_singleton c.2)
  have e : (⋃ k, A k) = ⋃ c ∈ {c | Cyl c ⊆ ⋃ k, A k}, Cyl c := by
    apply Set.Subset.antisymm
    · intro f hf
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hf
      obtain ⟨s, hs⟩ := hA k
      refine Set.mem_iUnion₂.2 ⟨⟨s, s.restrict f⟩, ?_, rfl⟩
      intro f' hf'
      have h : (f' ∈ A k) = (f ∈ A k) := hs fun i hi => congrFun hf' ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨k, h ▸ hk⟩
    · exact Set.iUnion₂_subset fun c hc => hc
  rw [e]
  exact MeasurableSet.biUnion (Set.to_countable _) fun c _ => hCyl c

omit [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] [∀ i, MeasurableSingletonClass (D i)] in
/-- Resampling. In a product of probability measures, drawing f and then replacing its value at one
point i by a fresh value gives the same distribution. -/
theorem infinitePi_resample [DecidableEq ι] (μ : ∀ i, Measure (D i))
    [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    ((Measure.infinitePi μ).prod (μ i)).map (fun p => Function.update p.1 i p.2) =
      Measure.infinitePi μ := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply measurable_update' (MeasurableSet.pi s.countable_toSet fun j _ => ht j)]
  by_cases hi : i ∈ s
  · have h : (fun p : (∀ j, D j) × D i => Function.update p.1 i p.2) ⁻¹' (Set.pi s t)
        = (Set.pi (s.erase i : Finset ι) t) ×ˢ (t i) := by
      ext ⟨f, r⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun j hj => ?_, ?_⟩
        · have := h j hj.2; rwa [Function.update_of_ne hj.1] at this
        · have := h i hi; rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ j hj
        by_cases hji : j = i
        · subst hji; rwa [Function.update_self]
        · rw [Function.update_of_ne hji]; exact h1 j ⟨hji, hj⟩
    rw [h, Measure.prod_prod, Measure.infinitePi_pi _ fun j _ => ht j, mul_comm]
    exact Finset.mul_prod_erase s (fun j => μ j (t j)) hi
  · have h : (fun p : (∀ j, D j) × D i => Function.update p.1 i p.2) ⁻¹' (Set.pi s t)
        = (Set.pi s t) ×ˢ Set.univ := by
      ext ⟨f, r⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Set.mem_univ, and_true]
      refine forall₂_congr fun j hj => ?_
      have hji : j ≠ i := fun e => hi (e ▸ hj)
      rw [Function.update_of_ne hji]
    rw [h, Measure.prod_prod, Measure.infinitePi_pi _ fun j _ => ht j, measure_univ, mul_one]

omit [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] [∀ i, MeasurableSingletonClass (D i)] in
/-- Reindexing. Reading a product-distributed f only at the points e k, for an injective e, gives
the product distribution over k. -/
theorem infinitePi_map_reindex {κ : Type*} (e : κ → ι) (he : Function.Injective e)
    (μ : ∀ i, Measure (D i)) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.infinitePi μ).map (fun f k => f (e k)) = Measure.infinitePi fun k => μ (e k) := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  let t' : ∀ i, Set (D i) := fun i => ⋂ (k : κ) (h : e k = i), (h ▸ t k : Set (D i))
  have ht' : ∀ k, t' (e k) = t k := by
    intro k
    ext d
    simp only [t', Set.mem_iInter]
    constructor
    · intro H; exact H k rfl
    · intro hd k' h
      obtain rfl := he h
      exact hd
  have hmt' : ∀ i, MeasurableSet (t' i) := by
    intro i
    by_cases hi : ∃ k, e k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [ht']; exact ht k
    · have : t' i = Set.univ := by
        ext d
        simp only [t', Set.mem_iInter, Set.mem_univ, iff_true]
        exact fun k h => absurd ⟨k, h⟩ hi
      rw [this]; exact MeasurableSet.univ
  have hpre : (fun (f : ∀ i, D i) k => f (e k)) ⁻¹' (Set.pi s t)
      = Set.pi (s.map ⟨e, he⟩ : Finset ι) t' := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_map,
      Function.Embedding.coeFn_mk, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, ht']
  have hm : Measurable fun (f : ∀ i, D i) (k : κ) => f (e k) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (e k)
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet fun k _ => ht k), hpre,
    Measure.infinitePi_pi _ fun i _ => hmt' i, Finset.prod_map]
  simp only [Function.Embedding.coeFn_mk, ht']

end UniformPi

/-! ## 2. Conditioning on finitely many values: cylinders are measurable -/

section Conditioning

variable {ι : Type*} {D : ι → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
  [∀ i, MeasurableSpace (D i)] [∀ i, MeasurableSingletonClass (D i)]

omit [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] in
theorem measurableSet_cylinder (s : Finset ι) (v : ∀ i, D i) :
    MeasurableSet {f : ∀ i, D i | ∀ i ∈ s, f i = v i} := by
  have h : {f : ∀ i, D i | ∀ i ∈ s, f i = v i} = Set.pi s fun i => {v i} := by
    ext f; simp [Set.mem_pi]
  rw [h]
  exact MeasurableSet.pi s.countable_toSet fun i _ => measurableSet_singleton _

end Conditioning

end Rom
