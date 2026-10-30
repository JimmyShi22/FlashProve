-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/Tv.lean: statistical distance on Mathlib's PMF.

Index privacy (`HasIndexPrivacy`, ZKCP/Defs.lean) is stated as "two views are within statistical
distance ζ". The definition of the argument system, in the same file, writes statistical distance as
a supremum over events,

    Δ(X, Y) = sup over all events E of | Pr[X ∈ E] − Pr[Y ∈ E] |,

for distributions given by their event probabilities. Prob/Basic.lean adopts that definition
unchanged (`sd`) and specialises it to discrete distributions (`tv`); this file proves the rules
that game-hopping proofs use. No oracle, field, code or protocol occurs here: everything is stated
on Mathlib's types.

Among the rules (sections 1 to 6): sd is a pseudo-metric, tv a metric with values in [0,1]; map and
bind do not increase tv; tv ≤ Pr[X ≠ Y] for a coupling.
Section 7: hybrid arguments (`tv_hybrid_range`, `tv_hybrid_list`).

sd has the right-hand side of ZKCP.SD of the definition file ZKCP/Defs.lean, letter for letter, for
types in any universe;
sd_eq_zero_of_forall_eq and le_add_of_sd_le are SD_self_eq_zero and le_add_of_SD_le of
ZKCP/Lemmas.lean.

Shared with VCV-io (`tv_hybrid_range`, `sd_hybrid_range`): lean/CREDITS.md, section 4.
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Prob.Count

open scoped ENNReal

namespace Prob

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## 1. Statistical distance of event probabilities -/

section Sd

/-- The working form: the distance is at most z if and only if every event's two probabilities
differ by at most z. -/
theorem sd_le_iff {X Y : Set α → ℝ≥0∞} {z : ℝ≥0∞} :
    sd X Y ≤ z ↔ ∀ E, X E ≤ Y E + z ∧ Y E ≤ X E + z := by
  unfold sd
  simp only [iSup_le_iff, max_le_iff, tsub_le_iff_left]

theorem le_add_sd (X Y : Set α → ℝ≥0∞) (E : Set α) : X E ≤ Y E + sd X Y :=
  ((sd_le_iff.1 le_rfl) E).1

theorem le_add_sd' (X Y : Set α → ℝ≥0∞) (E : Set α) : Y E ≤ X E + sd X Y :=
  ((sd_le_iff.1 le_rfl) E).2

theorem le_add_of_sd_le {X Y : Set α → ℝ≥0∞} {z : ℝ≥0∞} (h : sd X Y ≤ z) (E : Set α) :
    X E ≤ Y E + z :=
  ((sd_le_iff.1 h) E).1

@[simp] theorem sd_self (X : Set α → ℝ≥0∞) : sd X X = 0 :=
  nonpos_iff_eq_zero.1 (sd_le_iff.2 fun _ => ⟨by simp, by simp⟩)

theorem sd_eq_zero_of_forall_eq {X Y : Set α → ℝ≥0∞} (h : ∀ E, X E = Y E) : sd X Y = 0 := by
  have : X = Y := funext h
  rw [this, sd_self]

theorem sd_comm (X Y : Set α → ℝ≥0∞) : sd X Y = sd Y X :=
  iSup_congr fun _ => max_comm _ _

/-- Triangle inequality. -/
theorem sd_triangle (X Y Z : Set α → ℝ≥0∞) : sd X Z ≤ sd X Y + sd Y Z := by
  refine sd_le_iff.2 fun E => ⟨?_, ?_⟩
  · calc X E ≤ Y E + sd X Y := le_add_sd X Y E
      _ ≤ (Z E + sd Y Z) + sd X Y := by gcongr; exact le_add_sd Y Z E
      _ = Z E + (sd X Y + sd Y Z) := by ring
  · calc Z E ≤ Y E + sd Y Z := le_add_sd' Y Z E
      _ ≤ (X E + sd X Y) + sd Y Z := by gcongr; exact le_add_sd' X Y E
      _ = X E + (sd X Y + sd Y Z) := by ring

/-- If all event probabilities are at most 1, so is the distance. -/
theorem sd_le_one {X Y : Set α → ℝ≥0∞} (hX : ∀ E, X E ≤ 1) (hY : ∀ E, Y E ≤ 1) : sd X Y ≤ 1 :=
  sd_le_iff.2 fun E => ⟨(hX E).trans le_add_self, (hY E).trans le_add_self⟩

/-- One side is enough. For two assignments of probabilities in which an event and its complement
add up to 1, it suffices to bound X(E) − Y(E) for all events; the other order follows from the
complement. -/
theorem sd_le_of_forall_le_add {X Y : Set α → ℝ≥0∞} {z : ℝ≥0∞} (hX : ∀ E, X E + X Eᶜ = 1)
    (hY : ∀ E, Y E + Y Eᶜ = 1) (h : ∀ E, X E ≤ Y E + z) : sd X Y ≤ z := by
  refine sd_le_iff.2 fun E => ⟨h E, ?_⟩
  have hfin : X Eᶜ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ((le_add_self).trans (hX E).le)
  have hsum : Y E + X Eᶜ ≤ (X E + z) + X Eᶜ :=
    calc Y E + X Eᶜ ≤ Y E + (Y Eᶜ + z) := by gcongr; exact h Eᶜ
      _ = (Y E + Y Eᶜ) + z := by ring
      _ = (X E + X Eᶜ) + z := by rw [hY, hX]
      _ = (X E + z) + X Eᶜ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 hsum

/-- Images do not increase the distance: events about f(a) are events about a. -/
theorem sd_comap_le (X Y : Set α → ℝ≥0∞) (f : α → β) :
    sd (fun E : Set β => X (f ⁻¹' E)) (fun E : Set β => Y (f ⁻¹' E)) ≤ sd X Y :=
  sd_le_iff.2 fun _ => ⟨le_add_sd X Y _, le_add_sd' X Y _⟩

/-- Weighted sums: the distance of two mixtures with the same weights is at most the mixture of the
distances. -/
theorem sd_tsum_le {ι : Type w} (c : ι → ℝ≥0∞) (X Y : ι → Set α → ℝ≥0∞) :
    sd (fun E => ∑' i, c i * X i E) (fun E => ∑' i, c i * Y i E) ≤ ∑' i, c i * sd (X i) (Y i) := by
  refine sd_le_iff.2 fun E => ⟨?_, ?_⟩
  · rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [← mul_add]
    gcongr
    exact le_add_sd (X i) (Y i) E
  · rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [← mul_add]
    gcongr
    exact le_add_sd' (X i) (Y i) E

/-- Average over a discrete parameter. -/
theorem sd_expect_le (r : PMF γ) (X Y : γ → Set α → ℝ≥0∞) :
    sd (fun E => expect r fun c => X c E) (fun E => expect r fun c => Y c E) ≤
      expect r fun c => sd (X c) (Y c) :=
  sd_tsum_le (fun c => r c) X Y

/-- Average over a parameter drawn from any measure (for instance a random function on an infinite
domain). The event probabilities must be measurable in the parameter; the bound g need not be. -/
theorem sd_lintegral_le {Ω : Type w} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (X Y : Ω → Set α → ℝ≥0∞) (g : Ω → ℝ≥0∞) (hX : ∀ E, AEMeasurable (fun ω => X ω E) μ)
    (hY : ∀ E, AEMeasurable (fun ω => Y ω E) μ) (h : ∀ ω, sd (X ω) (Y ω) ≤ g ω) :
    sd (fun E => ∫⁻ ω, X ω E ∂μ) (fun E => ∫⁻ ω, Y ω E ∂μ) ≤ ∫⁻ ω, g ω ∂μ := by
  refine sd_le_iff.2 fun E => ⟨?_, ?_⟩
  · calc ∫⁻ ω, X ω E ∂μ ≤ ∫⁻ ω, (Y ω E + g ω) ∂μ :=
          MeasureTheory.lintegral_mono fun ω => ((sd_le_iff.1 (h ω)) E).1
      _ = ∫⁻ ω, Y ω E ∂μ + ∫⁻ ω, g ω ∂μ := MeasureTheory.lintegral_add_left' (hY E) g
  · calc ∫⁻ ω, Y ω E ∂μ ≤ ∫⁻ ω, (X ω E + g ω) ∂μ :=
          MeasureTheory.lintegral_mono fun ω => ((sd_le_iff.1 (h ω)) E).2
      _ = ∫⁻ ω, X ω E ∂μ + ∫⁻ ω, g ω ∂μ := MeasureTheory.lintegral_add_left' (hX E) g

end Sd

/-! ## 2. Statistical distance of discrete distributions -/

section TvBasic

/-- tv is sd applied to the event probabilities of two discrete distributions (by definition). -/
theorem sd_pr (p q : PMF α) : sd (pr p) (pr q) = tv p q := rfl

theorem tv_le_iff {p q : PMF α} {z : ℝ≥0∞} :
    tv p q ≤ z ↔ ∀ E, pr p E ≤ pr q E + z ∧ pr q E ≤ pr p E + z :=
  sd_le_iff

/-- What a bound on the distance is used for: an event's probability changes by at most tv p q. -/
theorem pr_le_pr_add_tv (p q : PMF α) (E : Set α) : pr p E ≤ pr q E + tv p q := le_add_sd _ _ E

theorem pr_le_pr_add_tv' (p q : PMF α) (E : Set α) : pr q E ≤ pr p E + tv p q := le_add_sd' _ _ E

theorem pr_le_add_of_tv_le {p q : PMF α} {z : ℝ≥0∞} (h : tv p q ≤ z) (E : Set α) :
    pr p E ≤ pr q E + z :=
  le_add_of_sd_le h E

@[simp] theorem tv_self (p : PMF α) : tv p p = 0 := sd_self _

theorem tv_comm (p q : PMF α) : tv p q = tv q p := sd_comm _ _

/-- Triangle inequality. -/
theorem tv_triangle (p q r : PMF α) : tv p r ≤ tv p q + tv q r := sd_triangle _ _ _

theorem tv_le_one (p q : PMF α) : tv p q ≤ 1 := sd_le_one (pr_le_one p) (pr_le_one q)

theorem tv_ne_top (p q : PMF α) : tv p q ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (tv_le_one p q)

/-- One side is enough: tv p q ≤ z as soon as Pr_p[E] ≤ Pr_q[E] + z for all events E. -/
theorem tv_le_of_forall_pr_le {p q : PMF α} {z : ℝ≥0∞} (h : ∀ E, pr p E ≤ pr q E + z) :
    tv p q ≤ z :=
  sd_le_of_forall_le_add (pr_add_compl p) (pr_add_compl q) h

theorem tv_eq_zero_iff {p q : PMF α} : tv p q = 0 ↔ p = q := by
  constructor
  · intro h
    refine ext_of_pr fun E => le_antisymm ?_ ?_
    · simpa [h] using pr_le_pr_add_tv p q E
    · simpa [h] using pr_le_pr_add_tv' p q E
  · rintro rfl
    exact tv_self p

theorem pr_le_pr_add_tsum_tsub (p q : PMF α) (E : Set α) : pr p E ≤ pr q E + ∑' a, (p a - q a) := by
  rw [pr_eq_tsum_indicator, pr_eq_tsum_indicator, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases h : a ∈ E
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    exact le_add_tsub
  · rw [Set.indicator_of_notMem h]
    exact zero_le _

/-- The event "p gives more weight than q" realises the whole excess of p over q. -/
theorem pr_setOf_lt_eq (p q : PMF α) :
    pr p {a | q a < p a} = pr q {a | q a < p a} + ∑' a, (p a - q a) := by
  rw [pr_eq_tsum_indicator, pr_eq_tsum_indicator, ← ENNReal.tsum_add]
  refine tsum_congr fun a => ?_
  by_cases h : q a < p a
  · have hm : a ∈ {a | q a < p a} := h
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, add_tsub_cancel_of_le h.le]
  · have hm : a ∉ {a | q a < p a} := h
    rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm,
      tsub_eq_zero_of_le (not_lt.1 h), add_zero]

/-- The pointwise formula: tv p q = Σ_a (p(a) − q(a))⁺, the subtraction being truncated at 0. -/
theorem tv_eq_tsum_tsub (p q : PMF α) : tv p q = ∑' a, (p a - q a) := by
  refine le_antisymm (tv_le_of_forall_pr_le (pr_le_pr_add_tsum_tsub p q)) ?_
  have h : ∑' a, (p a - q a) = pr p {a | q a < p a} - pr q {a | q a < p a} := by
    rw [pr_setOf_lt_eq, ENNReal.add_sub_cancel_left (pr_ne_top q _)]
  rw [h]
  exact le_iSup_of_le {a | q a < p a} (le_max_left _ _)

/-- The supremum in the definition is attained, at the event "p gives more weight than q". -/
theorem tv_eq_pr_sub_pr (p q : PMF α) : tv p q = pr p {a | q a < p a} - pr q {a | q a < p a} := by
  rw [tv_eq_tsum_tsub, pr_setOf_lt_eq, ENNReal.add_sub_cancel_left (pr_ne_top q _)]

theorem tv_eq_sum_tsub [Fintype α] (p q : PMF α) : tv p q = ∑ a, (p a - q a) := by
  rw [tv_eq_tsum_tsub, tsum_fintype]

/-- The excess of p over q equals the excess of q over p. -/
theorem tsum_tsub_comm (p q : PMF α) : ∑' a, (p a - q a) = ∑' a, (q a - p a) := by
  rw [← tv_eq_tsum_tsub, ← tv_eq_tsum_tsub, tv_comm]

/-- The usual formula: twice the distance is Σ_a |p(a) − q(a)|. -/
theorem two_mul_tv (p q : PMF α) : 2 * tv p q = ∑' a, ((p a - q a) + (q a - p a)) := by
  rw [ENNReal.tsum_add, ← tsum_tsub_comm p q, ← tv_eq_tsum_tsub, two_mul]

/-- Averages of a quantity bounded by c change by at most c · tv p q. -/
theorem expect_le_expect_add_mul_tv (p q : PMF α) {F : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a, F a ≤ c) :
    expect p F ≤ expect q F + c * tv p q := by
  rw [tv_eq_tsum_tsub, ← ENNReal.tsum_mul_left]
  unfold expect
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  calc p a * F a ≤ (q a + (p a - q a)) * F a := by gcongr; exact le_add_tsub
    _ = q a * F a + (p a - q a) * F a := add_mul _ _ _
    _ ≤ q a * F a + c * (p a - q a) := by rw [mul_comm c]; gcongr; exact h a

/-- Averages of a quantity with values in [0,1] change by at most tv p q. -/
theorem expect_le_expect_add_tv (p q : PMF α) {F : α → ℝ≥0∞} (h : ∀ a, F a ≤ 1) :
    expect p F ≤ expect q F + tv p q := by
  simpa using expect_le_expect_add_mul_tv p q h

open Classical in
theorem tv_pure_pure (a b : α) : tv (PMF.pure a) (PMF.pure b) = if a = b then 0 else 1 := by
  by_cases h : a = b
  · simp [h]
  · rw [if_neg h]
    refine le_antisymm (tv_le_one _ _) ?_
    have h1 := pr_le_pr_add_tv (PMF.pure a) (PMF.pure b) {a}
    rw [pr_pure, pr_pure] at h1
    simpa [Ne.symm h] using h1

end TvBasic

/-! ## 3. Data processing -/

section DataProcessing

/-- A function of the sample does not increase the distance. -/
theorem tv_map_le (p q : PMF α) (f : α → β) : tv (p.map f) (q.map f) ≤ tv p q := by
  have hp : pr (p.map f) = fun E => pr p (f ⁻¹' E) := funext (pr_map p f)
  have hq : pr (q.map f) = fun E => pr q (f ⁻¹' E) := funext (pr_map q f)
  unfold tv
  rw [hp, hq]
  exact sd_comap_le (pr p) (pr q) f

/-- An injective function of the sample keeps the distance. -/
theorem tv_map_of_injective (p q : PMF α) {f : α → β} (hf : Function.Injective f) :
    tv (p.map f) (q.map f) = tv p q := by
  refine le_antisymm (tv_map_le p q f) (tv_le_of_forall_pr_le fun E => ?_)
  have h := pr_le_pr_add_tv (p.map f) (q.map f) (f '' E)
  rwa [pr_map, pr_map, Set.preimage_image_eq E hf] at h

/-- A randomised function of the sample does not increase the distance. -/
theorem tv_bind_left_le (p q : PMF α) (f : α → PMF β) : tv (p.bind f) (q.bind f) ≤ tv p q :=
  tv_le_of_forall_pr_le fun E => by
    rw [pr_bind, pr_bind]
    exact expect_le_expect_add_tv p q fun a => pr_le_one (f a) E

/-- No randomised test D tells p from q with advantage more than tv p q. -/
theorem pr_bind_le_pr_bind_add_tv (p q : PMF α) (D : α → PMF β) (E : Set β) :
    pr (p.bind D) E ≤ pr (q.bind D) E + tv p q :=
  (pr_le_pr_add_tv _ _ E).trans (by gcongr; exact tv_bind_left_le p q D)

end DataProcessing

/-! ## 4. Averages over a parameter -/

section Average

/-- Average over a parameter: if both experiments start with the same draw c ← r, their distance is
at most the average over c of the distance of what follows. -/
theorem tv_bind_right_le (r : PMF γ) (f g : γ → PMF α) :
    tv (r.bind f) (r.bind g) ≤ expect r fun c => tv (f c) (g c) := by
  have hf : pr (r.bind f) = fun E => expect r fun c => pr (f c) E := funext (pr_bind r f)
  have hg : pr (r.bind g) = fun E => expect r fun c => pr (g c) E := funext (pr_bind r g)
  unfold tv
  rw [hf, hg]
  exact sd_expect_le r (fun c => pr (f c)) (fun c => pr (g c))

/-- A bound on the distance that holds for every value of the parameter holds for the whole. -/
theorem tv_bind_right_le_of_forall (r : PMF γ) (f g : γ → PMF α) {z : ℝ≥0∞}
    (h : ∀ c ∈ r.support, tv (f c) (g c) ≤ z) : tv (r.bind f) (r.bind g) ≤ z :=
  (tv_bind_right_le r f g).trans (expect_le_of_forall_le r h)

/-- If for every parameter outside B the distance is at most z, the distance of the two experiments
is at most Pr[B] + z. -/
theorem tv_bind_right_le_add (r : PMF γ) (f g : γ → PMF α) (B : Set γ) {z : ℝ≥0∞}
    (h : ∀ c ∈ r.support, c ∉ B → tv (f c) (g c) ≤ z) : tv (r.bind f) (r.bind g) ≤ pr r B + z :=
  (tv_bind_right_le r f g).trans (expect_le_pr_add r _ B (fun c => tv_le_one (f c) (g c)) h)

/-- The distance is at most the probability that the two continuations differ at the parameter. -/
theorem tv_bind_right_le_pr_ne (r : PMF γ) (f g : γ → PMF α) :
    tv (r.bind f) (r.bind g) ≤ pr r {c | f c ≠ g c} := by
  have h := tv_bind_right_le_add r f g {c | f c ≠ g c} (z := 0) fun c _ hc => by
    have : f c = g c := not_not.1 hc
    rw [this, tv_self]
  simpa using h

/-- Both steps change, first draw and continuation: the distance is at most tv p q plus the average
over q of the distances of the continuations. -/
theorem tv_bind_le (p q : PMF γ) (f g : γ → PMF α) :
    tv (p.bind f) (q.bind g) ≤ tv p q + expect q fun c => tv (f c) (g c) :=
  (tv_triangle _ (q.bind f) _).trans (add_le_add (tv_bind_left_le p q f) (tv_bind_right_le q f g))

theorem tv_bind_le' (p q : PMF γ) (f g : γ → PMF α) :
    tv (p.bind f) (q.bind g) ≤ tv p q + expect p fun c => tv (f c) (g c) := by
  rw [add_comm]
  exact (tv_triangle _ (p.bind g) _).trans
    (add_le_add (tv_bind_right_le p f g) (tv_bind_left_le p q g))

theorem tv_bind_le_of_forall
    (p q : PMF γ) (f g : γ → PMF α) {z : ℝ≥0∞} (h : ∀ c, tv (f c) (g c) ≤ z) :
    tv (p.bind f) (q.bind g) ≤ tv p q + z :=
  (tv_bind_le p q f g).trans (by gcongr; exact expect_le_of_forall_le q fun c _ => h c)

/-- Average over a uniform parameter. -/
theorem tv_unif_bind_le {C : Type w} [Fintype C] [Nonempty C] (f g : C → PMF α) :
    tv ((unif C).bind f) ((unif C).bind g) ≤ (∑ c, tv (f c) (g c)) / Fintype.card C := by
  rw [← expect_unif]
  exact tv_bind_right_le (unif C) f g

/-- If the parameter is part of the view, the average is exact: the distance of (c, f c) and (c, g
c), with c ← r, equals the average over c of the distance of f c and g c. -/
theorem tv_joint_eq (r : PMF γ) (f g : γ → PMF α) :
    tv (joint r f) (joint r g) = expect r fun c => tv (f c) (g c) := by
  rw [tv_eq_tsum_tsub]
  unfold expect
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun c => ?_
  change _ = r c * tv (f c) (g c)
  rw [tv_eq_tsum_tsub, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => ?_
  rw [joint_apply, joint_apply, ENNReal.mul_sub fun _ _ => PMF.apply_ne_top r c]

/-- Independent pairs: the distance is at most the sum of the distances of the components. -/
theorem tv_prod_le (p p' : PMF α) (q q' : PMF β) :
    tv (prod p q) (prod p' q') ≤ tv p p' + tv q q' := by
  unfold prod
  exact tv_bind_le_of_forall p p' _ _ fun a => tv_map_le q q' _

theorem tv_prod_left (p p' : PMF α) (q : PMF β) : tv (prod p q) (prod p' q) = tv p p' := by
  refine le_antisymm (by simpa using tv_prod_le p p' q q) ?_
  have h := tv_map_le (prod p q) (prod p' q) Prod.fst
  rwa [map_fst_prod, map_fst_prod] at h

theorem tv_prod_right (p : PMF α) (q q' : PMF β) : tv (prod p q) (prod p q') = tv q q' := by
  refine le_antisymm (by simpa using tv_prod_le p p q q') ?_
  have h := tv_map_le (prod p q) (prod p q') Prod.snd
  rwa [map_snd_prod, map_snd_prod] at h

end Average

/-! ## 5. Coupling -/

section Coupling

/-- Coupling lemma. Two quantities X and Y computed in one experiment r are within Pr[X ≠ Y]. -/
theorem tv_map_map_le_pr_ne (r : PMF γ) (X Y : γ → α) :
    tv (r.map X) (r.map Y) ≤ pr r {c | X c ≠ Y c} :=
  tv_le_of_forall_pr_le fun E => by
    rw [pr_map, pr_map]
    refine pr_le_add r fun c hc => ?_
    by_cases h : X c = Y c
    · left
      change Y c ∈ E
      rw [← h]
      exact hc
    · right
      exact h

/-- Coupling lemma, for a joint distribution of two samples: the marginals are within Pr[first ≠
second]. -/
theorem tv_le_pr_ne (c : PMF (α × α)) :
    tv (c.map Prod.fst) (c.map Prod.snd) ≤ pr c {x | x.1 ≠ x.2} :=
  tv_map_map_le_pr_ne c Prod.fst Prod.snd

/-- The coupling lemma in the form in which it is used: any coupling of p and q bounds their
distance. -/
theorem tv_le_of_coupling {p q : PMF α} (c : PMF (α × α))
    (h₁ : c.map Prod.fst = p) (h₂ : c.map Prod.snd = q) :
    tv p q ≤ pr c {x | x.1 ≠ x.2} := by
  rw [← h₁, ← h₂]
  exact tv_le_pr_ne c

end Coupling

/-! ## 6. Identical until bad -/

section UntilBad

/-- If p gives no more weight than q to any point outside B, then tv p q ≤ Pr_p[B]. -/
theorem tv_le_pr_of_le_off (p q : PMF α) (B : Set α) (h : ∀ a, a ∉ B → p a ≤ q a) :
    tv p q ≤ pr p B := by
  rw [tv_eq_tsum_tsub, pr_eq_tsum_indicator]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ B
  · rw [Set.indicator_of_mem ha]
    exact tsub_le_self
  · rw [tsub_eq_zero_of_le (h a ha)]
    exact zero_le _

/-- Two distributions that agree outside B give B the same probability. -/
theorem pr_eq_of_eq_off (p q : PMF α) (B : Set α) (h : ∀ a, a ∉ B → p a = q a) :
    pr p B = pr q B := by
  have hc : pr p Bᶜ = pr q Bᶜ := by
    rw [pr_eq_tsum_indicator, pr_eq_tsum_indicator]
    refine tsum_congr fun a => ?_
    by_cases ha : a ∈ B
    · have hn : a ∉ Bᶜ := fun hn => hn ha
      rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]
    · rw [Set.indicator_of_mem (show a ∈ Bᶜ from ha),
        Set.indicator_of_mem (show a ∈ Bᶜ from ha), h a ha]
  have hp := pr_compl p Bᶜ
  have hq := pr_compl q Bᶜ
  rw [compl_compl] at hp hq
  rw [hp, hq, hc]

/-- Identical until bad, for an arbitrary bad event B: two distributions that agree outside B are
within Pr[B]. -/
theorem tv_le_pr_of_eq_off (p q : PMF α) (B : Set α) (h : ∀ a, a ∉ B → p a = q a) :
    tv p q ≤ pr p B :=
  tv_le_pr_of_le_off p q B fun a ha => (h a ha).le




/-- The hypothesis of "identical until bad" (`tv_le_pr_of_eq_off`) at B = {x | x.2 = true} (the
second component is the flag), stated for events: it is enough that every event of the form "the
value lies in E and the flag is down" has the same probability in both experiments. -/
theorem eq_flag_down_of_forall_pr_eq (p q : PMF (α × Bool))
    (h : ∀ E : Set α, pr p {x | x.1 ∈ E ∧ x.2 = false} = pr q {x | x.1 ∈ E ∧ x.2 = false}) (a : α) :
    p (a, false) = q (a, false) := by
  have hs : {x : α × Bool | x.1 ∈ ({a} : Set α) ∧ x.2 = false} = {(a, false)} := by
    ext x
    obtain ⟨a', b⟩ := x
    simp
  have h' := h {a}
  rwa [hs, pr_singleton, pr_singleton] at h'

end UntilBad

/-! ## 7. Hybrid arguments -/

section Hybrid

/-- Hybrid argument over a sequence h 0, h 1, .., h n. -/
theorem tv_hybrid_range (h : ℕ → PMF α) (n : ℕ) :
    tv (h 0) (h n) ≤ ∑ i ∈ Finset.range n, tv (h i) (h (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (tv_triangle _ (h n) _).trans (by gcongr)

/-- Hybrid argument with the same bound z for each of the n steps. -/
theorem tv_hybrid_range_le_mul
    (h : ℕ → PMF α) (n : ℕ) {z : ℝ≥0∞} (hz : ∀ i, i < n → tv (h i) (h (i + 1)) ≤ z) :
    tv (h 0) (h n) ≤ n * z :=
  (tv_hybrid_range h n).trans
    ((Finset.sum_le_sum fun i hi => hz i (Finset.mem_range.1 hi)).trans (by simp))

/-- Hybrid argument over a list: the distance from the first to the last entry of p :: l is at most
the sum of the distances of neighbours. -/
theorem tv_hybrid_list (p : PMF α) (l : List (PMF α)) :
    tv p ((p :: l).getLast (List.cons_ne_nil p l)) ≤ (List.zipWith tv (p :: l) l).sum := by
  induction l generalizing p with
  | nil => simp
  | cons q l ih =>
    rw [List.getLast_cons (List.cons_ne_nil q l), List.zipWith_cons_cons, List.sum_cons]
    exact (tv_triangle p q _).trans (by gcongr; exact ih q)


/-- `tv_hybrid_range` for event probabilities. -/
theorem sd_hybrid_range (h : ℕ → Set α → ℝ≥0∞) (n : ℕ) :
    sd (h 0) (h n) ≤ ∑ i ∈ Finset.range n, sd (h i) (h (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (sd_triangle _ (h n) _).trans (by gcongr)

end Hybrid

end Prob
