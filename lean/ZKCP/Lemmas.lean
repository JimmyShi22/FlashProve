-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/Lemmas.lean: facts about the definitions of ZKCP/Defs.lean.

Nothing here is part of those definitions; the file shows of `U` and `Pr` that they mean what their
comments say:

  `U_cylinder`           U(λ) gives (2^λ)^(-n) to every condition that fixes the values at n
                         distinct points.
  `measurable_prob_run`  For an event that does not mention f, the integrand of `Pr` is measurable
                         (so ∫⁻ is the true average).
  `PrFrom_pure`, `PrFrom_sample`, `PrFrom_query`
                         The rules of lazy sampling for such a `Pr`.
  `Pr_eq_lazy`           f ← U(λ) sampled at once = f sampled lazily, for every oracle computation
                         and every event that does not mention f.
-/
import ZKCP.Defs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {α β : Type}

instance : IsProbabilityMeasure (U lam) := by unfold U; infer_instance

/-! ### Discrete distributions: expectation and event probability -/

/-- E[ F(a) | a ← p ]. -/
def expect (p : PMF α) (F : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * F a

lemma expect_pure (a : α) (F : α → ℝ≥0∞) : expect (PMF.pure a) F = F a := by
  classical
  unfold expect
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]

lemma expect_bind (p : PMF α) (g : α → PMF β) (F : β → ℝ≥0∞) :
    expect (p.bind g) F = expect p fun a => expect (g a) F := by
  unfold expect
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  simp only [mul_assoc]

lemma expect_map (p : PMF α) (h : α → β) (F : β → ℝ≥0∞) :
    expect (p.map h) F = expect p fun a => F (h a) := by
  change expect (p.bind (PMF.pure ∘ h)) F = _
  rw [expect_bind]; simp [expect_pure]

lemma expect_uniform [Fintype α] [Nonempty α] (F : α → ℝ≥0∞) :
    expect (PMF.uniformOfFintype α) F = ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * F a := by
  unfold expect; rw [tsum_fintype]; simp [PMF.uniformOfFintype_apply]

lemma expect_mono (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a, F a ≤ G a) : expect p F ≤ expect p G :=
  ENNReal.tsum_le_tsum fun a => by gcongr; exact h a

lemma expect_congr (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a, F a = G a) : expect p F = expect p G := by
  have : F = G := funext h
  rw [this]

lemma expect_add (p : PMF α) (F G : α → ℝ≥0∞) :
    expect p (fun a => F a + G a) = expect p F + expect p G := by
  unfold expect; simp only [mul_add]; exact ENNReal.tsum_add

lemma expect_const (p : PMF α) (c : ℝ≥0∞) : expect p (fun _ => c) = c := by
  unfold expect; rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

open Classical in
lemma prob_eq_expect (p : PMF α) (E : Set α) :
    prob p E = expect p fun a => if a ∈ E then 1 else 0 := by
  unfold prob expect
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun a => ?_
  by_cases h : a ∈ E <;> simp [h]

open Classical in
lemma prob_pure (a : α) (E : Set α) : prob (PMF.pure a) E = if a ∈ E then 1 else 0 := by
  rw [prob_eq_expect, expect_pure]

lemma prob_bind (p : PMF α) (g : α → PMF β) (E : Set β) :
    prob (p.bind g) E = expect p fun a => prob (g a) E :=
  PMF.toOuterMeasure_bind_apply p g E

lemma prob_le_one (p : PMF α) (E : Set α) : prob p E ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc _ ≤ expect p (fun _ => 1) := expect_mono p fun a => by split_ifs <;> simp
    _ = 1 := expect_const p 1

lemma prob_mono (p : PMF α) {E F : Set α} (h : E ⊆ F) : prob p E ≤ prob p F :=
  p.toOuterMeasure.mono h

lemma prob_add_compl (p : PMF α) (E : Set α) : prob p E + prob p Eᶜ = 1 := by
  classical
  rw [prob_eq_expect, prob_eq_expect, ← expect_add]
  calc _ = expect p (fun _ => 1) := expect_congr p fun a => by by_cases h : a ∈ E <;> simp [h]
    _ = 1 := expect_const p 1

/-! ### Running oracle computations -/

@[simp] lemma bind_eq (c : OComp lam α) (g : α → OComp lam β) : (c >>= g) = c.bind g := rfl
@[simp] lemma pure_eq (a : α) : (Pure.pure a : OComp lam α) = OComp.pure a := rfl

lemma run_bind (f : Oracle lam) (c : OComp lam α) (g : α → OComp lam β) :
    (c.bind g).run f = (c.run f).bind fun a => (g a).run f := by
  induction c with
  | pure a => simp [OComp.bind, OComp.run]
  | query q k ih => simp only [OComp.bind, OComp.run]; exact ih _
  | sample n k ih => simp only [OComp.bind, OComp.run, ih, PMF.bind_bind]

/-- The integrand of Pr, for an event that does not mention f, is a measurable function of the
oracle. -/
lemma measurable_prob_run (m : OComp lam α) (E : Set α) :
    Measurable fun f : Oracle lam => prob (m.run f) E := by
  induction m with
  | pure a => simp only [OComp.run]; exact measurable_const
  | query q k ih =>
    have h : Measurable fun p : Oracle lam × Digest lam => prob ((k p.2).run p.1) E :=
      measurable_from_prod_countable_left fun r => ih r
    exact h.comp (measurable_id.prodMk (measurable_pi_apply q))
  | sample n k ih =>
    simp only [OComp.run, prob_bind, expect_uniform]
    exact Finset.measurable_sum _ fun r _ => (ih r).const_mul _

lemma Pr_mono (m : OComp lam α) {E F : Set α} (h : E ⊆ F) : Pr m (fun _ => E) ≤ Pr m (fun _ => F) :=
  lintegral_mono fun _ => prob_mono _ h

lemma Pr_le_one (m : OComp lam α) (E : Oracle lam → Set α) : Pr m E ≤ 1 := by
  calc Pr m E ≤ ∫⁻ _, 1 ∂(U lam) := lintegral_mono fun _ => prob_le_one _ _
    _ = 1 := by simp

/-! ### U(λ) is what it should be -/

/-- The defining property of the uniform distribution on functions: any condition
f(q) = v(q) for all q in a finite set s of strings has probability (2^λ)^(-|s|). -/
theorem U_cylinder (s : Finset Str) (v : Str → Digest lam) :
    U lam {f | ∀ q ∈ s, f q = v q} = ((2 ^ lam : ℕ) : ℝ≥0∞)⁻¹ ^ s.card := by
  have h : {f : Oracle lam | ∀ q ∈ s, f q = v q} = Set.pi s fun q => {v q} := by
    ext f; simp [Set.mem_pi]
  rw [h, U, Measure.infinitePi_pi _ fun q _ => MeasurableSet.singleton _]
  simp [PMF.uniformOfFintype_apply]

/-- Resampling one point of the oracle does not change its distribution. -/
lemma U_resample (q : Str) :
    ((U lam).prod (PMF.uniformOfFintype (Digest lam)).toMeasure).map
      (fun p => Function.update p.1 q p.2) = U lam := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply measurable_update' (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  by_cases hq : q ∈ s
  · have h : (fun p : Oracle lam × Digest lam => Function.update p.1 q p.2) ⁻¹' (Set.pi s t)
        = (Set.pi (s.erase q : Finset Str) t) ×ˢ (t q) := by
      ext ⟨f, r⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨fun i hi => ?_, ?_⟩
        · have := h i hi.2; rwa [Function.update_of_ne hi.1] at this
        · have := h q hq; rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ i hi
        by_cases hiq : i = q
        · subst hiq; rwa [Function.update_self]
        · rw [Function.update_of_ne hiq]; exact h1 i ⟨hiq, hi⟩
    rw [h, Measure.prod_prod, U, Measure.infinitePi_pi _ fun i _ => ht i, mul_comm]
    exact Finset.mul_prod_erase s (fun i => (PMF.uniformOfFintype (Digest lam)).toMeasure (t i)) hq
  · have h : (fun p : Oracle lam × Digest lam => Function.update p.1 q p.2) ⁻¹' (Set.pi s t)
        = (Set.pi s t) ×ˢ Set.univ := by
      ext ⟨f, r⟩
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Set.mem_univ, and_true]
      refine forall₂_congr fun i hi => ?_
      have hiq : i ≠ q := fun e => hq (e ▸ hi)
      rw [Function.update_of_ne hiq]
    rw [h, Measure.prod_prod, U, Measure.infinitePi_pi _ fun i _ => ht i, measure_univ, mul_one]

lemma lintegral_U_resample (q : Str) {g : Oracle lam → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ f, g f ∂(U lam) = ∑ r : Digest lam, (Fintype.card (Digest lam) : ℝ≥0∞)⁻¹ *
      ∫⁻ f, g (Function.update f q r) ∂(U lam) := by
  conv_lhs => rw [← U_resample (lam := lam) q]
  rw [lintegral_map hg measurable_update',
    lintegral_prod_symm (fun p : Oracle lam × Digest lam => g (Function.update p.1 q p.2))
      (hg.comp measurable_update').aemeasurable, lintegral_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), PMF.uniformOfFintype_apply,
    mul_comm]

/-! ### Lazy sampling -/

/-- A partial table of oracle values already fixed. -/
abbrev Cache (lam : ℕ) : Type := Str → Option (Digest lam)

/-- The oracle that answers from the table c where c is defined and from f elsewhere. -/
def over (c : Cache lam) (f : Oracle lam) : Oracle lam := fun q => (c q).getD (f q)

lemma over_none (f : Oracle lam) : over (fun _ => none) f = f := rfl

lemma measurable_over (c : Cache lam) : Measurable (over c) := by
  refine measurable_pi_iff.2 fun q => ?_
  unfold over
  cases c q with
  | none => simpa using measurable_pi_apply q
  | some r => simp

/-- Pr[ a ∈ E | f ← U(λ) conditioned on the table c; a ← m^f ]. -/
def PrFrom (c : Cache lam) (m : OComp lam α) (E : Set α) : ℝ≥0∞ :=
  ∫⁻ f, prob (m.run (over c f)) E ∂(U lam)

lemma Pr_eq_PrFrom (m : OComp lam α) (E : Set α) : Pr m (fun _ => E) = PrFrom (fun _ => none) m E :=
  rfl

lemma measurable_prob_run_over (c : Cache lam) (m : OComp lam α) (E : Set α) :
    Measurable fun f : Oracle lam => prob (m.run (over c f)) E :=
  (measurable_prob_run m E).comp (measurable_over c)

open Classical in
lemma PrFrom_pure (c : Cache lam) (a : α) (E : Set α) :
    PrFrom c (.pure a) E = if a ∈ E then 1 else 0 := by
  simp [PrFrom, OComp.run, prob_pure]

lemma PrFrom_sample (c : Cache lam) (n : ℕ) (k : Fin (n + 1) → OComp lam α) (E : Set α) :
    PrFrom c (.sample n k) E =
      expect (PMF.uniformOfFintype (Fin (n + 1))) fun r => PrFrom c (k r) E := by
  simp only [PrFrom, OComp.run, prob_bind, expect_uniform]
  rw [lintegral_finset_sum _ fun r _ => (measurable_prob_run_over c (k r) E).const_mul _]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [lintegral_const_mul _ (measurable_prob_run_over c (k r) E)]

lemma PrFrom_query_hit {c : Cache lam} {q : Str} {r : Digest lam} (h : c q = some r)
    (k : Digest lam → OComp lam α) (E : Set α) : PrFrom c (.query q k) E = PrFrom c (k r) E := by
  simp [PrFrom, OComp.run, over, h]

lemma PrFrom_query_miss {c : Cache lam} {q : Str} (h : c q = none)
    (k : Digest lam → OComp lam α) (E : Set α) :
    PrFrom c (.query q k) E = expect (PMF.uniformOfFintype (Digest lam)) fun r =>
      PrFrom (Function.update c q (some r)) (k r) E := by
  unfold PrFrom
  rw [lintegral_U_resample q (measurable_prob_run_over c (.query q k) E), expect_uniform]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  refine lintegral_congr fun f => ?_
  have h1 : over c (Function.update f q r) = over (Function.update c q (some r)) f := by
    funext q'
    by_cases e : q' = q
    · subst e; simp [over, h]
    · simp [over, Function.update_of_ne e]
  have h2 : over (Function.update c q (some r)) f q = r := by simp [over]
  simp only [OComp.run, h1, h2]

/-- One lazily sampled oracle answer: from the table if present, else fresh, uniform and
recorded. -/
def lazyAnswer (c : Cache lam) (q : Str) : PMF (Digest lam × Cache lam) :=
  match c q with
  | some r => PMF.pure (r, c)
  | none => (PMF.uniformOfFintype (Digest lam)).map fun r => (r, Function.update c q (some r))

/-- Both query rules (`PrFrom_query_hit`, `PrFrom_query_miss`) in one. -/
lemma PrFrom_query (c : Cache lam) (q : Str) (k : Digest lam → OComp lam α) (E : Set α) :
    PrFrom c (.query q k) E = expect (lazyAnswer c q) fun out => PrFrom out.2 (k out.1) E := by
  unfold lazyAnswer
  cases h : c q with
  | none => simp only [expect_map]; exact PrFrom_query_miss h k E
  | some r => simp only [expect_pure]; exact PrFrom_query_hit h k E

/-- Run an oracle computation with a lazily sampled oracle, starting from table c. -/
def OComp.lazyRun : OComp lam α → Cache lam → PMF (α × Cache lam)
  | .pure a, c => PMF.pure (a, c)
  | .query q k, c => (lazyAnswer c q).bind fun out => (k out.1).lazyRun out.2
  | .sample n k, c => (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => (k r).lazyRun c

/-- Eager = lazy, with a continuation: run m lazily, then continue from the table it left. -/
theorem PrFrom_bind (c : Cache lam) (m : OComp lam α) (g : α → OComp lam β) (E : Set β) :
    PrFrom c (m.bind g) E = expect (m.lazyRun c) fun out => PrFrom out.2 (g out.1) E := by
  induction m generalizing c with
  | pure a => simp [OComp.bind, OComp.lazyRun, expect_pure]
  | query q k ih =>
    simp only [OComp.bind, OComp.lazyRun, PrFrom_query, expect_bind, ih]
  | sample n k ih =>
    simp only [OComp.bind, OComp.lazyRun, PrFrom_sample, expect_bind, ih]

/-- Lazy runs compose: the second run starts from the table that the first has left. -/
lemma OComp.lazyRun_bind (m : OComp lam α) (g : α → OComp lam β) (c : Cache lam) :
    (m.bind g).lazyRun c = (m.lazyRun c).bind fun o => (g o.1).lazyRun o.2 := by
  induction m generalizing c with
  | pure a => simp [OComp.bind, OComp.lazyRun]
  | query q k ih => simp only [OComp.bind, OComp.lazyRun, ih, PMF.bind_bind]
  | sample n k ih => simp only [OComp.bind, OComp.lazyRun, ih, PMF.bind_bind]

lemma bind_pure_right (m : OComp lam α) : m.bind .pure = m := by
  induction m with
  | pure a => rfl
  | query q k ih => simp only [OComp.bind, ih]
  | sample n k ih => simp only [OComp.bind, ih]

/-- Eager = lazy. Sampling the whole function f ← U(λ) first and then running m gives the same
output distribution as running m with an oracle that is sampled point by point on demand. -/
theorem Pr_eq_lazy (m : OComp lam α) (E : Set α) :
    Pr m (fun _ => E) = prob ((m.lazyRun fun _ => none).map Prod.fst) E := by
  classical
  rw [Pr_eq_PrFrom, ← bind_pure_right m, PrFrom_bind, bind_pure_right, prob_eq_expect, expect_map]
  simp only [PrFrom_pure]

lemma SD_self_eq_zero {X Y : Set α → ℝ≥0∞} (h : ∀ E, X E = Y E) : SD X Y = 0 := by
  simp [SD, h]

lemma le_add_of_SD_le {X Y : Set α → ℝ≥0∞} {z : ℝ≥0∞} (h : SD X Y ≤ z) (E : Set α) :
    X E ≤ Y E + z := by
  have h1 : X E - Y E ≤ z :=
    le_trans (le_trans (le_max_left _ _) (le_iSup (fun E => max (X E - Y E) (Y E - X E)) E)) h
  rw [add_comm]; exact tsub_le_iff_right.1 h1

end ZKCP
