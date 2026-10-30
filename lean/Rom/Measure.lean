-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Measure.lean: the uniform distribution on a whole family of oracles, as a measure, and
probabilities over it.

The domains may be infinite, so "all oracles are uniformly random functions, independent of each
other" is not a discrete distribution. It is the product measure `U S`. An algorithm is run with the
family f fixed (`OComp.runEager`), which gives a discrete distribution over its coins, and `Pr`
integrates over f. At S = `rom lam` these agree with `ZKCP.U`, `ZKCP.PrCoins` and `ZKCP.Pr` of
ZKCP/Defs.lean (Rom/Bridge.lean). The main lemma on `U S` is `lintegral_U_resample`.

Shared with VCV-io (with Rom/EagerLazy.lean): lean/CREDITS.md, section 4.

Notation: `ZKCP.`: the namespace of ZKCP/Defs.lean; `rom lam : OSpec` (Rom/OSpec.lean): the model of
ZKCP/Defs.lean: one oracle {0,1}* → {0,1}^lam; `PrCoins f c E : ℝ≥0∞` (this file): Pr[ a ∈ E | a ←
c^f ], with the family f fixed: over c's coins only; `Pr c E : ℝ≥0∞` (this file): Pr[ a ∈ E(f) | f ←
U S; a ← c^f ]: the average over the family of the probability over c's coins.
-/
import Rom.Eager
import Rom.OComp
noncomputable section -- Lean tags what it cannot compile

open MeasureTheory
open scoped ENNReal

namespace Rom

variable {S : OSpec} {α β : Type}

/-- Every subset of a (finite) range is an event. -/
instance (o : S.ι) : MeasurableSpace (S.Rng o) := ⊤
instance (o : S.ι) : DiscreteMeasurableSpace (S.Rng o) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The uniform distribution on the range of oracle o. -/
abbrev unifM (S : OSpec) (o : S.ι) : Measure (S.Rng o) :=
  (PMF.uniformOfFintype (S.Rng o)).toMeasure

/-- All oracles of the family are uniformly random functions, and all their values are independent:
the product, over the oracles o and the points q of Dom o, of the uniform distribution on Rng o. -/
def U (S : OSpec) : Measure (Fam S) :=
  Measure.infinitePi fun o : S.ι => Measure.infinitePi fun _ : S.Dom o => unifM S o

instance : IsProbabilityMeasure (U S) := by unfold U; infer_instance

/-- The family f with the value of oracle o at the point q replaced by r. -/
def Fam.set (f : Fam S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) : Fam S :=
  Function.update f o (Function.update (f o) q r)

@[simp] lemma Fam.set_self (f : Fam S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    f.set o q r o q = r := by
  simp [Fam.set]

lemma Fam.set_of_ne_point (f : Fam S) (o : S.ι) {q q' : S.Dom o} (h : q' ≠ q) (r : S.Rng o) :
    f.set o q r o q' = f o q' := by
  simp [Fam.set, Function.update_of_ne h]

lemma Fam.set_of_ne_oracle (f : Fam S) {o o' : S.ι} (h : o' ≠ o) (q : S.Dom o)
    (r : S.Rng o) (q' : S.Dom o') :
    f.set o q r o' q' = f o' q' := by
  simp [Fam.set, Function.update_of_ne h]

/-! ### Resampling one value (from Rom.infinitePi_resample, Rom/Eager.lean) -/

/-- The family of oracles as one function on the pairs (oracle, point). -/
abbrev Flat (S : OSpec) : Type := (p : Σ o : S.ι, S.Dom o) → S.Rng p.1

/-- U S is the image, under currying, of the product measure over all pairs (oracle, point). -/
lemma U_eq_map_curry : U S = (Measure.infinitePi fun p : (Σ o : S.ι, S.Dom o) => unifM S p.1).map
    (MeasurableEquiv.piCurry fun (o : S.ι) (_ : S.Dom o) => S.Rng o) :=
  (Measure.infinitePi_map_piCurry (X := fun (o : S.ι) (_ : S.Dom o) => S.Rng o)
    (fun (o : S.ι) (_ : S.Dom o) => unifM S o)).symm

lemma curry_update (g : Flat S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    (Sigma.curry (Function.update g ⟨o, q⟩ r) : Fam S) = Fam.set (Sigma.curry g) o q r := by
  funext o' q'
  by_cases ho : o' = o
  · subst ho
    by_cases hq : q' = q
    · subst hq; simp [Sigma.curry]
    · rw [Fam.set_of_ne_point _ _ hq]
      have : (⟨o', q'⟩ : Σ o : S.ι, S.Dom o) ≠ ⟨o', q⟩ := fun e => hq (by simpa using e)
      simp [Sigma.curry, Function.update_of_ne this]
  · rw [Fam.set_of_ne_oracle _ ho]
    have : (⟨o', q'⟩ : Σ o : S.ι, S.Dom o) ≠ ⟨o, q⟩ := fun e => ho (congrArg Sigma.fst e)
    simp [Sigma.curry, Function.update_of_ne this]

/-- Resampling. The average over the family of any measurable quantity is unchanged if one value, of
oracle o at the point q, is drawn afresh. -/
theorem lintegral_U_resample (o : S.ι) (q : S.Dom o) {g : Fam S → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ f, g f ∂(U S) =
      Prob.expect (PMF.uniformOfFintype (S.Rng o)) fun r => ∫⁻ f, g (f.set o q r) ∂(U S) := by
  set e := MeasurableEquiv.piCurry fun (o : S.ι) (_ : S.Dom o) => S.Rng o with he
  set μ : Measure (Flat S) := Measure.infinitePi fun p : (Σ o : S.ι, S.Dom o) => unifM S p.1 with hμ
  have hge : Measurable fun h : Flat S => g (e h) := hg.comp e.measurable
  have hset : ∀ r, Measurable fun f : Fam S => g (f.set o q r) := by
    intro r
    refine hg.comp ?_
    unfold Fam.set
    refine measurable_pi_iff.2 fun o' => ?_
    by_cases ho : o' = o
    · subst ho
      simp only [Function.update_self]
      exact measurable_update_left.comp (measurable_pi_apply o')
    · simp only [Function.update_of_ne ho]
      exact measurable_pi_apply o'
  have h1 : ∀ G : Fam S → ℝ≥0∞, Measurable G → ∫⁻ f, G f ∂(U S) = ∫⁻ h, G (e h) ∂μ := by
    intro G hG
    rw [U_eq_map_curry, lintegral_map hG e.measurable]
  rw [h1 g hg]
  conv_lhs => rw [hμ, ← infinitePi_resample (fun p : (Σ o : S.ι, S.Dom o) => unifM S p.1) ⟨o, q⟩]
  have hupd : Measurable fun p : Flat S × S.Rng o =>
      Function.update p.1 (⟨o, q⟩ : Σ o : S.ι, S.Dom o) p.2 :=
    measurable_update' (a := (⟨o, q⟩ : Σ o : S.ι, S.Dom o))
  rw [lintegral_map hge hupd,
    lintegral_prod_symm (fun p : Flat S × S.Rng o => g (e (Function.update p.1 ⟨o, q⟩ p.2)))
      (hge.comp hupd).aemeasurable, lintegral_fintype]
  unfold Prob.expect
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _), mul_comm]
  show _ = PMF.uniformOfFintype (S.Rng o) r * ∫⁻ f, g (f.set o q r) ∂(U S)
  rw [h1 _ (hset r)]
  congr 1
  refine lintegral_congr fun x => ?_
  show g (Sigma.curry (Function.update x ⟨o, q⟩ r)) = g (Fam.set (Sigma.curry x) o q r)
  rw [curry_update]

/-! ### Probabilities -/

/-- Pr[ a ∈ E | a ← c^f ], with the family f fixed: over c's coins only. -/
def PrCoins (f : Fam S) (c : OComp S α) (E : Set α) : ℝ≥0∞ := Prob.pr (c.runEager f) E

/-- Pr[ a ∈ E(f) | f ← U S; a ← c^f ]: the average over the family of the probability over c's
coins. -/
def Pr (c : OComp S α) (E : Fam S → Set α) : ℝ≥0∞ := ∫⁻ f, PrCoins f c (E f) ∂(U S)

/-- A quantity that also depends on one value of the family is measurable if it is so for each
possible value. -/
lemma measurable_eval_dep (o : S.ι) (q : S.Dom o)
    {F : S.Rng o → Fam S → ℝ≥0∞} (h : ∀ r, Measurable (F r)) :
    Measurable fun f : Fam S => F (f o q) f := by
  have h2 : Measurable fun p : Fam S × S.Rng o => F p.2 p.1 := measurable_from_prod_countable_left h
  have h3 : Measurable fun f : Fam S => f o q :=
    (measurable_pi_apply q).comp (measurable_pi_apply o)
  exact h2.comp (measurable_id.prodMk h3)

/-- The integrand of Pr is measurable, also for an event E(f) that mentions f, provided that for
each output a the set { f | a ∈ E(f) } is measurable.  So the integral in Pr is the true average. -/
theorem measurable_PrCoins_dep
    (c : OComp S α) (E : Fam S → Set α) (hE : ∀ a, MeasurableSet {f | a ∈ E f}) :
    Measurable fun f => PrCoins f c (E f) := by
  classical
  unfold PrCoins
  induction c with
  | pure a =>
    simp only [OComp.runEager, Prob.pr_pure]
    exact Measurable.ite (hE a) measurable_const measurable_const
  | query o q k ih =>
    exact measurable_eval_dep o q (F := fun r f => Prob.pr ((k r).runEager f) (E f)) ih
  | sample n k ih =>
    simp only [OComp.runEager, Prob.pr_bind, Prob.expect, tsum_fintype]
    exact Finset.measurable_sum _ fun r _ => (ih r).const_mul _

theorem measurable_PrCoins (c : OComp S α) (E : Set α) :
    Measurable fun f : Fam S => PrCoins f c E :=
  measurable_PrCoins_dep c (fun _ => E) fun a => by by_cases h : a ∈ E <;> simp [h]

lemma Pr_mono (c : OComp S α) {E F : Fam S → Set α} (h : ∀ f, E f ⊆ F f) : Pr c E ≤ Pr c F :=
  lintegral_mono fun f => Prob.pr_mono _ (h f)

lemma Pr_le_one (c : OComp S α) (E : Fam S → Set α) : Pr c E ≤ 1 := by
  calc Pr c E ≤ ∫⁻ _, 1 ∂(U S) := lintegral_mono fun f => Prob.pr_le_one _ _
    _ = 1 := by simp

end Rom
