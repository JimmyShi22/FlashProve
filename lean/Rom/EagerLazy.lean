-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Rom/EagerLazy.lean: sampling the whole family of oracles first ("eager") equals, in distribution,
  sampling each value when first queried ("lazy").

  `eager_eq_lazy` connects the measure `U S` (Rom/Measure.lean) with everything that is proved by
  lazy sampling. Its continuation G may depend on the output and on the whole family f, so the
  theorem composes: what follows an algorithm sees the family overlaid by the table that the
  algorithm returns. `Pr_eq_law` is the special case without continuation.

  Credit. The public Lean library VCV-io (https://github.com/Verified-zkEVM/VCV-io) also represents
  an algorithm with oracle access as a tree of queries.
  This file proves, for the trees of Rom/OComp.lean, that sampling all oracles first and sampling
  each value when it is first asked for give the same law. VCV-io, at commit
  afa6593f, proves the same equality
  (QueryTracking/RandomOracle/EagerTable.lean and DependentTable.lean, with the resampling step in
  ToMathlib/MeasureTheory/Measure/UniformTable.lean) by the same plan: induction generalized over a
  partial table, the same overlay of a table on a full function, the same resampling step. VCV-io's
  form is for finite domains and output laws; ours is a measure over possibly infinite families.
  lean/CREDITS.md, section 4, has VCV-io's entry.
  VCV-io is not a dependency:
  no file of this library imports it.

  Notation:
    `S`: `OSpec` (Rom/OSpec.lean): a family of oracles: names, and for each name a domain and a
      finite, non-empty range
    `Fam S` (Rom/OSpec.lean): a whole family of functions; `Table S`: a partial table: what lazy
      sampling has fixed so far
    `U S` (Rom/Measure.lean): the product, over the oracles o and the points q of Dom o, of the
      uniform distribution on Rng o
    `Pr c E` (Rom/Measure.lean): Pr[ a ∈ E(f) | f ← U S; a ← c^f ]; `PrCoins f c E`: Pr[ a ∈ E | a ←
      c^f ], with the family f fixed: over c's coins only
    `c.law` (Rom/OComp.lean): the law of the output under lazily sampled oracles, from the empty
      table
-/
import Rom.Measure
noncomputable section -- Lean tags what it cannot compile

open MeasureTheory
open scoped ENNReal

namespace Rom

open Prob (expect pr)

variable {S : OSpec} {α β : Type}

/-! ### The two semantics respect sequential composition -/

lemma OComp.runEager_bind (f : Fam S) (c : OComp S α) (g : α → OComp S β) :
    (c.bind g).runEager f = (c.runEager f).bind fun a => (g a).runEager f := by
  induction c with
  | pure a => simp [OComp.bind, OComp.runEager]
  | query o q k ih => simp only [OComp.bind, OComp.runEager, ih]
  | sample n k ih => simp only [OComp.bind, OComp.runEager, ih, PMF.bind_bind]

lemma OComp.runLazy_bind (c : OComp S α) (g : α → OComp S β) (T : Table S) :
    (c.bind g).runLazy T = (c.runLazy T).bind fun out => (g out.1).runLazy out.2 := by
  induction c generalizing T with
  | pure a => simp [OComp.bind, OComp.runLazy]
  | query o q k ih =>
    simp only [OComp.bind, OComp.runLazy]
    cases T o q with
    | some r => exact ih r T
    | none => simp only [ih, PMF.bind_bind]
  | sample n k ih => simp only [OComp.bind, OComp.runLazy, ih, PMF.bind_bind]

/-- The image of the output under a function φ. -/
theorem Pr_bind_pure (c : OComp S α) (φ : α → β) (T : Fam S → Set β) :
    Pr (c.bind fun a => .pure (φ a)) T = Pr c fun f => φ ⁻¹' T f := by
  unfold Pr PrCoins
  refine lintegral_congr fun f => ?_
  rw [OComp.runEager_bind]
  exact Prob.pr_map (c.runEager f) φ (T f)

/-! ### A family overlaid by a table -/

/-- The family that answers from the table T where T is defined and from f elsewhere. -/
def Table.over (T : Table S) (f : Fam S) : Fam S := fun o q => (T o q).getD (f o q)

lemma Table.over_empty (f : Fam S) : (Table.empty S).over f = f := rfl

lemma Table.over_of_some {T : Table S} {o : S.ι} {q : S.Dom o} {r : S.Rng o}
    (h : T o q = some r) (f : Fam S) : T.over f o q = r := by
  simp [Table.over, h]

lemma Table.measurable_over (T : Table S) : Measurable T.over := by
  refine measurable_pi_iff.2 fun o => measurable_pi_iff.2 fun q => ?_
  unfold Table.over
  cases T o q with
  | none => exact (measurable_pi_apply q).comp (measurable_pi_apply o)
  | some r => exact measurable_const

lemma Table.set_self (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    T.set o q r o q = some r := by
  simp [Table.set]

/-- Fixing a value of f at a point where the table has no entry is the same as writing it into the
table. -/
lemma Table.over_set {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q = none)
    (r : S.Rng o) (f : Fam S) :
    T.over (f.set o q r) = (T.set o q r).over f := by
  funext o' q'
  by_cases ho : o' = o
  · subst ho
    by_cases hq : q' = q
    · subst hq; simp [Table.over, h, Table.set]
    · simp [Table.over, Table.set, Fam.set, Function.update_of_ne hq]
  · simp [Table.over, Table.set, Fam.set, Function.update_of_ne ho]

/-! ### Eager = lazy -/

lemma expect_fintype {C : Type} [Fintype C] (p : PMF C) (F : C → ℝ≥0∞) :
    expect p F = ∑ c, p c * F c :=
  tsum_fintype _

/-- The average of a measurable continuation after an algorithm is a measurable function of the
family. -/
lemma measurable_expect_runEager
    (c : OComp S α) {G : α → Fam S → ℝ≥0∞} (hG : ∀ a, Measurable (G a)) :
    Measurable fun f => expect (c.runEager f) fun a => G a f := by
  induction c with
  | pure a => simp only [OComp.runEager, Prob.expect_pure]; exact hG a
  | query o q k ih =>
    exact measurable_eval_dep o q (F := fun r f => expect ((k r).runEager f) fun a => G a f) ih
  | sample n k ih =>
    simp only [OComp.runEager, Prob.expect_bind]
    simp only [expect_fintype]
    exact Finset.measurable_sum _ fun r _ => (ih r).const_mul _

/-- Eager = lazy. For every table T and every measurable continuation G, which may read the output
and the whole family:
running c on a uniform family overlaid by T and then G has the same average as running c lazily
from T and then G on a uniform family overlaid by the table that c returns. -/
theorem eager_eq_lazy (c : OComp S α) {G : α → Fam S → ℝ≥0∞}
    (hG : ∀ a, Measurable (G a)) (T : Table S) :
    ∫⁻ f, expect (c.runEager (T.over f)) (fun a => G a (T.over f)) ∂(U S) =
      expect (c.runLazy T) fun out => ∫⁻ f, G out.1 (out.2.over f) ∂(U S) := by
  induction c generalizing T with
  | pure a => simp only [OComp.runEager, OComp.runLazy, Prob.expect_pure]
  | query o q k ih =>
    cases h : T o q with
    | some r =>
      simp only [OComp.runEager, OComp.runLazy, h, Table.over_of_some h]
      exact ih r T
    | none =>
      rw [lintegral_U_resample o q
        (g := fun f => expect ((OComp.query o q k).runEager (T.over f)) fun a => G a (T.over f))
        ((measurable_expect_runEager (.query o q k) hG).comp T.measurable_over)]
      simp only [OComp.runLazy, h, Prob.expect_bind]
      refine Prob.expect_congr _ fun r => ?_
      simp only [OComp.runEager, Table.over_set h,
        Table.over_of_some (Table.set_self T o q r)]
      exact ih r _
  | sample n k ih =>
    simp only [OComp.runEager, OComp.runLazy, Prob.expect_bind]
    simp only [expect_fintype]
    have hm : ∀ r, Measurable fun f => expect ((k r).runEager (T.over f)) fun a => G a (T.over f) :=
      fun r => (measurable_expect_runEager (k r) hG).comp T.measurable_over
    rw [lintegral_finset_sum _ fun r _ => (hm r).const_mul _]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [lintegral_const_mul _ (hm r), ih r T]

/-- Pr[ a ∈ E | the family uniform, overlaid by T; a ← c^f ]. -/
def PrFrom (T : Table S) (c : OComp S α) (E : Set α) : ℝ≥0∞ :=
  ∫⁻ f, PrCoins (T.over f) c E ∂(U S)

lemma Pr_eq_PrFrom (c : OComp S α) (E : Set α) : Pr c (fun _ => E) = PrFrom (Table.empty S) c E :=
  rfl

/-- From any table: the probability of an event about the output alone is that of the lazy run. -/
theorem PrFrom_eq_lazy (T : Table S) (c : OComp S α) (E : Set α) :
    PrFrom T c E = pr ((c.runLazy T).map Prod.fst) E := by
  classical
  unfold PrFrom PrCoins
  simp only [Prob.pr_eq_expect]
  rw [eager_eq_lazy c (G := fun a _ => if a ∈ E then 1 else 0) (fun _ => measurable_const) T,
    Prob.expect_map]
  simp

/-- Run c lazily, then continue from the table that it returns. -/
theorem PrFrom_bind (T : Table S) (c : OComp S α) (g : α → OComp S β) (E : Set β) :
    PrFrom T (c.bind g) E = expect (c.runLazy T) fun out => PrFrom out.2 (g out.1) E := by
  simp only [PrFrom_eq_lazy, OComp.runLazy_bind, PMF.map_bind, Prob.pr_bind]

/-- Pr[ a ∈ E | f ← U S; a ← c^f ] is the probability of E under c.law, the output law of c with
lazily sampled oracles. -/
theorem Pr_eq_law (c : OComp S α) (E : Set α) : Pr c (fun _ => E) = pr c.law E :=
  (Pr_eq_PrFrom c E).trans (PrFrom_eq_lazy _ c E)

/-- `Pr_eq_law` for an event E(f), each { f | a ∈ E(f) } measurable: after the lazy run, what is
left is the measure of a set of families. -/
theorem Pr_dep_eq_lazy (c : OComp S α) (E : Fam S → Set α) (hE : ∀ a, MeasurableSet {f | a ∈ E f}) :
    Pr c E = expect (c.runLazy (Table.empty S)) fun out => U S {f | out.1 ∈ E (out.2.over f)} := by
  classical
  unfold Pr PrCoins
  simp only [Prob.pr_eq_expect]
  have h := eager_eq_lazy c (G := fun a f => if a ∈ E f then 1 else 0)
    (fun a => Measurable.ite (hE a) measurable_const measurable_const) (Table.empty S)
  refine Eq.trans h (Prob.expect_congr _ fun out => ?_)
  have hm : MeasurableSet {f | out.1 ∈ E (out.2.over f)} := out.2.measurable_over (hE out.1)
  rw [← lintegral_indicator_one hm]
  refine lintegral_congr fun f => ?_
  by_cases hf : out.1 ∈ E (out.2.over f) <;> simp [Set.indicator, hf]

end Rom
