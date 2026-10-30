-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/Public.lean: PUBLIC READINGS IN FRONT OF AN HONEST EXPERIMENT COST ITS BOUND
NOTHING. General in the family of oracles.

An experiment Y d hangs on a value d. Suppose that at every fixed d an event E d of its outcome has
probability at most ε. Then the same bound holds where d is what an algorithm Pub gets from the
oracles themselves, run IN FRONT, if no Y d asks a query that Pub may ask.

Why not the library's pub_lift (Johnson/TypedOracleCompiler/RecCompile/PublicLift.lean): that lemma bounds "yes and
bad" against every maker that does not know d, with the public algorithm behind the makers. An
honest side knows d: it runs the public algorithm first.

Main names.
  set_same, map_fst_runLazy_congr, PrFrom_congr_off   a lazy run's outcome reads the table only
    where the program may ask.
  pub_le   THE STATEMENT.

Limits. A lemma on experiments. It says nothing of a wire, a coding or a program. That an experiment
over one hash function asks no public string is a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Round

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open Rom Prob
open scoped ENNReal

variable {S : OSpec} {α D : Type}

theorem set_same (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    T.set o q r o q = some r := by
  simp [Table.set]

/-- Two tables that agree wherever the program may ask give its outcome one law. -/
theorem map_fst_runLazy_congr {P : (o : S.ι) → S.Dom o → Prop} (c : OComp S α) :
    c.AsksIn P → ∀ T T' : Table S, (∀ o q, P o q → T o q = T' o q) →
      (c.runLazy T).map Prod.fst = (c.runLazy T').map Prod.fst := by
  induction c with
  | pure a =>
    intro _ T T' _
    simp only [OComp.runLazy, PMF.pure_map]
  | query o q k ih =>
    intro hc T T' h
    have e := h o q hc.1
    cases hT : T' o q with
    | some r =>
      rw [hT] at e
      simp only [OComp.runLazy, hT, e]
      exact ih r (hc.2 r) T T' h
    | none =>
      rw [hT] at e
      simp only [OComp.runLazy, hT, e, PMF.map_bind]
      refine congrArg _ (funext fun r => ih r (hc.2 r) _ _ fun o' q' hp => ?_)
      by_cases hq : (⟨o', q'⟩ : Σ o, S.Dom o) = ⟨o, q⟩
      · cases hq
        rw [set_same, set_same]
      · rw [Law.set_other T r hq, Law.set_other T' r hq]
        exact h o' q' hp
  | sample n k ih =>
    intro hc T T' h
    simp only [OComp.runLazy, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r (hc r) T T' h)

theorem PrFrom_congr_off {P : (o : S.ι) → S.Dom o → Prop} {c : OComp S α} (hc : c.AsksIn P)
    {T T' : Table S} (h : ∀ o q, P o q → T o q = T' o q) (E : Set α) :
    PrFrom T c E = PrFrom T' c E := by
  rw [PrFrom_eq_lazy, PrFrom_eq_lazy, map_fst_runLazy_congr c hc T T' h]

/-- **Public readings in front of an honest experiment cost its bound nothing.** -/
theorem pub_le (Pub : OComp S D) (Y : D → OComp S α) (Pt : (o : S.ι) → S.Dom o → Prop)
    (hP : Pub.AsksIn Pt) (hY : ∀ d, (Y d).AsksIn fun o q => ¬ Pt o q) (T₀ : Table S)
    (E : D → Set α) {ε : ℝ≥0∞} (h : ∀ d, PrFrom T₀ (Y d) (E d) ≤ ε) :
    PrFrom T₀ (Pub.bind fun d => (Y d).bind fun a => .pure (d, a)) {z | z.2 ∈ E z.1} ≤ ε := by
  refine PrFrom_bind_le T₀ _ _ _ fun out ho => ?_
  rw [PrFrom_bind_pure]
  refine le_of_eq_of_le ?_ (h out.1)
  exact PrFrom_congr_off (hY out.1) (fun o q hn => Law.keeps_of_asksIn Pub hP T₀ out ho o q hn)
    (E out.1)

end OnBytes.Prover
