-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyCount.lean: one count after a harmless first part: an event that is caused by
single entries of the trace, and never by a query with the property P, is charged only to the
queries of the second part of an algorithm "c, then g" whose first part asks queries with P alone.

Two theorems. Generic in the family of oracles and in the event. The analogues of
`pr_stepEventAfter_le`, `pr_stepEvent_le` (Rom/OneCount.lean), which charge every query of the whole
algorithm.
`StepEvent step tr` (Rom/OneCount.lean): some entry e of tr has step pre e, pre the entries before
it. `OnlyQ P c` (Compile/Batch/CompleteUnif.lean): all queries of c, on all paths, have P.

Main names:
  `Rom.pr_stepEvent_behind`: from the empty table, Pr [ the event has happened in the trace of (c,
    then g) ] ≤ t · ε, t a bound on the queries of g a for every a (`hg`); ε a bound on the chance
    that the answer of one new query causes the event (`hnew`); a repeated entry does not cause it
    (`hold`); no query with P causes it (`hP`); all queries of c have P (`hc`); however many queries
    c asks.
  `Rom.pr_stepEventAfter_behind`: the same, under the same hypotheses, after any trace pre, with the
    table of pre (`T.Holds pre`, Rom/OneCount.lean).

Why: the bound on index binding charges the round-by-round error to every query of the committer. An
honest committer asks no query at the Fiat-Shamir oracle of sessions (`OracleName.fb Tag.onl`,
Compile/Batch/Oracles.lean), at which alone a session's state event can happen.

Limits: this file says nothing on events that c's queries can cause (hash events: they are counted
over all queries, elsewhere).
-/
import Rom.OneCount
import Compile.Batch.CompleteUnif

set_option autoImplicit false

open scoped ENNReal
open Prob

namespace Rom
open Compile.Batch.CompleteUnif (OnlyQ)

variable {S : OSpec} {α β : Type}

theorem pr_stepEventAfter_behind
    (step : Trace S → QA S → Prop) (ε : ℝ≥0∞) (P : (o : S.ι) → S.Dom o → Prop)
    (hold : ∀ (pre : Trace S) (e : QA S), e ∈ pre → ¬ step pre e)
    (hnew : ∀ (pre : Trace S) (o : S.ι) (q : S.Dom o),
      (∀ r, (⟨o, q, r⟩ : QA S) ∉ pre) → pr (unif (S.Rng o)) {r | step pre ⟨o, q, r⟩} ≤ ε)
    (hP : ∀ (pre : Trace S) (o : S.ι) (q : S.Dom o) (r : S.Rng o), P o q → ¬ step pre ⟨o, q, r⟩)
    (g : α → OComp S β) (t : ℕ) (hg : ∀ a, (g a).QueryBound t) (c : OComp S α) :
    OnlyQ P c → ∀ (pre : Trace S) (T : Table S), T.Holds pre →
      pr ((c.bind g).withTrace.runLazy T) {x | StepEventAfter step pre x.1.2} ≤ (t : ℝ≥0∞) * ε := by
  induction c with
  | pure a =>
    intro _ pre T hT
    have h := pr_stepEventAfter_le step (fun _ => ε) hold hnew (g a) t pre T hT (hg a)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    exact h
  | sample n k ih =>
    intro hc pre T hT
    simp only [OComp.bind, OComp.withTrace, OComp.runLazy]
    exact pr_bind_le_of_forall _ _ _ fun r _ => ih r (hc r) pre T hT
  | query o q k ih =>
    intro hc pre T hT
    have hrest : ∀ (r : S.Rng o) (T' : Table S), T'.Holds (pre ++ [⟨o, q, r⟩]) →
        pr ((((k r).bind g).withTrace.bind fun out =>
              OComp.pure (out.1, (⟨o, q, r⟩ : QA S) :: out.2)).runLazy T')
            {x | StepEventAfter step pre x.1.2} ≤
          (t : ℝ≥0∞) * ε := by
      intro r T' hT'
      rw [runLazy_withTrace_step, pr_map]
      refine le_trans (pr_mono _ ?_) (ih r (hc.2 r) _ T' hT')
      intro x hx
      rcases (stepEventAfter_cons step pre _ _).1 hx with h1 | h1
      · exact absurd h1 (hP pre o q r hc.1)
      · exact h1
    simp only [OComp.bind, OComp.withTrace, OComp.runLazy]
    cases hTq : T o q with
    | some r => exact hrest r T (hT.concat_old hTq)
    | none => exact pr_bind_le_of_forall _ _ _ fun r _ => hrest r _ (hT.concat_new hTq r)

/-- One count after a harmless first part, from the empty table. -/
theorem pr_stepEvent_behind (step : Trace S → QA S → Prop) (ε : ℝ≥0∞)
    (P : (o : S.ι) → S.Dom o → Prop) (hold : ∀ (pre : Trace S) (e : QA S), e ∈ pre → ¬ step pre e)
    (hnew : ∀ (pre : Trace S) (o : S.ι) (q : S.Dom o),
      (∀ r, (⟨o, q, r⟩ : QA S) ∉ pre) → pr (unif (S.Rng o)) {r | step pre ⟨o, q, r⟩} ≤ ε)
    (hP : ∀ (pre : Trace S) (o : S.ι) (q : S.Dom o) (r : S.Rng o), P o q → ¬ step pre ⟨o, q, r⟩)
    (c : OComp S α) (g : α → OComp S β) (t : ℕ) (hc : OnlyQ P c) (hg : ∀ a, (g a).QueryBound t) :
    pr (c.bind g).withTrace.law {x | StepEvent step x.2} ≤ (t : ℝ≥0∞) * ε := by
  have h :=
    pr_stepEventAfter_behind step ε P hold hnew hP g t hg c hc [] (Table.empty S) Table.holds_empty
  rw [OComp.law, pr_map]
  refine le_trans (pr_mono _ ?_) h
  intro x hx
  exact (stepEvent_iff_after_nil step _).1 hx

end Rom
