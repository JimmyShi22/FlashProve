-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/OneCount.lean: a union bound over the queries, under lazy sampling, for bad events that are
defined query by query (`StepEvent`). The main theorem is `pr_stepEvent_le`.

The file is generic in the family of oracles and in the event. Compile/Batch/Hash.lean applies it to
the two hash events E_M and E_F of the compiled scheme.
-/
import Rom.EagerLazy
import Prob.Count

open scoped ENNReal
open Prob

namespace Rom

variable {S : OSpec} {α : Type}

/-- An event that happens at a step. step pre e says that the query-answer pair e, coming after the
trace pre, causes the event. -/
def StepEvent (step : Trace S → QA S → Prop) (tr : Trace S) : Prop :=
  ∃ (pre : Trace S) (e : QA S) (post : Trace S), tr = pre ++ e :: post ∧ step pre e

/-- The event happens in the part tr of a trace that begins with pre. -/
def StepEventAfter (step : Trace S → QA S → Prop) (pre tr : Trace S) : Prop :=
  ∃ (a : Trace S) (e : QA S) (b : Trace S), tr = a ++ e :: b ∧ step (pre ++ a) e

theorem stepEvent_iff_after_nil (step : Trace S → QA S → Prop) (tr : Trace S) :
    StepEvent step tr ↔ StepEventAfter step [] tr := by
  simp only [StepEvent, StepEventAfter, List.nil_append]

theorem not_stepEventAfter_nil (step : Trace S → QA S → Prop) (pre : Trace S) :
    ¬ StepEventAfter step pre [] := by
  rintro ⟨a, e, b, h, -⟩
  simp at h

theorem stepEventAfter_cons (step : Trace S → QA S → Prop) (pre : Trace S)
    (e : QA S) (tr : Trace S) :
    StepEventAfter step pre (e :: tr) ↔ step pre e ∨ StepEventAfter step (pre ++ [e]) tr := by
  constructor
  · rintro ⟨a, e0, b, h, hs⟩
    cases a with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl (by simpa using hs)
    | cons x a =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨a, e0, b, rfl, by simpa using hs⟩
  · rintro (hs | ⟨a, e0, b, rfl, hs⟩)
    · exact ⟨[], e, tr, rfl, by simpa using hs⟩
    · exact ⟨e :: a, e0, b, rfl, by simpa using hs⟩

/-- A step event is never undone. -/
theorem StepEvent.append {step : Trace S → QA S → Prop} {tr : Trace S}
    (h : StepEvent step tr) (tr' : Trace S) : StepEvent step (tr ++ tr') := by
  obtain ⟨pre, e, post, rfl, hs⟩ := h
  exact ⟨pre, e, post ++ tr', by simp, hs⟩

/-- The table holds exactly the pairs of the trace. -/
def Table.Holds (T : Table S) (tr : Trace S) : Prop :=
  ∀ (o : S.ι) (q : S.Dom o) (r : S.Rng o), T o q = some r ↔ (⟨o, q, r⟩ : QA S) ∈ tr

theorem Table.holds_empty : (Table.empty S).Holds [] := by
  intro o q r
  simp [Table.empty]

/-- A repeated query changes neither the table nor what the trace holds. -/
theorem Table.Holds.concat_old {T : Table S} {tr : Trace S} (h : T.Holds tr) {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (hT : T o q = some r) :
    T.Holds (tr ++ [⟨o, q, r⟩]) := by
  intro o' q' r'
  rw [List.mem_append, List.mem_singleton, h o' q' r']
  constructor
  · exact Or.inl
  · rintro (h1 | h1)
    · exact h1
    · rw [h1]; exact (h o q r).1 hT

/-- A new query enters the table and the trace. -/
theorem Table.Holds.concat_new {T : Table S} {tr : Trace S} (h : T.Holds tr) {o : S.ι} {q : S.Dom o}
    (hT : T o q = none) (r : S.Rng o) : (T.set o q r).Holds (tr ++ [⟨o, q, r⟩]) := by
  intro o' q' r'
  rw [List.mem_append, List.mem_singleton, ← h o' q' r']
  by_cases ho : o' = o
  · subst ho
    by_cases hq : q' = q
    · subst hq
      simp only [Table.set, Function.update_self, Option.some.injEq, hT]
      constructor
      · rintro rfl; exact Or.inr rfl
      · rintro (h1 | h1)
        · cases h1
        · simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h1
          exact h1.symm
    · simp only [Table.set, Function.update_self, Function.update_of_ne hq]
      constructor
      · exact Or.inl
      · rintro (h1 | h1)
        · exact h1
        · simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h1
          exact absurd h1.1 hq
  · simp only [Table.set, Function.update_of_ne ho]
    constructor
    · exact Or.inl
    · rintro (h1 | h1)
      · exact h1
      · exact absurd (Sigma.mk.inj h1).1 ho

/-- The run of "the algorithm with its trace" after one query: the pair is put in front of the rest
of the trace. -/
theorem runLazy_withTrace_step (c : OComp S α) (e : QA S) (T : Table S) :
    (c.withTrace.bind fun out => OComp.pure (out.1, e :: out.2)).runLazy T =
      (c.withTrace.runLazy T).map fun x => ((x.1.1, e :: x.1.2), x.2) := by
  rw [OComp.runLazy_bind]
  rfl

/-- One count. Let an event be caused by single entries of the trace, never by an entry that is in
the trace already, and by the answer of a new query, after a trace of length n, with probability at
most ε n. Then an algorithm with at most t queries that starts after the trace pre, with the table
of pre, causes the event with probability at most ε (|pre|) + ... + ε (|pre| + t - 1). -/
theorem pr_stepEventAfter_le (step : Trace S → QA S → Prop) (ε : ℕ → ℝ≥0∞)
    (hold : ∀ (pre : Trace S) (e : QA S), e ∈ pre → ¬ step pre e)
    (hnew : ∀ (pre : Trace S) (o : S.ι) (q : S.Dom o),
      (∀ r, (⟨o, q, r⟩ : QA S) ∉ pre) → pr (unif (S.Rng o)) {r | step pre ⟨o, q, r⟩} ≤ ε pre.length)
    (A : OComp S α) :
    ∀ (t : ℕ) (pre : Trace S) (T : Table S), T.Holds pre → A.QueryBound t →
      pr (A.withTrace.runLazy T) {x | StepEventAfter step pre x.1.2} ≤
        ∑ v ∈ Finset.range t, ε (pre.length + v) := by
  induction A with
  | pure a =>
    intro t pre T _ _
    simp only [OComp.withTrace, OComp.runLazy, pr_pure, Set.mem_setOf_eq,
      if_neg (not_stepEventAfter_nil step pre)]
    exact zero_le _
  | sample n k ih =>
    intro t pre T hT hb
    simp only [OComp.withTrace, OComp.runLazy]
    exact pr_bind_le_of_forall _ _ _ fun r _ => ih r t pre T hT (hb r)
  | query o q k ih =>
    intro t pre T hT hb
    cases t with
    | zero => exact absurd hb (by simp [OComp.QueryBound])
    | succ t =>
      have hb' : ∀ r, (k r).QueryBound t := hb
      have hlen : ∀ r : S.Rng o, (pre ++ [(⟨o, q, r⟩ : QA S)]).length = pre.length + 1 :=
        fun r => by simp
      have hsum : ∑ v ∈ Finset.range (t + 1), ε (pre.length + v)
          = (∑ v ∈ Finset.range t, ε (pre.length + 1 + v)) + ε pre.length := by
        rw [Finset.sum_range_succ']
        refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun v _ => ?_) rfl
        congr 1; omega
      have hrest : ∀ (r : S.Rng o) (T' : Table S), T'.Holds (pre ++ [⟨o, q, r⟩]) →
          ¬ step pre ⟨o, q, r⟩ →
          pr (((k r).withTrace.bind fun out =>
                OComp.pure (out.1, (⟨o, q, r⟩ : QA S) :: out.2)).runLazy T')
              {x | StepEventAfter step pre x.1.2} ≤
            ∑ v ∈ Finset.range t, ε (pre.length + 1 + v) := by
        intro r T' hT' hns
        rw [runLazy_withTrace_step, pr_map]
        have h := ih r t _ T' hT' (hb' r)
        rw [hlen r] at h
        refine le_trans (pr_mono _ ?_) h
        intro x hx
        rcases (stepEventAfter_cons step pre _ _).1 hx with h1 | h1
        · exact absurd h1 hns
        · exact h1
      rw [hsum]
      simp only [OComp.withTrace, OComp.runLazy]
      cases hTq : T o q with
      | some r =>
        exact (hrest r T (hT.concat_old hTq) (hold _ _ ((hT o q r).1 hTq))).trans le_self_add
      | none =>
        rw [add_comm]
        refine (pr_bind_le_add _ _ _ {r | step pre ⟨o, q, r⟩}
          (fun r _ hr => hrest r _ (hT.concat_new hTq r) hr)).trans ?_
        exact add_le_add (hnew pre o q fun r hr => by rw [← hT o q r, hTq] at hr; cases hr) le_rfl

/-- One count, from the empty table, under `hold` and `hnew`. An algorithm with at most t queries
causes the event with probability at most ε 0 + ... + ε (t - 1), over lazily sampled oracles and its
own coins. -/
theorem pr_stepEvent_le (step : Trace S → QA S → Prop) (ε : ℕ → ℝ≥0∞)
    (hold : ∀ (pre : Trace S) (e : QA S), e ∈ pre → ¬ step pre e)
    (hnew : ∀ (pre : Trace S) (o : S.ι) (q : S.Dom o),
      (∀ r, (⟨o, q, r⟩ : QA S) ∉ pre) → pr (unif (S.Rng o)) {r | step pre ⟨o, q, r⟩} ≤ ε pre.length)
    (A : OComp S α) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {x | StepEvent step x.2} ≤ ∑ v ∈ Finset.range t, ε v := by
  have h := pr_stepEventAfter_le step ε hold hnew A t [] (Table.empty S) Table.holds_empty hA
  simp only [List.length_nil, Nat.zero_add] at h
  rw [OComp.law, pr_map]
  refine le_trans (pr_mono _ ?_) h
  intro x hx
  exact (stepEvent_iff_after_nil step _).1 hx

end Rom
