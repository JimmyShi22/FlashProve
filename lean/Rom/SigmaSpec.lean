-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SigmaSpec.lean: many families of oracles side by side (`OSpec.sigma`), and one union bound over
the queries for all of them together (`pr_stepEvent_sigma_le`). Generic; built on Rom/OneCount.lean.

Why. A scheme may come as a family of schemes A t, one for each value t of a public parameter, each
over its own family of oracles S t whose very types depend on t. A theorem "for every t" fixes t
before the oracles are sampled. An adversary that picks t late, after queries, is an algorithm over
all the families at once. This file has that family and the one probabilistic fact on it.

`OSpec.sigma S S₀`, "the whole" in the comments, is the family of all oracles of all S t, and of one
more family S₀ that belongs to no t (for queries that belong to no scheme: the step to one hash
function on strings needs every string to encode a query). All oracles are independent, as in every
family.

  `stepEvent_sigma`        If t's event has happened in the entries at t, the event of the whole
                           (`stepSigma`) has happened.
  `pr_stepEvent_sigma_le`  If at each t an entry that is already in the trace never causes t's event
                           (hold), and a new query causes it with probability at most ε (number of
                           entries before it) (hnew), ε monotone (hε), then an algorithm with n
                           queries in all, spread over the t as it likes and as late as it likes,
                           causes the event of some t with probability at most ε 0 + .. + ε (n − 1):
                           the bound for one t.
  `stepSigma_hold`, `stepSigma_hnew`
                           The two hypotheses of `pr_stepEvent_le` (Rom/OneCount.lean), for the
                           event of the whole. (No other file of this library uses these two;
                           `pr_stepEvent_sigma_le` is `pr_stepEvent_le` with these two, stated for
                           the union of the events, for the reader.)

Limits: nothing on any scheme. From a bound "for every algorithm with n queries" at each single t no
such bound for all t follows (argued by hand, not in Lean): the hypothesis here is on a single
query. Of "the event of the whole is the union of the events of the t" one inclusion is proved, the
one that is needed (`stepEvent_sigma`).
-/
import Rom.OneCount

open scoped ENNReal
open Prob

namespace Rom
variable {T : Type} [DecidableEq T] {α β : Type}

/-- All oracles of all families S t, and those of S₀. An oracle is inl (t, an oracle of S t) or inr
(an oracle of S₀). -/
def OSpec.sigma (S : T → OSpec) (S₀ : OSpec) : OSpec where
  ι := (Σ t, (S t).ι) ⊕ S₀.ι
  Dom := fun x => match x with
    | .inl o => (S o.1).Dom o.2
    | .inr o => S₀.Dom o
  Rng := fun x => match x with
    | .inl o => (S o.1).Rng o.2
    | .inr o => S₀.Rng o
  finRng := fun x => match x with
    | .inl o => (S o.1).finRng o.2
    | .inr o => S₀.finRng o
  neRng := fun x => match x with
    | .inl o => (S o.1).neRng o.2
    | .inr o => S₀.neRng o

variable {S : T → OSpec} (S₀ : OSpec)

/-- an entry at t, as an entry of the whole -/
def QA.inT (t : T) (e : QA (S t)) : QA (OSpec.sigma S S₀) := ⟨.inl ⟨t, e.1⟩, e.2.1, e.2.2⟩

/-- the entry, if it is one at t -/
def QA.atT (t : T) : QA (OSpec.sigma S S₀) → Option (QA (S t))
  | ⟨.inl ⟨t', o⟩, q, r⟩ => if h : t' = t then some (h ▸ (⟨o, q, r⟩ : QA (S t'))) else none
  | ⟨.inr _, _, _⟩ => none

/-- the entries at t of a trace of the whole, in their order -/
def Trace.atT (t : T) (tr : Trace (OSpec.sigma S S₀)) : Trace (S t) := tr.filterMap (QA.atT S₀ t)

/-- an algorithm over S t, as an algorithm over the whole: the same tree -/
def OComp.inT (t : T) : OComp (S t) α → OComp (OSpec.sigma S S₀) α
  | .pure a => .pure a
  | .query o q k => .query (S := OSpec.sigma S S₀) (.inl ⟨t, o⟩) q fun r => (k r).inT t
  | .sample n k => .sample n fun r => (k r).inT t

/-- From an event that is defined query by query for each t (`step t pre e`, Rom/OneCount.lean), the
event of the whole: an entry at t causes the event of t, after the entries at t before it; an entry
at S₀ causes nothing. -/
def stepSigma (step : ∀ t, Trace (S t) → QA (S t) → Prop) (pre : Trace (OSpec.sigma S S₀)) :
    QA (OSpec.sigma S S₀) → Prop
  | ⟨.inl ⟨t, o⟩, q, r⟩ => step t (Trace.atT S₀ t pre) ⟨o, q, r⟩
  | ⟨.inr _, _, _⟩ => False

variable {S₀}

theorem QA.atT_inT (t : T) (e : QA (S t)) : QA.atT S₀ t (QA.inT S₀ t e) = some e := dif_pos rfl

theorem QA.atT_eq_some {t : T} {e : QA (OSpec.sigma S S₀)}
    {e' : QA (S t)} (h : QA.atT S₀ t e = some e') : e = QA.inT S₀ t e' := by
  obtain ⟨⟨t', o⟩ | o, q, r⟩ := e
  · have h' : (if hh : t' = t then some (hh ▸ (⟨o, q, r⟩ : QA (S t'))) else none) = some e' := h
    by_cases ht : t' = t
    · subst ht
      rw [dif_pos rfl] at h'
      exact (Option.some.inj h') ▸ rfl
    · rw [dif_neg ht] at h'
      cases h'
  · have h' : (none : Option (QA (S t))) = some e' := h
    cases h'

theorem Trace.atT_append (t : T) (a b : Trace (OSpec.sigma S S₀)) :
    Trace.atT S₀ t (a ++ b) = Trace.atT S₀ t a ++ Trace.atT S₀ t b :=
  List.filterMap_append

theorem Trace.atT_cons_inT (t : T) (e : QA (S t)) (tr : Trace (OSpec.sigma S S₀)) :
    Trace.atT S₀ t (QA.inT S₀ t e :: tr) = e :: Trace.atT S₀ t tr := by
  unfold Trace.atT
  rw [List.filterMap_cons, QA.atT_inT]

theorem Trace.mem_atT {t : T} {e : QA (S t)} {tr : Trace (OSpec.sigma S S₀)} :
    e ∈ Trace.atT S₀ t tr ↔ QA.inT S₀ t e ∈ tr := by
  unfold Trace.atT
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩
    exact (QA.atT_eq_some h) ▸ ha
  · exact fun h => ⟨_, h, QA.atT_inT t e⟩

theorem Trace.length_atT_le (t : T) (tr : Trace (OSpec.sigma S S₀)) :
    (Trace.atT S₀ t tr).length ≤ tr.length :=
  List.length_filterMap_le _ _

theorem OComp.inT_bind (t : T) (c : OComp (S t) α) (g : α → OComp (S t) β) :
    (c.bind g).inT S₀ t = (c.inT S₀ t).bind fun a => (g a).inT S₀ t := by
  induction c with
  | pure a => rfl
  | query o q k ih => simp only [OComp.bind, OComp.inT, ih]
  | sample n k ih => simp only [OComp.bind, OComp.inT, ih]

theorem OComp.QueryBound.inT (t : T) :
    ∀ (c : OComp (S t) α) (n : ℕ), c.QueryBound n → (c.inT S₀ t).QueryBound n
  | .pure _, _, _ => trivial
  | .query _ _ _, 0, h => h.elim
  | .query _ _ k, n + 1, h => fun r => OComp.QueryBound.inT t (k r) n (h r)
  | .sample _ k, n, h => fun r => OComp.QueryBound.inT t (k r) n (h r)

theorem stepEvent_sigma (step : ∀ t, Trace (S t) → QA (S t) → Prop) (t : T)
    (tr : Trace (OSpec.sigma S S₀)) (h : StepEvent (step t) (Trace.atT S₀ t tr)) :
    StepEvent (stepSigma S₀ step) tr := by
  obtain ⟨pre, e, post, h, hs⟩ := h
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.filterMap_eq_append_iff.1 h
  obtain ⟨l₃, a, l₄, rfl, h3, h4, -⟩ := List.filterMap_eq_cons_iff.1 h2
  refine ⟨l₁ ++ l₃, a, l₄, by simp, ?_⟩
  have ea := QA.atT_eq_some h4
  subst ea
  show step t (Trace.atT S₀ t (l₁ ++ l₃)) e
  have : Trace.atT S₀ t (l₁ ++ l₃) = pre := by
    unfold Trace.atT
    rw [List.filterMap_append, h1, List.filterMap_eq_nil_iff.2 h3, List.append_nil]
  rw [this]
  exact hs

theorem stepSigma_hold {step : ∀ t, Trace (S t) → QA (S t) → Prop}
    (hold : ∀ t (pre : Trace (S t)) (e : QA (S t)), e ∈ pre → ¬ step t pre e)
    (pre : Trace (OSpec.sigma S S₀)) (e : QA (OSpec.sigma S S₀)) (he : e ∈ pre) :
    ¬ stepSigma S₀ step pre e := by
  obtain ⟨⟨t, o⟩ | o, q, r⟩ := e
  · exact hold t _ _ (Trace.mem_atT.2 he)
  · exact fun h => h

theorem stepSigma_hnew {step : ∀ t, Trace (S t) → QA (S t) → Prop} {ε : ℕ → ℝ≥0∞} (hε : Monotone ε)
    (hnew : ∀ t (pre : Trace (S t)) (o : (S t).ι) (q : (S t).Dom o),
      (∀ r, (⟨o, q, r⟩ : QA (S t)) ∉ pre) →
      pr (unif ((S t).Rng o)) {r | step t pre ⟨o, q, r⟩} ≤ ε pre.length)
    (pre : Trace (OSpec.sigma S S₀)) (o : (OSpec.sigma S S₀).ι) (q : (OSpec.sigma S S₀).Dom o)
    (hq : ∀ r, (⟨o, q, r⟩ : QA (OSpec.sigma S S₀)) ∉ pre) :
    pr (unif ((OSpec.sigma S S₀).Rng o)) {r | stepSigma S₀ step pre ⟨o, q, r⟩} ≤ ε pre.length := by
  obtain ⟨t, o⟩ | o := o
  · exact le_trans (hnew t (Trace.atT S₀ t pre) o q fun r hr => hq r (Trace.mem_atT.1 hr))
      (hε (Trace.length_atT_le t pre))
  · exact le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)) (zero_le _)

/-- One union bound for all t together, under hold, hnew and monotone ε: an algorithm with n queries
in all causes the event of some t with probability at most ε 0 + .. + ε (n − 1). -/
theorem pr_stepEvent_sigma_le (step : ∀ t, Trace (S t) → QA (S t) → Prop) (ε : ℕ → ℝ≥0∞)
    (hε : Monotone ε) (hold : ∀ t (pre : Trace (S t)) (e : QA (S t)), e ∈ pre → ¬ step t pre e)
    (hnew : ∀ t (pre : Trace (S t)) (o : (S t).ι) (q : (S t).Dom o),
      (∀ r, (⟨o, q, r⟩ : QA (S t)) ∉ pre) →
      pr (unif ((S t).Rng o)) {r | step t pre ⟨o, q, r⟩} ≤ ε pre.length)
    (A : OComp (OSpec.sigma S S₀) α) (n : ℕ) (hA : A.QueryBound n) :
    pr A.withTrace.law {x | ∃ t, StepEvent (step t) (Trace.atT S₀ t x.2)} ≤
      ∑ v ∈ Finset.range n, ε v :=
  le_trans (pr_mono _ fun x ⟨t, h⟩ => stepEvent_sigma step t x.2 h)
    (pr_stepEvent_le (S := OSpec.sigma S S₀) (stepSigma S₀ step) ε (stepSigma_hold hold)
      (stepSigma_hnew hε hnew) A n hA)

end Rom
