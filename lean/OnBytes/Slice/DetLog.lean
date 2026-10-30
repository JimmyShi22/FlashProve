-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/DetLog.lean: the value of an algorithm under fixed oracle functions hangs on these
functions through the queries of its own log alone.

For a tie at one fixed hash that is patched at some strings (the format's realised oracle, with
another function's values put at strings that the format never asks): a checker whose own log holds
none of the patched strings has one value under both.

Main theorems: `log_query`, `log_sample` (the log of the run with every coin 0, unfolded);
`det_eq_of_log` (if g' answers every query of the log under g as g did, the value under g' is the
value under g); `log_eq_of_log` (and the log is the log under g); `det_eq_of_agree` (the same from a
set: g and g' agree on a set of queries that holds the log's).

General in the oracles' specification. `det` is the run with every coin 0: for an algorithm without
coins its one value. No probability.

-/
import Rom.Cache
import Rom.Prefix

set_option autoImplicit false

namespace OnBytes.Slice
open Rom

variable {S : OSpec} {α : Type}

/-- The log of a run that begins with a query: the query's entry, then the log of what follows. -/
theorem log_query (g : Fam S) (o : S.ι) (q : S.Dom o) (k : S.Rng o → OComp S α) :
    ((OComp.query o q k).withTrace.det g).2 =
      (⟨o, q, g o q⟩ : QA S) :: ((k (g o q)).withTrace.det g).2 := by
  show (((k (g o q)).withTrace.bind fun out =>
    OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).det g).2 = _
  rw [OComp.det_bind]
  rfl

/-- The log of a run that begins with a coin: the log of what follows the coin 0. -/
theorem log_sample (g : Fam S) (n : ℕ) (k : Fin (n + 1) → OComp S α) :
    ((OComp.sample n k).withTrace.det g).2 = ((k 0).withTrace.det g).2 := rfl

/-- **If g' answers every query of the log under g as g did, the value under g' is the value under
g.** -/
theorem det_eq_of_log (g g' : Fam S) (c : OComp S α)
    (h : ∀ e ∈ (c.withTrace.det g).2, g' e.1 e.2.1 = e.2.2) : c.det g' = c.det g := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
    rw [log_query] at h
    have h0 : g' o q = g o q := h ⟨o, q, g o q⟩ List.mem_cons_self
    show (k (g' o q)).det g' = (k (g o q)).det g
    rw [h0]
    exact ih _ fun e he => h e (List.mem_cons_of_mem _ he)
  | sample n k ih =>
    rw [log_sample] at h
    exact ih 0 h

/-- **So is the log**: under the same condition the run under g' has the log of the run under g. -/
theorem log_eq_of_log (g g' : Fam S) (c : OComp S α)
    (h : ∀ e ∈ (c.withTrace.det g).2, g' e.1 e.2.1 = e.2.2) :
    (c.withTrace.det g').2 = (c.withTrace.det g).2 := by
  induction c with
  | pure a => rfl
  | query o q k ih =>
    rw [log_query] at h
    have h0 : g' o q = g o q := h ⟨o, q, g o q⟩ List.mem_cons_self
    rw [log_query, log_query, h0]
    exact congrArg _ (ih _ fun e he => h e (List.mem_cons_of_mem _ he))
  | sample n k ih =>
    rw [log_sample] at h
    rw [log_sample, log_sample]
    exact ih 0 h

/-- Every entry of the log of the run with every coin 0 holds g's own answer. -/
theorem log_ans (g : Fam S) (c : OComp S α) :
    ∀ e ∈ (c.withTrace.det g).2, e.2.2 = g e.1 e.2.1 := by
  induction c with
  | pure a => exact fun e he => absurd he List.not_mem_nil
  | query o q k ih =>
    intro e he
    rw [log_query] at he
    rcases List.mem_cons.1 he with rfl | h
    · rfl
    · exact ih _ e h
  | sample n k ih =>
    intro e he
    rw [log_sample] at he
    exact ih 0 e he

/-- **The same from a set of queries**: g and g' agree wherever P holds, and P holds of every query
of the log under g. -/
theorem det_eq_of_agree (g g' : Fam S) (c : OComp S α) (P : (o : S.ι) → S.Dom o → Prop)
    (hP : ∀ e ∈ (c.withTrace.det g).2, P e.1 e.2.1) (hg : ∀ o q, P o q → g' o q = g o q) :
    c.det g' = c.det g :=
  det_eq_of_log g g' c fun e he => (hg e.1 e.2.1 (hP e he)).trans (log_ans g c e he).symm

end OnBytes.Slice

#print axioms OnBytes.Slice.det_eq_of_log
#print axioms OnBytes.Slice.log_eq_of_log
#print axioms OnBytes.Slice.det_eq_of_agree
