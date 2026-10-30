-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Dry/Val.lean: THE OUTPUT OF A DRY RUN, AS A LAW OF ITS OWN; and two algorithms that ask the same
oracles one after the other. General in the family of oracles.

General lemmas. This file states no goal of the release.

A dry run (OComp.record, Rom/Handle/Defs.lean) answers a deferred query by a fresh uniform value,
whatever its point is, and every other query by an arbitrary fixed value; it has no table. It
returns the output and the list of the fresh answers. Where only the OUTPUT is asked about, the
log is in the way. Here is the same run without a log.

Main names.
  Handler.dry mk     the rule of a dry run, without a log: its state is Unit.
  OComp.dryVal mk    the law of the output under that rule.
  Handler.dry_of_mark, Handler.dry_of_not   that rule at a deferred query; at another.
  record_fst         it is the law of the output of OComp.record (pr_record: for an event).
  record_bind_pure   a dry run whose output is cut by a function gives the same answers.
  dryVal_pure, dryVal_bind, dryVal_query_mark, dryVal_query_plain   it goes along a program step by
                     step: "c, then g" is "the law of c, then the law of g".
  pr_dryVal_bind_le, pr_dryVal_bind_pure   two steps for a bound on an event.
  InStep.query_query   where the test for "deferred" looks at the oracle's name alone: two
                     algorithms that both begin with a query to one oracle are in step (InStep,
                     Rom/Handle/Defs.lean) if what follows is in step: at one and the same answer if
                     that oracle is deferred, at any two answers if it is not.
  InStep.map_left    the left algorithm's output cut by a function.

Limits. Nothing here speaks of a table or of a log.
Terms: lean/GLOSSARY.md.

-/
import Rom.Handle.Laws

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
open scoped ENNReal
variable {S : OSpec} {α β : Type}

/-- The rule of a dry run, without a log: a deferred query gets a fresh uniform answer, every other
query an arbitrary fixed value. -/
def Handler.dry (mk : Mark S) : Handler S Unit := fun _ o q =>
  if mk o q then (unif (S.Rng o)).map fun r => (r, ()) else PMF.pure (Classical.arbitrary _, ())

theorem Handler.dry_of_mark (mk : Mark S) {o : S.ι} {q : S.Dom o} (hm : mk o q = true) (u : Unit) :
    Handler.dry mk u o q = (unif (S.Rng o)).map fun r => (r, ()) :=
  if_pos hm

theorem Handler.dry_of_not (mk : Mark S) {o : S.ι} {q : S.Dom o} (hm : mk o q = false) (u : Unit) :
    Handler.dry mk u o q = PMF.pure (Classical.arbitrary _, ()) :=
  if_neg (by rw [hm]; exact Bool.false_ne_true)

/-- **The law of the output of a dry run.** -/
def OComp.dryVal (mk : Mark S) (c : OComp S α) : PMF α :=
  (c.interp (Handler.dry mk) ()).map Prod.fst

namespace OComp
variable (mk : Mark S)

theorem dryVal_pure (a : α) : (OComp.pure a : OComp S α).dryVal mk = PMF.pure a := by
  simp only [dryVal, interp_pure, PMF.pure_map]

/-- "c, then g": the law of c, then the law of g. -/
theorem dryVal_bind (c : OComp S α) (g : α → OComp S β) :
    (c.bind g).dryVal mk = (c.dryVal mk).bind fun a => (g a).dryVal mk := by
  simp only [dryVal, interp_bind, PMF.map_bind, PMF.bind_map, Function.comp_def]

theorem dryVal_query_mark {o : S.ι} {q : S.Dom o} (hm : mk o q = true)
    (k : S.Rng o → OComp S α) :
    (OComp.query o q k).dryVal mk = (unif (S.Rng o)).bind fun r => (k r).dryVal mk := by
  simp only [dryVal, interp_query, Handler.dry_of_mark mk hm, PMF.map_bind, PMF.bind_map,
    Function.comp_def]

theorem dryVal_query_plain {o : S.ι} {q : S.Dom o} (hm : mk o q = false)
    (k : S.Rng o → OComp S α) :
    (OComp.query o q k).dryVal mk = (k (Classical.arbitrary _)).dryVal mk := by
  simp only [dryVal, interp_query, Handler.dry_of_not mk hm, PMF.pure_bind]

/-- **It is the law of the output of the dry run that keeps its answers.** -/
theorem record_fst (c : OComp S α) : (c.record mk).map Prod.fst = c.dryVal mk := by
  have hφ : ∀ (s : Unit × Trace S) (o : S.ι) (q : S.Dom o),
      (Handler.defer mk Handler.idle s o q).map (fun p => (p.1, ())) =
        Handler.dry mk () o q := by
    rintro ⟨b, l⟩ o q
    cases hm : mk o q with
    | false =>
      rw [Handler.defer_of_not Handler.idle hm, Handler.dry_of_not mk hm]
      simp only [Handler.idle, Handler.fixed, PMF.pure_map]
    | true =>
      simp only [Handler.defer_of_mark Handler.idle hm, Handler.dry_of_mark mk hm, PMF.map_comp,
        Function.comp_def]
  have e : (c.interp (Handler.defer mk Handler.idle) ((), [])).map (fun x => (x.1, ())) =
      c.interp (Handler.dry mk) () :=
    interp_map_state (Handler.defer mk Handler.idle) (Handler.dry mk) (fun _ => ()) hφ c ((), [])
  simp only [dryVal, ← e, record, PMF.map_comp, Function.comp_def]

/-- The output cut by a function: the same recorded answers. -/
theorem record_bind_pure (c : OComp S α) (f : α → β) :
    (c.bind fun a => .pure (f a)).record mk = (c.record mk).map fun z => (f z.1, z.2) := by
  simp only [record, interp_bind, interp_pure, PMF.map_bind, PMF.pure_map, PMF.map_comp,
    Function.comp_def] <;> rfl

/-- An event of the output alone has the same probability in both. -/
theorem pr_record (c : OComp S α) (E : Set α) :
    pr (c.record mk) {z | z.1 ∈ E} = pr (c.dryVal mk) E := by
  rw [← record_fst, pr_map]
  rfl

/-- A bound that holds after every first part holds for the two parts together. -/
theorem pr_dryVal_bind_le (c : OComp S α) (g : α → OComp S β) (E : Set β) {ε : ℝ≥0∞}
    (h : ∀ a, pr ((g a).dryVal mk) E ≤ ε) : pr ((c.bind g).dryVal mk) E ≤ ε := by
  rw [dryVal_bind]
  exact pr_bind_le_of_forall _ _ _ fun a _ => h a

theorem pr_dryVal_bind_pure (c : OComp S α) (f : α → β) (E : Set β) :
    pr ((c.bind fun a => .pure (f a)).dryVal mk) E = pr (c.dryVal mk) (f ⁻¹' E) := by
  rw [dryVal_bind, ← pr_map]
  simp only [dryVal_pure]
  rfl

end OComp

/-- Where "deferred" goes by the oracle's name: two algorithms that both begin with a query to the
oracle o are in step if what follows is: at one answer if o is deferred, at any two if not. -/
theorem InStep.query_query {m : S.ι → Bool} {R : α → β → Prop} {o : S.ι} {q q' : S.Dom o}
    {k : S.Rng o → OComp S α} {k' : S.Rng o → OComp S β}
    (h : ∀ r r', (m o = true → r = r') → InStep (fun o _ => m o) R (k r) (k' r')) :
    InStep (fun o _ => m o) R (.query o q k) (.query o q' k') := by
  cases hm : m o with
  | false =>
    exact .plainL hm fun r => .plainR hm fun r' => h r r' fun e => by
      rw [hm] at e
      exact absurd e Bool.false_ne_true
  | true => exact .both hm hm fun r => h r r fun _ => rfl

/-- The left algorithm's output cut by a function f. -/
theorem InStep.map_left {γ : Type} {mk : Mark S} {R : α → β → Prop} {R' : γ → β → Prop} {f : α → γ}
    {c : OComp S α} {c' : OComp S β} (hc : InStep mk R c c') (h : ∀ a b, R a b → R' (f a) b) :
    InStep mk R' (c.bind fun a => .pure (f a)) c' := by
  induction hc with
  | done hab => exact .done (h _ _ hab)
  | drawL _ ih => exact .drawL ih
  | drawR _ ih => exact .drawR ih
  | plainL hm _ ih => exact .plainL hm ih
  | plainR hm _ ih => exact .plainR hm ih
  | both hm hm' _ ih => exact .both hm hm' ih

end Rom

#print axioms Rom.OComp.record_fst
#print axioms Rom.OComp.record_bind_pure
#print axioms Rom.OComp.pr_dryVal_bind_le
#print axioms Rom.InStep.query_query
#print axioms Rom.InStep.map_left
