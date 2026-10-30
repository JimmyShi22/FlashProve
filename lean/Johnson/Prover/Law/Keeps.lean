-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Keeps.lean: WHAT A LAZY RUN WRITES: if every query of an algorithm has the
property P, every table that its lazy run from T can return agrees with T wherever P fails. General
in the family of oracles. One theorem and a corollary.

Why. Rom.PrFrom_bind (Rom/EagerLazy.lean) hands on the table that the lazy run returns. Whoever
carries a sentence of the form "the table has no entry at these queries" along an algorithm needs to
know where a run can write.

Main names.
  keeps_of_asksIn   THE STATEMENT.
  none_of_asksIn   so an entry that is missing in T, at a query without P, is missing afterwards.

An earlier lemma: Rom.Derive.runLazy_avoids (Rom/Derive.lean): the same for a whole oracle that is
never asked (OComp.Avoids, Rom/SpecDerive.lean). Here the property reads the query too
(OComp.AsksIn, Rom/SigmaExits.lean): so it can part the queries to one oracle. The proof is
runLazy_avoids's, walked again.

Limits. On the support of the run's law alone: no probability. Nothing on which entries ARE
written.
Terms: lean/GLOSSARY.md.

-/
import Rom.EagerLazy
import Rom.AsksIn

set_option autoImplicit false

namespace OnBytes.Prover.Law
open Rom

variable {S : OSpec} {α : Type}

/-- A table with one more entry, at another query. -/
theorem set_other (T : Table S) {o o' : S.ι} {q : S.Dom o} {q' : S.Dom o'} (r : S.Rng o')
    (h : (⟨o, q⟩ : Σ o, S.Dom o) ≠ ⟨o', q'⟩) : T.set o' q' r o q = T o q := by
  by_cases ho : o = o'
  · subst ho
    have hq : q ≠ q' := fun e => h (by rw [e])
    simp [Table.set, Function.update_of_ne hq]
  · simp [Table.set, Function.update_of_ne ho]

/-- **If every query of c has P, a table that c's lazy run from T can return agrees with T wherever
P fails.** -/
theorem keeps_of_asksIn {P : (o : S.ι) → S.Dom o → Prop} (c : OComp S α) :
    c.AsksIn P → ∀ (T : Table S), ∀ x ∈ (c.runLazy T).support,
      ∀ (o : S.ι) (q : S.Dom o), ¬ P o q → x.2 o q = T o q := by
  induction c with
  | pure a =>
    intro _ T x hx o q _
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | query o' q' k ih =>
    intro hc T x hx o q hn
    cases hT : T o' q' with
    | some r =>
      simp only [OComp.runLazy, hT] at hx
      exact ih r (hc.2 r) T x hx o q hn
    | none =>
      simp only [OComp.runLazy, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      rw [ih r (hc.2 r) _ x hx o q hn]
      refine set_other T r fun e => hn ?_
      have h1 := hc.1
      cases e
      exact h1
  | sample n k ih =>
    intro hc T x hx o q hn
    simp only [OComp.runLazy, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hx⟩ := hx
    exact ih r (hc r) T x hx o q hn

/-- So an entry that is missing in T, at a query without P, is missing afterwards. -/
theorem none_of_asksIn {P : (o : S.ι) → S.Dom o → Prop} {c : OComp S α} (h : c.AsksIn P)
    {T : Table S} {x : α × Table S} (hx : x ∈ (c.runLazy T).support) {o : S.ι} {q : S.Dom o}
    (hn : ¬ P o q) (hT : T o q = none) : x.2 o q = none :=
  (keeps_of_asksIn c h T x hx o q hn).trans hT

end OnBytes.Prover.Law

#print axioms OnBytes.Prover.Law.set_other
#print axioms OnBytes.Prover.Law.keeps_of_asksIn
#print axioms OnBytes.Prover.Law.none_of_asksIn
