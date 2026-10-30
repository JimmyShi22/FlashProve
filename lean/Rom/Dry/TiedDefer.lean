-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Dry/TiedDefer.lean: TWO ORACLE ALGORITHMS THAT GO SIDE BY SIDE (TiedL, Rom/Dry/Tied.lean), RUN
WITH THEIR DEFERRED QUERIES ANSWERED AFRESH (Handler.defer, Rom/Handle/Defs.lean); and what a run
with deferred queries leaves of a lazily sampled table. General in the family of oracles. Theorems
with their proofs.

General lemmas. This file states no goal of the release.

  TiedL.map_defer     THE LAW, the twin of TiedL.map_replay: runs from one state of the rule for the
      plain queries, with the logs l and l': whatever function of (output, last state) takes the
      same value at all outputs and logs that the relation relates has THE SAME LAW in both runs. It
      follows the pattern of TiedL.map_replay.
  runDefer_avoids     after a run of an algorithm that never asks the oracle o the table's column o
      is as it was.
Terms: lean/GLOSSARY.md.

-/
import Rom.Dry.Tied
import Rom.Derive

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {σ α β γ : Type}

/-- **Runs with deferred queries answered afresh, from one state of the rule for the plain
queries.** -/
theorem TiedL.map_defer {mk : Mark S} (h : Handler S σ)
    {R : α → Trace S → β → Trace S → Prop} {H : α × σ × Trace S → γ} {H' : β × σ × Trace S → γ}
    (hH : ∀ a l b l', R a l b l' → ∀ s : σ, H (a, s, l) = H' (b, s, l'))
    {l l' : Trace S} {c : OComp S α} {c' : OComp S β} (hc : TiedL mk R l l' c c') :
    ∀ s : σ, (c.interp (Handler.defer mk h) (s, l)).map H =
      (c'.interp (Handler.defer mk h) (s, l')).map H' := by
  induction hc with
  | done hab =>
    intro s
    simp only [OComp.interp_pure, PMF.pure_map]
    rw [hH _ _ _ _ hab]
  | plain hm _ ih =>
    intro s
    simp only [OComp.interp_query, Handler.defer_of_not h hm, PMF.bind_map, PMF.map_bind,
      Function.comp_def, ih]
  | both hm hm' _ ih =>
    intro s
    simp only [OComp.interp_query, Handler.defer_of_mark h hm, Handler.defer_of_mark h hm',
      PMF.bind_map, PMF.map_bind, Function.comp_def, ih]
  | draw _ ih =>
    intro s
    simp only [OComp.interp_sample, PMF.map_bind, ih]

/-- what lazy sampling leaves of a table's other columns -/
theorem lazyAnswer_other {T : Table S} {o o' : S.ι} (ho : o ≠ o') (q : S.Dom o) :
    ∀ x ∈ (lazyAnswer T o q).support, x.2 o' = T o' := by
  intro x hx
  unfold lazyAnswer at hx
  cases hT : T o q with
  | some r =>
    rw [hT] at hx
    rw [(PMF.mem_support_pure_iff _ _).mp hx]
  | none =>
    rw [hT] at hx
    obtain ⟨r, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    exact Derive.set_of_ne_oracle T (Ne.symm ho) q r

/-- **After a run of an algorithm that never asks o the table's column o is as it was.** -/
theorem runDefer_avoids (mk : Mark S) (o : S.ι) : ∀ (c : OComp S α), c.Avoids o →
    ∀ (T : Table S) (lg : Trace S), ∀ x ∈ (c.runDefer mk T lg).support, x.2.1 o = T o := by
  intro c
  induction c with
  | pure a =>
    intro _ T lg x hx
    rw [(PMF.mem_support_pure_iff _ _).mp hx]
  | sample n k ih =>
    intro hc T lg x hx
    obtain ⟨r, _, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    exact ih r (hc r) T lg x hr
  | query o' q k ih =>
    intro hc T lg x hx
    obtain ⟨p, hp, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    cases hm : mk o' q with
    | true =>
      rw [Handler.defer_of_mark Handler.lazy hm] at hp
      obtain ⟨r, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      exact ih r (hc.2 r) T _ x hr
    | false =>
      rw [Handler.defer_of_not Handler.lazy hm] at hp
      obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
      rw [ih y.1 (hc.2 y.1) y.2 lg x hr]
      exact lazyAnswer_other hc.1 q y hy

end Rom

#print axioms Rom.TiedL.map_defer
#print axioms Rom.runDefer_avoids
