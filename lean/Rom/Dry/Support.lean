-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Dry/Support.lean: WHAT EVERY REPLAY OF A DRY RUN's RECORDED ANSWERS LOOKS LIKE, outcome by
outcome. General in the family of oracles.

General lemmas. This file states no goal of the release.

record_runReplay (Rom/Handle/Laws.lean) is an equality of joint laws. Here is what it says of single
outcomes, for use where the algorithm that replays is chosen AFTER the dry run's output has been
seen, so that the joint law cannot be applied at once.

Main names.
  support_record_runReplay   c and c' ask their deferred queries in step, and c's output is φ of
      c' 's. Then for every (output, recorded answers) that a dry run of c can give, and every end
      that a replay of these answers at c' can have: the output is φ of the replay's; the answers
      are used up; no query has failed to find its answer.
  map_some_inj               two laws with the same image under "some" are the same.

Limits. Nothing here says when two algorithms ask their deferred queries in step.
Terms: lean/GLOSSARY.md.

-/
import Rom.Handle.Laws

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {α β γ : Type}

theorem OComp.support_record_runReplay {mk : Mark S} {R : α → β → Prop} {φ : β → α}
    (hR : ∀ a b, R a b → a = φ b) {c : OComp S α} {c' : OComp S β} (hc : InStep mk R c c')
    (T : Table S) (lg : Trace S) :
    ∀ x ∈ (c.record mk).support, ∀ y ∈ (c'.runReplay mk T lg x.2).support,
      x.1 = φ y.1 ∧ y.2.left = [] ∧ y.2.miss = false := by
  intro x hx y hy
  have hmem : (x, y) ∈ ((c.record mk).bind fun x =>
      (c'.runReplay mk T lg x.2).map fun y => (x, y)).support := by
    simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff]
    exact ⟨x, hx, y, hy, rfl⟩
  rw [OComp.record_runReplay hR hc T lg] at hmem
  simp only [PMF.mem_support_map_iff] at hmem
  obtain ⟨y₀, -, h⟩ := hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  exact ⟨rfl, rfl, rfl⟩

theorem map_some_inj {P Q : PMF γ} (h : P.map some = Q.map some) : P = Q :=
  PMF.ext fun a => by
    have e : ∀ U : PMF γ, U a = pr (U.map some) {some a} := fun U => by
      rw [pr_map, ← pr_singleton]
      refine congrArg (pr U) (Set.ext fun b => ?_)
      simp
    rw [e P, e Q, h]

end Rom

#print axioms Rom.OComp.support_record_runReplay
#print axioms Rom.map_some_inj
