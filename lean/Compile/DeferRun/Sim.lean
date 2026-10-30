-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DeferRun/Sim.lean: A TOKEN PROGRAM IN MODE I, PART BY PART, AGAINST A LAW ON (value, plain
state). One definition and its calculus. General in the family of oracles.

General lemmas. This file states no goal of the release.

A token program's output holds tokens; what it stands for is read off the state at the end (the
store of strings). The plain side speaks of values and of a plain state (a table). To compare the
two part by part one carries, for each part, what is known of the outcome.

  SimAt tb c D ψ R κ   from the state D, in mode I (Rom/Defer.lean): the run of c, its output a read
                       off the end state D' as ψ a D' and D' cut to the plain state tb D', has the
                       law κ; and every outcome has R a D'.
  SimAt.pure, .sample, .bind   constructor by constructor. In .bind what follows is compared from
                       each outcome (a, D') of the first part, against a law that is handed the
                       VALUE ψ a D' and the plain state tb D'.
  SimAt.mono, .out, .congr     a weaker R; another read-off that agrees where R holds; an equal law.
  SimAt.prefix         the store only grows: that joins R.

-/
import Compile.Step1_life2_Virt
import Compile.Step1_life2_Chall

set_option autoImplicit false

noncomputable section

namespace Compile
namespace DeferRun
open Rom Prob

variable {S : OSpec} {sp : Split S} {τ α β α' β' : Type} (tb : DSt S → τ)

/-- See the head. -/
structure SimAt (c : Step S sp α) (D : DSt S) (ψ : α → DSt S → β) (R : α → DSt S → Prop)
    (κ : PMF (β × τ)) : Prop where
  law : ((c.run true D).map fun v => (ψ v.1 v.2, tb v.2)) = κ
  post : ∀ v ∈ (c.run true D).support, R v.1 v.2

namespace SimAt
variable {tb}
variable {D : DSt S} {ψ : α → DSt S → β} {R : α → DSt S → Prop} {κ : PMF (β × τ)}

theorem pure {a : α} (hR : R a D) (e : κ = PMF.pure (ψ a D, tb D)) :
    SimAt tb (Step.pure a : Step S sp α) D ψ R κ where
  law := by
    rw [e]
    exact PMF.pure_map _ _
  post := fun v hv => by
    have hv' : v = (a, D) := (PMF.mem_support_pure_iff _ _).1 hv
    rw [hv']
    exact hR

theorem sample {n : ℕ} {k : Fin (n + 1) → Step S sp α} {κs : Fin (n + 1) → PMF (β × τ)}
    (h : ∀ r, SimAt tb (k r) D ψ R (κs r)) :
    SimAt tb (Step.sample n k) D ψ R ((unif (Fin (n + 1))).bind κs) where
  law := by
    show (((unif (Fin (n + 1))).bind fun r => (k r).run true D).map _) = _
    rw [PMF.map_bind]
    exact congrArg _ (funext fun r => (h r).law)
  post := fun v hv => by
    have hv' : v ∈ ((unif (Fin (n + 1))).bind fun r => (k r).run true D).support := hv
    obtain ⟨r, _, hr⟩ := (PMF.mem_support_bind_iff _ _ _).1 hv'
    exact (h r).post v hr

/-- **Sequential composition.** -/
theorem bind {c : Step S sp α} {g : α → Step S sp α'} {ψ' : α' → DSt S → β'}
    {R' : α' → DSt S → Prop} {k' : β → τ → PMF (β' × τ)} (h1 : SimAt tb c D ψ R κ)
    (h2 : ∀ a D', R a D' → SimAt tb (g a) D' ψ' R' (k' (ψ a D') (tb D'))) :
    SimAt tb (c.bind g) D ψ' R' (κ.bind fun o => k' o.1 o.2) where
  law := by
    rw [Life2.run_bind, PMF.map_bind, ← h1.law, PMF.bind_map]
    exact Rom.bind_congr_support _ fun v hv => (h2 v.1 v.2 (h1.post v hv)).law
  post := fun v hv => by
    rw [Life2.run_bind] at hv
    obtain ⟨u, hu, hv⟩ := (PMF.mem_support_bind_iff _ _ _).1 hv
    exact (h2 u.1 u.2 (h1.post u hu)).post v hv

theorem mono {c : Step S sp α} {R' : α → DSt S → Prop} (h : SimAt tb c D ψ R κ)
    (hR : ∀ a D', R a D' → R' a D') : SimAt tb c D ψ R' κ :=
  ⟨h.law, fun v hv => hR _ _ (h.post v hv)⟩

/-- Another read-off, equal where R holds. -/
theorem out {c : Step S sp α} {ψ' : α → DSt S → β} (h : SimAt tb c D ψ R κ)
    (hψ : ∀ a D', R a D' → ψ' a D' = ψ a D') : SimAt tb c D ψ' R κ where
  law := by
    rw [← h.law]
    refine Rom.bind_congr_support _ fun v hv => ?_
    show PMF.pure (ψ' v.1 v.2, tb v.2) = PMF.pure (ψ v.1 v.2, tb v.2)
    rw [hψ _ _ (h.post v hv)]
  post := h.post

theorem congr {c : Step S sp α} {κ' : PMF (β × τ)} (h : SimAt tb c D ψ R κ) (e : κ' = κ) :
    SimAt tb c D ψ R κ' := e ▸ h

/-- The store only grows. -/
theorem «prefix» {c : Step S sp α} (h : SimAt tb c D ψ R κ) :
    SimAt tb c D ψ (fun a D' => R a D' ∧ D.vals <+: D'.vals) κ :=
  ⟨h.law, fun v hv => ⟨h.post v hv, Life2.vals_prefix true c D v hv⟩⟩

end SimAt

end DeferRun
end Compile

#print axioms Compile.DeferRun.SimAt.bind
