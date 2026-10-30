-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Stat.lean: the exact form of honest-verifier zero knowledge gives the statistical form. Proof of
`Iop.Spec.stat_of_exact` (stated in Ior/Honest.lean).

One theorem, on one IOR with its honest side (`IOR.Honest`, Ior/Honest.lean), and one helper lemma.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.

Let S simulate the honest side H exactly (`ExactWith`), let (x, y, w) be in the relation, and let
the set Hid w x have probability at most z. Draw ρ uniformly, then a set T of further positions by
any rule D that may read ρ and has coins of its own, and that stays within the budget. Then the
triple (ρ, T, what the honest run shows, or the notice (`none`) if ρ is withheld (`Honest.withheld`,
Ior/Honest.lean)) and the triple (ρ, T, what the simulator writes) are at statistical distance at
most z.

Why: both experiments begin with the same draw of ρ. For ρ outside Hid w x what follows has the same
law in both, because for every T that D can choose the two outputs have the same law. So the
distance is at most the probability that ρ falls into Hid w x.

Limits: the rule D does not see the prover's coins or the prover's messages: a reader who chooses
further positions after having seen symbols is not covered by this statement.
Terms: lean/GLOSSARY.md.
-/
import Ior.Honest
import Prob.Tv

set_option autoImplicit false

namespace Iop
open Prob IOR
open scoped ENNReal

/-- Two continuations that agree on every value that can be drawn give the same law. -/
private theorem bind_congr_support
    {α β : Type} (p : PMF α) {f g : α → PMF β} (h : ∀ a ∈ p.support, f a = g a) :
    p.bind f = p.bind g :=
  tv_eq_zero_iff.1 (le_antisymm
    (tv_bind_right_le_of_forall p f g fun a ha => by rw [h a ha, tv_self]) (zero_le _))

theorem stat_of_exact : Spec.stat_of_exact := by
  intro Xi Xo Ei Eo R Wi Wo H Ri bud S z hS x y w hR hz D hD
  refine le_trans (tv_bind_right_le_pr_ne _ _ _) (le_trans (pr_mono _ ?_) hz)
  intro ρ hρ
  by_contra hn
  exact hρ (bind_congr_support (D ρ) fun T hT => by rw [hS x y w hR ρ hn T (hD ρ T hT)])

end Iop
