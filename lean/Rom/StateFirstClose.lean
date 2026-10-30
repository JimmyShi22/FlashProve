-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstClose.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): the proof of its main lemma, `Spec.mixClose` (stated in
Rom/StateFirstMix.lean).

  `ghost_empty`
              The relation `Ghost` at empty tables and no hidden query (`Ghost`, `Psi`, `avgH`:
              Rom/StateFirstHitDef.lean).
  `mixClose`  For every mixed program (`mixSpec`: typed queries to the family before the step, raw
              queries to the family after it) with at most nT typed queries at chain oracles and nR
              raw queries, whose typed continuations do not depend on hid (the last block of a chain
              answer), and every event E: Pr[real interpretation ∈ E] ≤ Pr[the reduction's
              interpretation ∈ E] + (nT + nR)² / 2^(2 lam) + nR nT / 2^lam.

`mainLe` (Rom/StateFirstMain.lean) at empty tables gives the collision term and Psi; `psiLe`
(Rom/StateFirstHit.lean) at no hidden query, where the average is Psi itself, bounds Psi. `real` and
`real'` return the same for every fixed family (`runEager_real'`).

Notation:
  `Ghost C T bT bF H` (Rom/StateFirstHitDef.lean): the relation between the reduction's table bF,
      the table bT of all chain answers and the hidden queries H; T: a `Table S`
  `real` (Rom/StateFirstMix.lean): the real interpretation: typed queries are expanded (state, then
      expansion queries); raw queries stay
  `real'` (Rom/StateFirstMix.lean): the real interpretation in which a raw query for a state is also
      followed by the expansion queries, whose answers are discarded

Limits: one-sided for each event; the other side follows by the complement where it is used
(Rom/StateFirstPriv.lean). Nothing on a scheme.
-/
import Rom.StateFirstMain
import Rom.StateFirstHit

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

theorem ghost_empty {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) :
    Ghost C (Table.empty S) ⟨[], []⟩ ⟨[], []⟩ [] where
  loose := rfl
  sub := fun _ h => h
  cover := fun _ h => by cases h
  hid := fun _ h => by cases h
  madeF := fun _ _ _ _ => rfl
  true := fun _ h => by cases h
  inj := fun _ h => by cases h
  nodup := List.nodup_nil
  live := fun _ h => by cases h
  chain := fun _ h => by cases h

/-- Under the hypotheses of its statement, the real and the reduction's interpretation of a mixed
program are close (`Spec.mixClose`). -/
theorem mixClose : Spec.mixClose := by
  intro S lam C α c nT nR hB hF E
  have e0 : Pr (real C c) (fun _ => E) = Pr (real' C c) (fun _ => E) := by
    unfold Pr PrCoins
    simp only [runEager_real']
  rw [e0, Pr_eq_law, Pr_eq_law]
  unfold OComp.law
  rw [pr_map, pr_map]
  have h1 := mainLe S lam C α c nT nR 0 (Table.empty _) (Table.empty S) ⟨[], []⟩ ⟨[], []⟩ []
    hB rel_empty (ghost_empty C) (le_refl _) E
  have h2 : Psi C c (Table.empty S) ⟨[], []⟩ [] ≤ _ :=
    psiLe S lam C α c nT nR (Table.empty S) ⟨[], []⟩ [] hB hF List.nodup_nil (fun _ h => by cases h)
  refine le_trans h1 (add_le_add (add_le_add le_rfl (le_of_eq ?_)) (le_trans h2 (le_of_eq ?_)))
  · unfold bnd collP wSt
    rw [Nat.zero_add, div_eq_mul_inv]
  · unfold hitP
    rw [List.length_nil, Nat.zero_add, Nat.mul_comm, div_eq_mul_inv]

end Rom
