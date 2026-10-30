-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/ProxRecord.lean: at the typed full-size sizes of the setting "record with work",
every round of a proof's shared chain from place 7 on is covered by numbers made of the proof
library's counts and of its bound on the MAIN code's list.

The nine typed stages of the two proximity tests of a shared chain (`sharedFolded`, `sharedOmega`,
Johnson/Prices/Dear.lean) pass `stageTest` (Johnson/Prices/Prox.lean), and no bound of the 60 typed
rounds `sharedTail` is marked bad. So by `iopp_covered` each number of `sharedTailCounts` is at most
the error of its round (`sharedTail_covered`): 0 for SPLIT, in which the verifier says nothing; then
the numbers of the two tests (`ioppCounts`). For every x under `AtRecord`, every list of codes and
every plan P that `sharedPlan recordSet codes x` returns, the numbers, and 0 for SEAL, are at most
the errors of the rounds of P from place 7 on, one by one (`shared_tail_covered`). At four of the
nine stages the mask code gives the distance (said here without a theorem): there these numbers
are too small to serve (the head of Johnson/Prices/Pair.lean); the like with the list of the code
that gives the distance is not in this file.

By `decide +kernel`, that is, evaluated by Lean's kernel at the written numbers, and turning with
them: `shared_stages_test`, `sharedTail_good`.

Main definition: `sharedTailCounts`.
Main theorems: `shared_stages_test`, `sharedTail_good`, `sharedTail_covered`, `shared_tail_covered`.
What is not claimed: what the heads of Johnson/Prices/Prox.lean and Johnson/Prices/Dear.lean do not
claim: above all that the numbers bound a prover's chance in these rounds, and that some x has a
plan.

-/
import Johnson.Prices.Prox
import Johnson.Prices.Dear
import OnBytes.Params.RecordRound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices

/-- The nine typed stages pass the test. By evaluation in Lean's kernel. -/
theorem shared_stages_test :
    ((sharedFolded ++ sharedOmega).all fun x => stageTest recordSet x.g) = true := by
  decide +kernel

/-- No bound of the 60 typed rounds is marked bad. By evaluation in Lean's kernel. -/
theorem sharedTail_good :
    (sharedTail.all fun y => !(y.bound recordSet .shared).bad) = true := by
  decide +kernel

/-- The numbers of the 60 typed rounds. -/
noncomputable def sharedTailCounts : List ℝ :=
  0 :: (ioppCounts recordSet .shared sharedFolded (1 + 64 + 1 + 2 * recordSet.samples) ++
    ioppCounts recordSet .shared sharedOmega (1 + 2 * recordSet.samples))

/-- **Each of the 60 typed rounds is covered.** -/
theorem sharedTail_covered :
    List.Forall₂ (CoveredBy recordSet .shared) sharedTailCounts sharedTail := by
  have ht := List.all_eq_true.mp shared_stages_test
  have hg : ∀ y ∈ sharedTail, (y.bound recordSet .shared).bad = false := fun y hy => by
    simpa using List.all_eq_true.mp sharedTail_good y hy
  unfold sharedTailCounts
  unfold sharedTail at hg ⊢
  refine List.Forall₂.cons ?_ (forall₂_app
    (iopp_covered (plainScope_shared _) rr_set.2 _ _ _ _
      (fun x hx => ht x (List.mem_append_left _ hx))
      fun y hy => hg y (List.mem_cons_of_mem _ (List.mem_append_left _ hy)))
    (iopp_covered (plainScope_shared _) rr_set.2 _ _ _ _
      (fun x hx => ht x (List.mem_append_right _ hx))
      fun y hy => hg y (List.mem_cons_of_mem _ (List.mem_append_right _ hy))))
  unfold CoveredBy
  exact_mod_cast Binary.val_nonneg _

/-- **The rounds of every shared plan at the typed sizes, from place 7 on, are covered.** -/
theorem shared_tail_covered {codes : Codes} {x : LinSized} {P : Planned} (hx : AtRecord x)
    (h : sharedPlan recordSet codes x = .ok P) :
    List.Forall₂ (fun (cnt : ℝ) (r : PlanRound) => cnt ≤ ((r.error.val : ℚ) : ℝ))
      (sharedTailCounts ++ [0]) (P.rounds.drop 7) := by
  rw [(shared_rounds_at hx h).1, List.map_append]
  refine forall₂_app ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · rw [List.forall₂_map_right_iff]
    exact sharedTail_covered
  · exact_mod_cast Binary.val_nonneg _

end OnBytes.Params.Prices
