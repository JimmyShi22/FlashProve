-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontE0.lean: THE TWO WRITTEN LISTS HAVE THE SAME ENTRIES, AND SO THE
FIRST CHAIN's PLAN IN THE PUBLIC PART IS THE WRITTEN ONE, OFF THE FRONT ALONE. Joins; nothing is
evaluated here.
  **`E0`**: `proofThree.A.plan.plan.rounds = dryProofFull.1.map (·.1.entry)`: from `same_written`
    (K5FrontSame.lean) by the walker's law, and `named_written` (K5FrontNamed.lean).
  **`plans_made`**: `Z.plans.1 = P5T.esFull.1` from the public part's return and one equation by
    field: the planner's three lists for the proof file are the written ones (`plans_made_of`,
    K5FrontPlans.lean, at `E0`). `plans_front`: the like under the pin of the door's row 9, in
    scope.
Limits. The full size alone. Both lists are WRITTEN values. Returns and a test's yes are premises.
Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5FrontSame
import Johnson.Desc.First.Att.Row.K5FrontNamed
import Johnson.Desc.First.Att.Row.K5FrontPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.G (dryProofFull)

theorem all_outOf {α : Type} (p : α → Bool) : ∀ l : List (Nat × α),
    (l.all fun x => p x.2) = true → ∀ a ∈ outOf l, p a = true
  | [], _, a, ha => absurd ha (List.not_mem_nil)
  | x :: xs, h, a, ha => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [outOf, List.mem_append] at ha
    rcases ha with ha | ha
    · rw [(List.mem_replicate.1 ha).2]
      exact h.1
    · exact all_outOf p xs h.2 a ha

/-- **THE TWO WRITTEN LISTS HAVE THE SAME ENTRIES.** -/
theorem E0 : proofThree.A.plan.plan.rounds = dryProofFull.1.map (·.1.entry) := by
  unfold Fmt.Plan.rounds
  rw [priced_is, sameRuns_sound _ _ _ same_written, dry_is]
  have hn : ∀ a ∈ outOf runsD, (a.name != Fmt.recordName) = true :=
    all_outOf (fun e : Fmt.Entry => e.name != Fmt.recordName) runsD named_written
  exact List.filter_eq_self.2 hn

/-- **THE PLAN's FIRST LIST IS THE WRITTEN ONE, OFF THE FRONT ALONE, BY FIELD.** -/
theorem plans_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    Z.plans.1 = P5T.esFull.1 :=
  plans_made_of E0 h hm

/-- The like under the pin of the door's row 9, in scope. -/
theorem plans_front {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.plans.1 = P5T.esFull.1 :=
  plans_front_of E0 hW h hy

end H2K5.Row

#print axioms H2K5.Row.all_outOf
#print axioms H2K5.Row.E0
#print axioms H2K5.Row.plans_made
#print axioms H2K5.Row.plans_front
