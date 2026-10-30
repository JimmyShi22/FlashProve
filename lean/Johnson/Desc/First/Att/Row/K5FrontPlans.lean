-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontPlans.lean: THE FIRST CHAIN's PLAN IN THE PUBLIC PART IS THE
WRITTEN ONE, OFF THE FRONT OF THE PROOF FILE's IOP's MAKER ALONE, BY FIELD: from the public part's
return, ONE EQUATION ON WHAT THE PLANNER CONFIGURED (its three lists for the proof file are the
three
written ones), and one closed equation between two written lists, which is a premise here. A join of
laws that lie; nothing is evaluated.

  `first_plan_made`: `Z.first.given.plan = proofThree.A.plan.plan`: the chains are read back from
    what the planner configured (`ProofFile.Law.pub_configure`,
    Johnson/Desc/ProofFile/Law/PlainMade.lean); a plan as read back is the plan as made, where it
    fits the format's words (`proof_read_made`, OnBytes/Model/ReadBackMade.lean; `proof_fit0` | 1 |
    2, Johnson/Desc/Ok/NumberPrices/PlansAtWritten.lean).
  **`plans_made_of`**: so `Z.plans.1 = P5T.esFull.1`, where
    E0 : `proofThree.A.plan.plan.rounds = dryProofFull.1.map (·.1.entry)`.
  `plans_front_of`: a corollary, in scope, under the accept of the door's row 9 (`madePinnedAt`; by
    `proof_plans_in_scope`, Johnson/Goal/Numbers/MadeInScope.lean). NOT FOR WHOEVER IS TO SHOW ROW
    9
    ITSELF: for that reader it would be a circle.
THE FIRST TWO HAVE NO PIN AND NO SCOPE AMONG THEIR PREMISES, AND NONE STANDS UNDER THE HEAD. Who
shows
the equation on the three lists at the goals' stored files: whoever shows that the planner's three
makers of these lists return the written ones; not said here.
Limits. The full size alone. A return and an equation by field are premises. Nothing on soundness.
On
hiding nothing.

-/
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.Ok.NumberPrices.PlansAtWritten
import Johnson.P5T.PlanSeatsFull
import OnBytes.Model.ReadBackMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.PlanWritten.Joined (proof_plans_in_scope)
open VerifiableInference.Number.ByRuns (proofThree proof_fit0 proof_fit1 proof_fit2)
open Johnson.G (dryProofFull)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : ProofFile.Pub}

/-- The first chain's plan as read back is the first written plan: BY FIELD: no pin, no scope. -/
theorem first_plan_made {pol lay KL : ByteArray} (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    Z.first.given.plan = proofThree.A.plan.plan := by
  obtain ⟨ls, _, hc, hk, _⟩ := ProofFile.Law.pub_configure h
  refine (proof_read_made hc hk (fun P hP => ?_) hm).1
  rw [hm] at hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · exact proof_fit0
  · exact proof_fit1
  · exact proof_fit2

/-- **THE PLAN's FIRST LIST IS THE WRITTEN ONE, OFF THE FRONT ALONE, BY FIELD.** -/
theorem plans_made_of (E0 : proofThree.A.plan.plan.rounds = dryProofFull.1.map (·.1.entry))
    {pol lay KL : ByteArray} (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hm : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    Z.plans.1 = P5T.esFull.1 := by
  show Z.first.given.plan.rounds = dryProofFull.1.map (·.1.entry)
  rw [first_plan_made h hm, E0]

/-- The like under the pin of the door's row 9, in scope: a corollary. -/
theorem plans_front_of (E0 : proofThree.A.plan.plan.rounds = dryProofFull.1.map (·.1.entry))
    {W : VerifierAndGoals.PublicFiles} (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.plans.1 = P5T.esFull.1 :=
  plans_made_of E0 h (proof_plans_in_scope hW h hy)

end H2K5.Row

#print axioms H2K5.Row.first_plan_made
#print axioms H2K5.Row.plans_made_of
#print axioms H2K5.Row.plans_front_of
