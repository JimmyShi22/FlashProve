-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12MemberWritten
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Desc.Ok.NumberPrices.PlansAtWritten
import OnBytes.Model.ReadBackMade
/-
Johnson/Loose/H2K12/K12MemberFront.lean: CONDITIONAL: THE PROXIMITY TEST's (the kind K12's) ROW
AMONG THE ROWS THAT "the proof file's IOP as written in Lean returns, with its cut" WANTS OF EACH
LOT: THE KIND's FOUR WRITTEN MEMBERS, WHERE THE FRONT OF THE IOP's MAKER HAS RETURNED Z, FROM FOUR
EQUATIONS BY FIELD. A joining: no evaluation in Lean's kernel stands in this file.
THE FIVE PREMISES, BY NAME: hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z (the front's return; general
in the hash o); hs, hz, hp: of what the planner configured, Z.p.chains.made: the setting is
recordSet, the proof file's sizes are proofSizedFull, the three lists are proofThree's; hc: what is
sent, Z.made.proof, is proofSendsFull. (Z.p is Z.made.p by definition:
Johnson/Desc/ProofFile/Pub.lean.)
  plans_priced_front from hZ and hp: the three lists of rounds as read back are proofThree's
                   (ProofPlansPriced, Johnson/G/PlansPriced.lean): members_written's hg. By
                   ProofFile.Law.pub_configure (Johnson/Desc/ProofFile/Law/PlainMade.lean),
                   proof_read_made (OnBytes/Model/ReadBackMade.lean) and proof_fit0, proof_fit1,
                   proof_fit2 (Johnson/Desc/Ok/NumberPrices/PlansAtWritten.lean). Its first clause,
                   by the same road, is H2K5.Row.first_plan_made
                   (Johnson/Desc/First/Att/Row/K5FrontPlans.lean)
  members_written_front from the five: members_written's four conjuncts
                   (H2K12/K12MemberWritten.lean) at Z.made
  places_return_front from the five: there is N with H2U.placesOfMade Z.made = .ok N
FIVE PREMISES FOR SIX IS FEWER LETTERS, NOT LESS DEBT ON ONE POINT. members_written's hD (declPOf
Z.made = .ok D) is no premise here: pub_configure draws it from hZ. It is not thereby paid: the
front RUNS declPOf (ProofFile.pubBy), and in it treesSent's own check over all rounds of the first chain:
whoever shows hZ at given public files by Lean's kernel meets that check inside it. What is truly
gained: hg falls to hp: one equation by field less.
WHAT IT IS NOT: none of the five is shown of any public files by Lean's kernel. It spends no
opening, no "in scope" test and no row of the entry tests. The full size alone. No soundness
statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params Johnson.G.OfPlan H2U
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree proof_fit0 proof_fit1 proof_fit2)
open Johnson.G (proofSendsFull)
open H2K.Member (piLFull piUFull piOFull piWFull)

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}

/-- **members_written's hg, off the front's return and hp.** -/
theorem plans_priced_front (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hp : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]) :
    ProofPlansPriced Z.made proofThree.A.plan proofThree.B.plan proofThree.C.plan := by
  obtain ⟨ls, _, hc, hk, _⟩ := ProofFile.Law.pub_configure hZ
  refine proof_read_made hc hk (fun P hP => ?_) hp
  rw [hp] at hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl
  · exact proof_fit0
  · exact proof_fit1
  · exact proof_fit2

/-- **WHERE THE FRONT HAS RETURNED, FROM FOUR EQUATIONS BY FIELD: THE FOUR WRITTEN MEMBERS.** -/
theorem members_written_front (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hs : Z.p.chains.made.sized.set = recordSet)
    (hz : Z.p.chains.made.sized.proof = proofSizedFull)
    (hp : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (hc : Z.made.proof = proofSendsFull) :
    p12OfMade Z.made = piLFull ∧
      p12FoldedOfMade Z.made 9 = ({ piUFull with place := ⟨2, none, 9, .K12⟩ } : P12) ∧
      p12OmegaOfMade Z.made 10 = ({ piOFull with place := ⟨2, none, 10, .K12⟩ } : P12) ∧
      p12OwnOfMade Z.made 2 = ({ piWFull with place := ⟨3, none, 2, .K12⟩ } : P12) := by
  obtain ⟨_, _, _, _, hD⟩ := ProofFile.Law.pub_configure hZ
  exact members_written Z.made hs hz hp (plans_priced_front hZ hp) hc Z.D hD

theorem places_return_front (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hs : Z.p.chains.made.sized.set = recordSet)
    (hz : Z.p.chains.made.sized.proof = proofSizedFull)
    (hp : Z.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (hc : Z.made.proof = proofSendsFull) : ∃ N, placesOfMade Z.made = .ok N := by
  obtain ⟨_, _, _, _, hD⟩ := ProofFile.Law.pub_configure hZ
  exact places_return Z.made hs hz hp (plans_priced_front hZ hp) hc Z.D hD

end

end H2K12

#print axioms H2K12.plans_priced_front
#print axioms H2K12.members_written_front
#print axioms H2K12.places_return_front
