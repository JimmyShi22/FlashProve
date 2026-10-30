-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/AtTheBorder.lean: THE OUTPUT HEAD's OWN ROUNDS (kind K6): the
six statements (P2) of Honest/K6/Term/Statements.lean, each under its own premises. Calls alone.

WHAT IT IS NOT. None of them says that a verifier accepts a proof. Each speaks only where the first
chain's invariant holds in front of member 341. AcceptedS is light at this sub-protocol: the yes is
of form alone. ExchangeS, the weight, stands under the twelve fields of K6HeadBelow, of which no
value is shown here. All limits in the head of Statements.lean hold.

  playsAndIsAcceptedAtTheBorder   by k6_playsS_at_head, k6_acceptedS_at_head (K6/Law/SeatedAtHead)
  ridesPastAtTheBorder            by k6_ridesPastS_head (K6/Law/RidesPastAll)
  formHoldsBehindTheBorder        by k6_behindS_stepped (K6/Law/BehindStepped)
  deliversAtTheBorder             by k6_exchangeS_of_below (K6/Law/ScriptBelowFree)
  fourAtTheHeadsRiders            by the first three, csHead_none_across_341 and csHead_begins_342
                                  (Honest/Thread/CsHeadAcross.lean)
  allFiveAtTheHeadsRiders         by that and deliversAtTheBorder
-/
import Johnson.Desc.ProofFile.Honest.K6.Term.Statements
import Johnson.Desc.ProofFile.Honest.K6.Law.SeatedAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.BehindStepped
import Johnson.Desc.ProofFile.Honest.K6.Law.RidesPastAll
import Johnson.Desc.ProofFile.Honest.Thread.CsHeadAcross

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (k6_exchangeS_of_below)

/-- **(P2) It plays, and its step says yes.** -/
theorem playsAndIsAcceptedAtTheBorder : PlaysAndIsAcceptedAtTheBorder := by
  intro W₀ Rc Z D r Zp Np cF x h weights G Ky X₀ H seat Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said
  exact ⟨k6_playsS_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ seat Said,
    fun fall => k6_acceptedS_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ seat Said fall⟩

/-- **(P2) What stays open past the member stays true.** -/
theorem ridesPastAtTheBorder : RidesPastAtTheBorder := by
  intro W₀ Rc Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said keepsGives
  exact k6_ridesPastS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said keepsGives

/-- **(P2) Behind the member's accepting step the form and the riders hold, and the step kept what
"keeps" names.** -/
theorem formHoldsBehindTheBorder : FormHoldsBehindTheBorder := by
  intro W₀ Rc Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd riders keepsByKind w
    Said fit
  exact k6_behindS_stepped h H Q test carryX item n₁ n₂ b₀ Vd w keepsByKind Said riders
    fit.keepsIsGiven fit.replyNotBehind fit.ridersStay fit.ridersBegin

/-- **(P2), the weight: what the member owes is delivered**, under the seat and K6HeadBelow. -/
theorem deliversAtTheBorder : DeliversAtTheBorder := by
  intro W₀ Rc Z D r Zp Np cF x h weights G Ky X₀ H seat Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    Said o d rowOf own base cnt free below
  exact k6_exchangeS_of_below below seat

/-- **(P2) Four of the five at the frame's own riders.** -/
theorem fourAtTheHeadsRiders : FourAtTheHeadsRiders := by
  intro W₀ Rc Z D r Zp Np cF x h weights G Ky X₀ H seat Bk Q test carryX item n₁ n₂ Vd nextFree
    afterDigits callsReturned keepsByKind w Said keepsGives keepsIsGiven
  obtain ⟨plays, accepted⟩ := playsAndIsAcceptedAtTheBorder W₀ Rc Z D r Zp Np cF x h weights G Ky
    X₀ H seat Bk Q test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead nextFree afterDigits callsReturned)) (kpBy keepsByKind) w Said
  refine ⟨plays, ?_, ?_, accepted⟩
  · exact formHoldsBehindTheBorder W₀ Rc Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂
      339 Vd (csHead nextFree afterDigits callsReturned) keepsByKind w Said
      { keepsIsGiven := keepsIsGiven
        replyNotBehind := by omega
        ridersStay := fun c hc lo hi => absurd hi (csHead_none_across_341 hc lo)
        ridersBegin := fun c hc lo => .inl ⟨347, csHead_begins_342 hc lo⟩ }
  · exact ridesPastAtTheBorder W₀ Rc Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ 339
      Vd (ridersOf (csHead nextFree afterDigits callsReturned)) (kpBy keepsByKind) w Said
      fun s s' k => keepsGives s s' k

/-- **(P2) All five at the frame's own riders, as one value of the frame's structure.** -/
theorem allFiveAtTheHeadsRiders : AllFiveAtTheHeadsRiders := by
  intro W₀ Rc Z D r Zp Np cF x h weights G Ky X₀ H seat Bk Q test carryX item n₁ n₂ Vd nextFree
    afterDigits callsReturned keepsByKind w Said o d rowOf own base cnt free keepsGives
    keepsIsGiven below fall
  obtain ⟨plays, behind, ridesPast, accepted⟩ := fourAtTheHeadsRiders W₀ Rc Z D r Zp Np cF x h
    weights G Ky X₀ H seat Bk Q test carryX item n₁ n₂ Vd nextFree afterDigits callsReturned
    keepsByKind w Said keepsGives keepsIsGiven
  exact
    { plays := plays
      behind := behind
      exchange := deliversAtTheBorder W₀ Rc Z D r Zp Np cF x h weights G Ky X₀ H seat Bk Q test
        carryX item n₁ n₂ 339 Vd (ridersOf (csHead nextFree afterDigits callsReturned))
        (kpBy keepsByKind) w Said o d rowOf own base cnt free below
      ridesPast := ridesPast
      accepted := accepted fall }

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.playsAndIsAcceptedAtTheBorder
#print axioms ProofFile.Honest.K6.Term.ridesPastAtTheBorder
#print axioms ProofFile.Honest.K6.Term.formHoldsBehindTheBorder
#print axioms ProofFile.Honest.K6.Term.deliversAtTheBorder
#print axioms ProofFile.Honest.K6.Term.fourAtTheHeadsRiders
#print axioms ProofFile.Honest.K6.Term.allFiveAtTheHeadsRiders
