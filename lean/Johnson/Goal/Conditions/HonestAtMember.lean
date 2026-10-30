-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HonestAtMember.lean: **HonestWithin (Ladder.lean) AT THE MEMBER member A gen
(Johnson/Goal/Conditions/HomeAtWider.lean), in scope, where protocolDataWellFormed says yes**: the member of
theWider of which completeness is said. A call of honestWithin_wider_live, queryBound_drawn and
queryBound_home (Johnson/Goal/Conditions/HonestAtHome.lean): it adds no strength. A theorem about
the goals' own definition at a member. This file states no goal.

Main names.
  CountArgs A Z   a premise's record on the arguments A at the files Z: four of A's fields ARE
    written values: carry is the first-block exit at the test passHome; the three caps are 2^(work +
    6) tries at the three files' rounds; and each path of each draw has its request tree's depth.
  queryBound_pfOf   the prover's program pfOf A asks the hash function at most 8 + 7068035999651
    times, on every path, at all weights, randomness, requests and numbers drawn.
  honestWithin_member   THE STATEMENT.

Limits. That protocolDataWellFormed accepts is proved in Lean, in the side library (outside the main library and
with that library's own limits), at the written copy of the full-size example's files under every
acceptance policy in scope (theLive_zAt, AtFullSide/Top/LiveAtPolicies.lean; owner:
Johnson/Goal/Conditions/HomeLast.lean, limit 4); that theorem is not called here. The scope is wider
than these files; elsewhere in it that protocolDataWellFormed accepts stays a premise. CountArgs IS A PREMISE: it
fixes four fields of A and one clause on its draws (a clause of Coins.Fit, which completeness'
DrawFit asks too); the strategies, the printer, the instance, the randomness and the other fields
stay letters. That completeness' premises can be met at the same A is not shown here. THE CAPS ARE
OF OUR CHOOSING. NO COMPLETENESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HonestAtHome
import Johnson.Goal.Conditions.HomeAtWider

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles Rom
open OnBytes.Prover (carryF proveForm)

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable {b : PublicFiles → ℕ} {Rand : Type} {B N : ℕ} (A : HomeArgs b Rand B N)

/-- What the count asks of the arguments at the files Z. -/
structure CountArgs (Z : PublicFiles) : Prop where
  carry : A.carry Z = fun d => carryF (homeT b Z) (fun _ => passHome b Z) d
  capT : A.capT Z = FlashProve.capT (sAt Z)
  capL : A.capL Z = FlashProve.capL
  capB : A.capB Z = FlashProve.capB (sAt Z)
  paths : ∀ d ρ a, (A.drawOf Z d ρ a).coT.path.length = (homeR b Z).queryLayout.depthReqT ∧
    (A.drawOf Z d ρ a).coL.path.length = (homeR b Z).queryLayout.depthReqL ∧
    (A.drawOf Z d ρ a).coB.path.length = (homeR b Z).queryLayout.depthReq

/-- **The prover's program at the member.** -/
theorem queryBound_pfOf (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (H : CountArgs A Z) (s : IntegerTransformer.Settings) (w : ModelWeights s) (ρ : Rand)
    (p o : List Token) (a : Fin (N + 1)) :
    (pfOf A Z s w ρ p o a).QueryBound (8 + 7068035999651) := by
  unfold pfOf
  rw [H.carry, H.capT, H.capL, H.capB]
  exact queryBound_home b Z scope live (fillB b Z) (A.st Z) _ (A.xOf Z p o)
    (fun d => A.drawOf Z d ρ a) (A.print Z s w ρ p o a) fun d => H.paths d ρ a

variable (gen : (Z : PublicFiles) → Rand → Digest → Digest → Fin (b Z + 1))

/-- **HonestWithin at the member, in scope, where protocolDataWellFormed says yes.** -/
theorem honestWithin_member (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (H : CountArgs A Z) :
    HonestWithin (atSecondHashFunction (member A gen)) Z (settingsOfRead pp) :=
  honestWithin_wider_live (homeK A) ⟨b, gen⟩ _ Z pp hr scope live (fun _ => trivial)
    fun w ρ p t => by
      rw [prove_homeK]
      exact queryBound_drawn _ _ fun a => queryBound_pfOf A Z scope live H _ w ρ p t a

end FlashProve

#print axioms FlashProve.queryBound_pfOf
#print axioms FlashProve.honestWithin_member
