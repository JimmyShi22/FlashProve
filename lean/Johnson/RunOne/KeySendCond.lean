-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendCond.lean: THEOREMS. **Two premises of send_goodIn, AT THE KEY FILE's DESCRIPTION's OWN LETTERS**, for whoever calls that law itself at the three sendings of Key.descriptionFromSource X N P's first chain
(and not send_seat, KeySendSeat.lean).
OBJECT. K1's numbers as Key.firstChain lays them (parIdx X · parMsg X · parW X msg: KeySendAtDesc.lean) and the blocks that stand in (Key.descriptionFromSource X N P).first.blocksInOrder at 0 | 1 | W's place.
USER. Other files' rows at these three places. LETTERS. rad.
  cond_idx | cond_msg | cond_w     the law's one Boolean condPort … rad = true, FROM THE RUN's YES AND meetsB at every sampled message (the one clause of the three that no theorem gives)
  rounds_idx | rounds_msg | rounds_w   the laid block's rounds ARE K1.rounds of these numbers
  first_round · seed_kind          K1.rounds Q begins with the round at seedEntry Q; that entry's name has the kind .seeds
What is not claimed. meetsB. That a frame's data are these rounds. Nothing on soundness.

-/
import Johnson.RunOne.KeySendAtDesc

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params Johnson.Pack
open Johnson.RunOne.KeyKeeps Johnson.RunOne.KeyPay
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K1 (Par condPort shapeAt sampledAt seedEntry)
open VerifiableInference.Desc.Key

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {x : Xi} {v₁ v₂ v₃ : Fmt.View}

theorem cond_idx (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) (rad : Nat → Nat)
    (hm : ∀ k, sampledAt (parIdx X) k → meetsB (parIdx X).codes (shapeAt (parIdx X) k) (rad k.val) = true) : condPort (parIdx X) rad = true := by
  obtain ⟨hl, hp⟩ := send_plan_of_yes hy
  exact cond_of _ rad (pays_bare _ st₁ _ (idx_pays _ _ _) (hp _ (List.mem_of_getElem? (idx_at X N P)))).plan (hl _ _ _ _) hm

theorem cond_msg (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) (rad : Nat → Nat)
    (hm : ∀ k, sampledAt (parMsg X) k → meetsB (parMsg X).codes (shapeAt (parMsg X) k) (rad k.val) = true) : condPort (parMsg X) rad = true := by
  obtain ⟨hl, hp⟩ := send_plan_of_yes hy
  exact cond_of _ rad (pays_bare _ st₁ _ (msg_pays _ _ _) (hp _ (List.mem_of_getElem? (msg_at X N P)))).plan (hl _ _ _ _) hm

theorem cond_w (hy : (descriptionFromSource X N P).run x v₁ v₂ v₃ = true) {bw : Block FirstState Claim}
    (hb : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw) (rad : Nat → Nat)
    (hm : ∀ msg, linMessageW X.Y.k.oneTime.lin = some msg → ∀ k, sampledAt (parW X msg) k → meetsB (parW X msg).codes (shapeAt (parW X msg) k) (rad k.val) = true) :
    ∃ msg, linMessageW X.Y.k.oneTime.lin = some msg ∧ condPort (parW X msg) rad = true := by
  obtain ⟨hl, hp⟩ := send_plan_of_yes hy
  have hpl : (bareOf bw).planOk = true := hp _ (List.mem_of_getElem? (w_at X N P hb))
  obtain ⟨msg, hmsg, hP⟩ := w_pays hb (Bool.and_eq_true_iff.1 (show (bw.planOk && bw.hasNoClaimsAndNothingAfter) = true from hpl)).1
  exact ⟨msg, hmsg, cond_of _ rad hP.plan (hl _ _ _ _) (hm msg hmsg)⟩

theorem rounds_idx (X : Source) : (bareOf (sendIndexMasks (β := LookupRecord) (Cl := Claim) X.Y.k.oneTime pieces (gIdx X))).rounds = VerifiableInference.Desc.K1.rounds (parIdx X) :=
  idx_rounds _ _ _

theorem rounds_msg (X : Source) : (bareOf (sendOwnMessage (β := LookupRecord) (Cl := Claim) X.Y.k.oneTime pieces (gMsg X))).rounds = VerifiableInference.Desc.K1.rounds (parMsg X) :=
  msg_rounds _ _ _

theorem rounds_w {bw : Block FirstState Claim} {msg : Array OracleNotice} (hm : linMessageW X.Y.k.oneTime.lin = some msg)
    (hb : sendW X.Y.k.oneTime pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (gW X) = some bw) : (bareOf bw).rounds = VerifiableInference.Desc.K1.rounds (parW X msg) :=
  (show (bareOf bw).rounds = bw.rounds from rfl).trans (w_rounds hm hb)

theorem first_round (Q : Par) : (VerifiableInference.Desc.K1.rounds Q)[0]? = some { entry := seedEntry Q } := rfl

theorem seed_kind (Q : Par) : Fmt.kindOf (seedEntry Q).name = some .seeds := kind_seed

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.cond_idx
#print axioms Johnson.RunOne.KeySendGood.cond_msg
#print axioms Johnson.RunOne.KeySendGood.cond_w
#print axioms Johnson.RunOne.KeySendGood.rounds_idx
#print axioms Johnson.RunOne.KeySendGood.rounds_msg
#print axioms Johnson.RunOne.KeySendGood.rounds_w
#print axioms Johnson.RunOne.KeySendGood.first_round
#print axioms Johnson.RunOne.KeySendGood.seed_kind
