-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/M1/LotsThin.lean: the rule's door on the book at K1's senders on the first chain, with the
opening's clause taken from clear_written.

  okFast_of_clear    BookClearAny gives the form that the door asks
                     (at the owner's spenders: ownerSp)
  door_of_clear      the door, from that clause at the written entries

Limits. hClear is a premise here: the book is clear at the opening, at the written entries and order.
LotsThinClosed.lean states the door with it discharged by clear_written. Scope, the gate and the return are the caller's. How far the door
speaks: the head of LotsDoor.lean.
-/
import AtFullSide.M1.LotsAtReturn
import AtFullSide.M1.LotsW
import AtFullSide.M1.LotsOwnersWritten
import Johnson.SendSim.At.GuardTestTie

set_option autoImplicit false

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes.SendSim.At OnBytes.SendSim.Seat
open P2Law.ProofPlan (WP)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K1 (qFull firstPar)
open VerifiableInference.Desc.K13.Law (gpFull)

/-- **BookClearAny gives okFast.** -/
theorem okFast_of_clear {P : VerifiableInference.Desc.K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts}
    {ord : List Place} {o : Addr} (h : BookClearAny P ride Bk ord o) :
    okFast P ride Bk ord o = true := by
  have h1 := (ownerOkB_iff (P := P) (ride := ride)).2 h
  unfold ownerOkB ownerFitsB at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨hw, hf⟩, hg⟩ := h1
  have hm : ∀ p ∈ ownerSp Bk o, p ∈ Bk.ahead.map (·.spender) ∧ (Bk.spentBy o p).isEmpty = false := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
    have he' := (List.mem_filter.1 he).1
    have hs : e ∈ Bk.spentBy o e.spender := by
      rw [spentBy_eq]
      exact List.mem_filter.2 ⟨he, by simp⟩
    refine ⟨List.mem_map.2 ⟨e, he', rfl⟩, ?_⟩
    cases hh : (Bk.spentBy o e.spender) with
    | nil => rw [hh] at hs; cases hs
    | cons _ _ => rfl
  unfold okFast
  simp only [Bool.and_eq_true]
  refine ⟨⟨hw, List.all_eq_true.2 fun p hp => List.all_eq_true.1 hf p (hm p hp).1⟩,
    List.all_eq_true.2 fun p hp => ?_⟩
  have h2 := List.all_eq_true.1 hg p (hm p hp).1
  rw [(hm p hp).2, Bool.false_or] at h2
  exact h2

variable {W₀ Rc Tr X₀ X' : Type} {P : VerifierAndGoals.PublicFiles} {Fl : OnlineProverParts W₀ Rc Tr X₀ X'}
  {R : OnlineProverWithDescription W₀ Rc Tr X₀ X'}

/-- **The door, from the clause at the opening.** -/
theorem door_of_clear
    (hClear : BookClearAny (firstPar qFull gpFull) (rideOf (firstFold qFull)) aheadBook (orderOf WP)
      oOpen)
    (hS : VerifierAndGoals.InScope P = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R) :
    ∀ e ∈ R.B.ahead, e.once = true → lotsMine R.Z R.G e.owner = true →
      lotsOkB R.Z R.G R.B (orderOf R.F) e.owner = true :=
  door_at_return hS hL h (okFast_of_clear hClear) ok_w owners_written

end AtFullSide.M1

#print axioms AtFullSide.M1.door_of_clear
