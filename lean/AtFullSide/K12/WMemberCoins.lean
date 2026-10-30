-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/WMemberCoins.lean: at the written book, at the coins that the row hands the last chain's
test: the two K1 members' stretches are the senders' own coins.

  member_coins_at_W   members_held at the second part of the pair, at restCoins
  held_cut_W, held_cut_I   at a job at the written plan and ride: its cut, reading what the stretch reads

Limits.
- hB is a premise: book_laid has it at onlineProverFromPublicFiles's return.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.HeldAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.MakerBook
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K1 (parGF parWF)
open Johnson.Prover.Send (shapeAt)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (rawBookRows_written rawWhole_is_raw)

variable {V W X : Type}

/-- **At the coins that the row hands the test the two K1 members' stretches are the senders' own.** -/
theorem member_coins_at_W {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (J : TestJob W X) (hp : J.p.place = placeW)
    (k : Coins B) (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (hl : lendRow B (B.rowsOf 2) (k.look 2) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c) :
    (∀ {c₀ : Cs (K1.dueR parGF rideGF)},
      (k.look 0 senderI).2.cut ⟨0, 0⟩ (K1.dueR parGF rideGF) = some c₀ →
      (∀ i, i < (K1.dueMsg parGF.codes (shapeAt parGF (parGF.sent.size - 1))
          (rideGF (parGF.sent.size - 1))).f →
        K1.cf c₀ ((K1.startR parGF rideGF (parGF.sent.size - 1)).f + i) =
          ((restCoins J c.2.1).mem 0).f i) ∧
      ∀ i, i < (K1.dueMsg parGF.codes (shapeAt parGF (parGF.sent.size - 1))
          (rideGF (parGF.sent.size - 1))).e →
        K1.ce c₀ ((K1.startR parGF rideGF (parGF.sent.size - 1)).e + i) =
          ((restCoins J c.2.1).mem 0).e i) ∧
    (∀ {c₀ : Cs (K1.dueR parWF rideWF)},
      (k.look 0 senderW).2.cut ⟨0, 0⟩ (K1.dueR parWF rideWF) = some c₀ →
      (∀ i, i < (K1.dueMsg parWF.codes (shapeAt parWF 0) (rideWF 0)).f →
        K1.cf c₀ ((K1.startR parWF rideWF 0).f + i) = ((restCoins J c.2.1).mem 1).f i) ∧
      ∀ i, i < (K1.dueMsg parWF.codes (shapeAt parWF 0) (rideWF 0)).e →
        K1.ce c₀ ((K1.startR parWF rideWF 0).e + i) = ((restCoins J c.2.1).mem 1).e i) := by
  obtain ⟨-, hl'⟩ := lendRow_cons_ok hl
  obtain ⟨l1, -⟩ := lendRow_cons_ok hl'
  rw [hp] at l1
  exact members_held hB (by decide : 1 ∈ [0, 1]) k l1

/-- **A job at W's written plan and ride: its cut is there, and reads what the stretch reads.** hS:
member_coins_at_W's second clause at St. -/
theorem held_cut_W {Wj Xj : Type} {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (J : K1.SendJob Wj Xj) (hP : J.P = parWF)
    (hr : J.ride = rideWF) (k : Coins B) (St : ProofFile.Honest.K12.Stretch)
    (hS : ∀ {c₀ : Cs (K1.dueR parWF rideWF)},
      (k.look 0 senderW).2.cut ⟨0, 0⟩ (K1.dueR parWF rideWF) = some c₀ →
      (∀ i, i < (K1.dueMsg parWF.codes (shapeAt parWF 0) (rideWF 0)).f →
        K1.cf c₀ ((K1.startR parWF rideWF 0).f + i) = St.f i) ∧
      ∀ i, i < (K1.dueMsg parWF.codes (shapeAt parWF 0) (rideWF 0)).e →
        K1.ce c₀ ((K1.startR parWF rideWF 0).e + i) = St.e i) :
    ∃ c, K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c ∧
      (∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P 0) (J.ride 0)).f →
        K1.cf c ((K1.startR J.P J.ride 0).f + i) = St.f i) ∧
      ∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P 0) (J.ride 0)).e →
        K1.ce c ((K1.startR J.P J.ride 0).e + i) = St.e i := by
  obtain ⟨P, first, ride, data⟩ := J
  obtain rfl : P = parWF := hP
  obtain rfl : ride = rideWF := hr
  obtain ⟨-, dW, -⟩ := written_W
  obtain ⟨r1, -, -⟩ := rawBookRows_written _ B (rawWhole_is_raw hB)
  have cov : K1.bookCovers B 0 senderW (K1.dueR parWF rideWF) = true := by
    unfold K1.bookCovers
    show decide (_ ≤ (dueAt B.first _).f ∧ _ ≤ (dueAt B.first _).e) = true
    rw [r1, dW]
    exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
  have is := ProofFile.Honest.K1.lentCut_isSome k 0 (by decide) senderW (K1.dueR parWF rideWF)
  rw [cov] at is
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 is
  exact ⟨c, hc, hS hc⟩

/-- **The same at the first sender's written plan and ride, at its last message.** -/
theorem held_cut_I {Wj Xj : Type} {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (J : K1.SendJob Wj Xj) (hP : J.P = parGF)
    (hr : J.ride = rideGF) (k : Coins B) (St : ProofFile.Honest.K12.Stretch)
    (hS : ∀ {c₀ : Cs (K1.dueR parGF rideGF)},
      (k.look 0 senderI).2.cut ⟨0, 0⟩ (K1.dueR parGF rideGF) = some c₀ →
      (∀ i, i < (K1.dueMsg parGF.codes (shapeAt parGF (parGF.sent.size - 1))
          (rideGF (parGF.sent.size - 1))).f →
        K1.cf c₀ ((K1.startR parGF rideGF (parGF.sent.size - 1)).f + i) = St.f i) ∧
      ∀ i, i < (K1.dueMsg parGF.codes (shapeAt parGF (parGF.sent.size - 1))
          (rideGF (parGF.sent.size - 1))).e →
        K1.ce c₀ ((K1.startR parGF rideGF (parGF.sent.size - 1)).e + i) = St.e i) :
    ∃ c, K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c ∧
      (∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P (J.P.sent.size - 1))
          (J.ride (J.P.sent.size - 1))).f →
        K1.cf c ((K1.startR J.P J.ride (J.P.sent.size - 1)).f + i) = St.f i) ∧
      ∀ i, i < (K1.dueMsg J.P.codes (shapeAt J.P (J.P.sent.size - 1))
          (J.ride (J.P.sent.size - 1))).e →
        K1.ce c ((K1.startR J.P J.ride (J.P.sent.size - 1)).e + i) = St.e i := by
  obtain ⟨P, first, ride, data⟩ := J
  obtain rfl : P = parGF := hP
  obtain rfl : ride = rideGF := hr
  obtain ⟨dI, -⟩ := written_W
  obtain ⟨r1, -, -⟩ := rawBookRows_written _ B (rawWhole_is_raw hB)
  have cov : K1.bookCovers B 0 senderI (K1.dueR parGF rideGF) = true := by
    unfold K1.bookCovers
    show decide (_ ≤ (dueAt B.first _).f ∧ _ ≤ (dueAt B.first _).e) = true
    rw [r1, dI]
    exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
  have is := ProofFile.Honest.K1.lentCut_isSome k 0 (by decide) senderI (K1.dueR parGF rideGF)
  rw [cov] at is
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 is
  exact ⟨c, hc, hS hc⟩

end AtFullSide.K12

#print axioms AtFullSide.K12.held_cut_W
#print axioms AtFullSide.K12.held_cut_I
#print axioms AtFullSide.K12.member_coins_at_W
