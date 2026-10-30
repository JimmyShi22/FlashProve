-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchMaskAt.lean: the closing of a segment (K10): two clauses of the field stand of
`FreshBySwitch` (Pay/XchFreshField.lean), under the head, at a reached state in front of the closing of a segment into which a code
switch leads: the fresh mask's message has the shape of the switch's last message, and the seat at which the laws on the first
chain's script speak of that message.

  **`mask_seat_at`**    the two clauses

By: the closed test `mask_seat_written` (Pay/XchMaskW.lean); `mask_no_reached`, `mask_message` (Pay/FoldAt.lean); `seat_at_reach` (Pay/SeatsAtStand.lean); `msgShape_at` and the written list
of messages as Pay/FoldAt.lean takes them.

Limits. The head is a premise; that the state is reached and has not failed is a premise. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchMaskW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (maskNo seatsPlanW)
open VerifiableInference.Desc.First.K2Hands (MList MW_eq)
open VerifiableInference.Desc.K12.Door (msgsOfChain msgShape_at)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.Sound (seatBy noFirst)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K2 (SwitchPlace switchSent switchSeatIn)
open ProofFile.Honest.K2.Law (placesW)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The fresh mask's message has the switch's last message's shape and seat.** -/
theorem mask_seat_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (h1 : 1 ≤ l) (hl : l < 25)
    {p : SwitchPlace} (hp : placesW.find? (·.link == l) = some p) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none) {mk : Nat}
    (hm : (K9.recOf s).frame.mask = some mk) :
    (∀ y, s.st.oracles[mk]? = some y →
      y.shape = ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape) ∧
      seatBy noFirst s.book mk = some (seatSw Zp p ((switchSent p.sizes p.others).size - 1)) := by
  obtain ⟨y₀, hy₀, -⟩ := mask_message h hl hr hf hm
  have hy₁ : s.st.oracles[mk]? = some y₀ := hy₀
  have hlt : mk < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hy₁).1
  obtain rfl : mk = maskNo seatsPlanW P5T.psFull l :=
    Option.some.inj (hm.symm.trans (mask_no_reached h.toAtMg hl hr))
  have ht := List.all_eq_true.1 mask_seat_written (l - 1) (List.mem_range.2 (by omega))
  have e : l - 1 + 1 = l := by omega
  rw [e] at ht
  unfold maskTest at ht
  rw [hp] at ht
  have ht2 : (match switchSeatIn P5T.seatsAllFull l ((switchSent p.sizes p.others).size - 1) with
      | some q =>
        decide (MList[maskNo seatsPlanW P5T.psFull l]? =
          some ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape) &&
        decide (LFull.places[maskNo seatsPlanW P5T.psFull l]? = some (q.j, q.t + 0))
      | none => false) = true := ht
  cases hq : switchSeatIn P5T.seatsAllFull l ((switchSent p.sizes p.others).size - 1) with
  | none =>
    rw [hq] at ht2
    cases ht2
  | some q =>
    rw [hq] at ht2
    obtain ⟨a1, a2⟩ := Eq.mp (Bool.and_eq_true _ _) ht2
    have a1' := of_decide_eq_true a1
    have a2' := of_decide_eq_true a2
    have hM := (facts_reached h hr hf).2.2.2.2
    have e3 : msgsOfChain Zp.made.proof.1 = MList := by
      rw [sends_in_scope h.toAtMg.scope h.toAtMg.laid.pub (P5J.pins_of_laid h.toAtMg.scope h.toAtMg.laid).1]
      exact MW_eq
    have hs := msgShape_at (st := s.st) hM _ hlt
    rw [e3, a1'] at hs
    have hlink : p.link = l := by
      have hbq := List.find?_some hp
      exact eq_of_beq hbq
    have w2 : P5J.At.pseatsAll Zp = P5T.seatsAllFull := (P5J.AtMg.seats_written h.toAtMg).2.1
    have hk : 14 * l + IM.nAt l + 5 ≤ 358 := by
      have hn : IM.nAt l = if l = 24 then 9 else 7 := rfl
      rw [hn]
      split <;> omega
    refine ⟨fun y hy => ?_, ?_⟩
    · rw [hy] at hs
      exact Option.some.inj hs
    · rw [seat_at_reach h hk hr hf hlt a2']
      unfold seatSw
      rw [w2, hlink, hq]
      rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.mask_seat_at
