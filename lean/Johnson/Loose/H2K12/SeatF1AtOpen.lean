-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/SeatF1AtOpen.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's
FIRST CHAIN: sub-protocol number 353 of the IOP as written in Lean, opened (IM.Open,
Johnson/IMR/SeatOpen.lean), SITS AT THE PLACE OF THE LAST CODE SWITCH (SeatF1,
H2K12/GroupAt354.lean), with the numbers that the list of rounds gives there. One theorem: calls.
  seatF1_open     in scope, where the sub-protocol passes its test on the list of rounds: there are
                  P and n with prepOf Z G₀ = some P and numsAt P none = some n, and SeatF1 holds at
                  k2P Z a nm .finish n, whose group's number is n.grp.
By the road of adds_at_353 (Johnson/IMR/MsgsBehind.lean): back_zero_at (there) · back_numbers
(Johnson/IMR/BackSeat.lean) · alone_underR, alone_planOk, retype_planOk (Johnson/IMR/SeatForm.lean):
an accept of the seated sub-protocol is one of the lot's, at every state · k2_mem, K2Is.live
(Johnson/IMR/K2Seat.lean).
Limits. hp (the sub-protocol's own test on the list of rounds accepts) is a premise. That n.grp is
the table's number of the last group: grp_finish_of_id, hgrp_finish_scope
(Johnson/Top/H0/Tw/K2C/GroupAtNums.lean, GroupAtScope.lean [not in this library]):
not called here. No soundness
statement. Nothing on hiding.

-/
import Johnson.IMR.MsgsBehind
import Johnson.Loose.H2K12.GroupAt354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

/-- **SUB-PROTOCOL NUMBER 353 SITS AT THE PLACE OF THE LAST CODE SWITCH.** -/
theorem seatF1_open {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S ProofFile.Cl}
    (hb : c.blocksInOrder[353]? = some b) (hp : b.planOk = true) :
    ∃ Pp n nm a, P1K2.prepOf Z Bs.G₀ = some Pp ∧ P1K2.numsAt Pp none = some n ∧
      SeatF1 b (IM.k2P Z a nm .finish n) ∧ (IM.k2P Z a nm .finish n).grp = n.grp := by
  obtain ⟨k0, x, name, e0, hx, hln, hla⟩ := Meaning.Carry.back_zero_at O
  obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 0 k0 e0).symm.trans hb)
  have hpb : (x.retype : Block S ProofFile.Cl).planOk = true := by
    have a1 : (k0.planOk && k0.hasNoClaimsAndNothingAfter) = true := hp
    rw [Bool.and_eq_true] at a1
    rw [← IM.alone_planOk hla]
    exact a1.1
  obtain ⟨Pp, nn, hP, hn, arms⟩ := (IM.k2_mem hx).live (IM.retype_planOk x hpb).1
  rw [hln] at hn
  rcases arms with ⟨-, ex⟩ | ⟨l', HP, el, -, -⟩ | ⟨l', el, -⟩
  · refine ⟨Pp, nn, x.name, x.place, hP, hn, ⟨rfl, fun s rs gs t hd => ?_⟩, rfl⟩
    have hdx : x.decide s rs gs = .ok t := (IM.alone_underR hla).2 _ _ _ _ hd
    rw [ex] at hdx
    exact hdx
  · rw [hln] at el
    cases el
  · rw [hln] at el
    cases el

end H2K12

#print axioms H2K12.seatF1_open
