-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/Seat353OfShape.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN:
ONE FIELD OF K12's FILES' LIST
OF DEBTS (K12Left.seat353, H2K12/Owed354AtMg.lean), PAID AS IT STANDS: sub-protocol number 353 of
the first flat list sits at the place of the last code switch (SeatF1, H2K12/GroupAt354.lean),
with numbers whose group is the table's number of the last group. Two theorems: calls.
  seat353_of_shape   at the IOP as written in Lean, opened (IM.Open, Johnson/IMR/SeatOpen.lean).
  seat353_at_head    at the one head (P5J.AtMg, Johnson/P5J/AtMg.lean): the field to the
                  letter.
The equation on the group: the switch's numbers' group is the number of links of the request's shape
in the planner's sizes (numsAt_grp, Johnson/Top/H0/Tw/K2C/GroupAtNums.lean); that shape is the
ground's first chain's (prepOf_request, there), which is the public part's (blank_ground,
Johnson/IMR/PureJoin.lean); under hsh it is the written shape, which has 25 links (full_links,
Johnson/Desc/K1/Law/AtFull.lean: decided by the kernel).
Limits. hsh (the public part's first chain's shape is the written one) is a premise: its payer from
the pins on the written sendings is typed in another of K12's files. From the head alone the
equation is not had. The full size alone. No soundness statement. Nothing on hiding.

-/
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.Desc.K1.Law.AtFull
import Johnson.IMR.PureJoin
import Johnson.Loose.H2K12.Seat353AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-- **THE FIELD AT THE IOP AS WRITTEN IN LEAN, OPENED.** -/
theorem seat353_of_shape {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true)
    (hsh : Z.first.shape = VerifiableInference.Desc.ReqLit.shapeFull)
    (N : VerifiableInference.Desc.First.Numbers) (hN : N.groupAt 25 = 25) :
    ∃ b p, c.blocksInOrder[353]? = some b ∧ SeatF1 b p ∧ p.grp = N.groupAt 25 := by
  obtain ⟨k0, x, name, e0, -, -, -⟩ := Meaning.Carry.back_zero_at O
  have hb : c.blocksInOrder[353]? = some { k0 with planOk := k0.planOk && k0.hasNoClaimsAndNothingAfter } :=
    (IM.back_numbers hS hR O).1 0 k0 e0
  have hbl := (VerifiableInference.Desc.Sound.planOk_parts F hp).1
  obtain ⟨ls, -, -, -, eG⟩ := IM.blank_ground O.blank
  have eF := O.desc
  subst eF
  have hbl' : VerifiableInference.Desc.blocksOk c.blocksInOrder = true := hbl
  have h1 := List.all_eq_true.1 hbl' _ (List.mem_of_getElem? hb)
  rw [Bool.and_eq_true] at h1
  obtain ⟨Pp, n, nm, a, hP, hn, hK, hg⟩ := seatF1_open hS hR O hb h1.1
  refine ⟨_, _, hb, hK, ?_⟩
  rw [hg, P1K2.numsAt_grp hn, (P1K2.prepOf_request hP).2, eG, hsh, hN]
  exact VerifiableInference.Desc.K1.full_links

/-- **THE FIELD AT THE ONE HEAD, TO THE LETTER.** -/
theorem seat353_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hsh : Zp.first.shape = VerifiableInference.Desc.ReqLit.shapeFull) :
    ∃ B p, cF.blocksInOrder[353]? = some B ∧ SeatF1 B p ∧
      p.grp = (P5J.At.N Zp cF).groupAt P5J.fullLinks.length := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact seat353_of_shape h.scope h.reads O h.laid.planOk hsh (P5J.At.N Zp cF) rfl

end H2K12

#print axioms H2K12.seat353_of_shape
#print axioms H2K12.seat353_at_head
