-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/JoinShareMeets.lean: the kind "the code switch" (K2): UNDER THE
HEAD AND THE OPENING THE SHARED SENDING's LOTS AND THIS KIND's AGREE: at the joined lists that hold
the shared sending's 52 jobs and, for the others' record, this kind's share alone (`switchShareAt`,
Honest/K2/JoinShare.lean): `MsgsAgree` of the lots of messages, `PadsAgree` of the lots of pads; and
the share's members' numbers stand apart, from each other and from the shared sending's. Four
statements with their proofs; no definition.

  `share_meets_msgs`   `join_msgsAgree_head` called at the share
  `share_meets_pads`   `join_padsAgree_head` called at the share
  `share_meets_tn`     no member's number of the share stands twice: the premise htn of
                       `joinFit_head` (Honest/Thread/JoinAtHead.lean) at the share
  `share_meets_dis`    none of them is a number of the shared sending's 52 jobs: its premise hdis

By, of other authors: `join_msgsAgree_head`, `join_padsAgree_head`
(Honest/Thread/JoinAtHead.lean). Of ours: `share_msgsAgree_at_head`, `share_padsAgree_at_head`,
`share_far_msgs_at_head`, `share_far_pads_at_head` (Honest/K2/Law/JoinShareAtHead.lean) ·
`borders_apart_at_head`, `border_not_shared` (Honest/K2/Law/SwitchBorders.lean). WHY: the
last two were written after two premises of these laws; here Lean takes them for these premises.

Limits. THE OTHERS' RECORD HOLDS THIS KIND's SHARE ALONE: of a record that holds another kind's lots
too nothing is said: there that kind's lots are to agree among themselves, with this kind's and with
the shared sending's. That lots agree is no tie. No lot's text is opened. The full size and the
format's second hash function alone. The head and the opening are premises; that they can be met is not
said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.JoinAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.JoinShareAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchBorders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.FirstThread (TreeLot MsgsAgree PadsAgree joinMl joinPl byNo k1Jobs
  join_msgsAgree_head join_padsAgree_head byNo_at_head)

variable {W₀ Rc Xi Tr Xj X : Type} {Bk : ProverCoinCounts} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD AND THE OPENING: THE LOTS OF MESSAGES OF THE SHARED SENDING AND OF THIS KIND's
SHARE AGREE.** -/
theorem share_meets_msgs (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj) (front : Nat)
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj) (own₀ : X) (bs : List (Block S ProofFile.Cl))
    (front' : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    MsgsAgree (joinMl cF.blocksInOrder front (P5J.At.arr Zp) wit own₀
      (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
      (switchShareAt Bk bs front' Zp Bs.G₀ D readers rest)) :=
  join_msgsAgree_head h O no Dt Dd front wit own₀
    (share_msgsAgree_at_head h.toAtMg O bs front' D readers rest)
    (share_far_msgs_at_head h.toAtMg O bs front' D readers rest)

/-- **UNDER THE HEAD AND THE OPENING: THE LOTS OF PADS OF THE SHARED SENDING AND OF THIS KIND's
SHARE AGREE.** -/
theorem share_meets_pads (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj)
    (bs : List (Block S ProofFile.Cl)) (front' : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    PadsAgree (joinPl cF.blocksInOrder (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀))
      (switchShareAt Bk bs front' Zp Bs.G₀ D readers rest)) :=
  join_padsAgree_head h O no Dt Dd
    (share_padsAgree_at_head h.toAtMg O bs front' D readers rest)
    (share_far_pads_at_head h.toAtMg O bs front' D readers rest)

/-- **UNDER THE HEAD AND THE OPENING: NO MEMBER's NUMBER OF THE SHARE STANDS TWICE**, where the
share's numbers are taken in the first chain's flat list. -/
theorem share_meets_tn (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (front' : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    (switchShareAt Bk cF.blocksInOrder front' Zp Bs.G₀ D readers rest).tn.Nodup :=
  borders_apart_at_head h O

/-- **UNDER THE HEAD AND THE OPENING: NONE OF THEM IS A NUMBER OF THE SHARED SENDING's JOBS.** -/
theorem share_meets_dis (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf Xj)
    (front' : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    ∀ b ∈ (switchShareAt Bk cF.blocksInOrder front' Zp Bs.G₀ D readers rest).tn,
      b ∉ (byNo cF.blocksInOrder (k1Jobs (X := X) no Dt Dd Zp Bs.G₀)).map (·.1) := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
  rw [byNo_at_head h O no Dt Dd]
  exact border_not_shared h O hp _ _ _

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.share_meets_msgs
#print axioms ProofFile.Honest.K2.Law.share_meets_pads
#print axioms ProofFile.Honest.K2.Law.share_meets_tn
#print axioms ProofFile.Honest.K2.Law.share_meets_dis
