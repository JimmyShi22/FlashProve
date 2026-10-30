-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/FirstAtHeadW.lean: UNDER THE LIBRARY's HEAD (`P5J.AtMgA` and `IM.Open`: hypotheses):
THE INDEX-MASK MESSAGE OF THE FIRST OPENING HAS NO MAIN ROW:
so by `rowsR_no_main` no reader reaches that member's rows.

  `first_no_main_head`   the message has no main row at the head's public part and ground
  `first_member_head`   at `jobRealW`'s first member, at the head's public part and ground: the
                 member by name, and the premises hk and hm of `first_member_rows`

Limits.
- `first_last_no_main` (SendersW.lean) is the evaluation beneath: the full size alone.
- Nothing on completeness, soundness or hiding.

Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.HalfAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.SendersW
import Johnson.Desc.ProofFile.Honest.K12.AtProof.FirstMemberSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain Block)
open ProofFile.Honest ProofFile.Honest.K12.AtProof
open Johnson.Prover.Send (shapeAt)
open P5J (TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x) {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- **Under the head the index-mask message has no main row.** -/
theorem first_no_main_head : (shapeAt (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp)) ((VerifiableInference.Desc.K1.firstPar Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1)).mainRows = 0 := by
  rw [VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h)]
  exact first_last_no_main

omit h O in
/-- The index-mask message stands in its sending, at the written plan. -/
theorem first_last_lt : VerifiableInference.Desc.K1.parGF.sent.size - 1 <
    VerifiableInference.Desc.K1.parGF.sent.size := by decide +kernel

/-- **AT `jobRealW`'s FIRST MEMBER.** Where `jobRealW` returns at the head's public part and ground,
its first member is `memK1` of `K1.firstJob`, at the last message; that message stands in its
sending and has no main row: the premises hk and hm of `first_member_rows`, which the caller calls.
-/
theorem first_member_head {Xi W₀ Rc Tr X : Type} (S : OnBytes.HonestTrace.Sz)
    (Fd : VerifiableInference.Desc.FileDescription Xi)
    (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → Nat)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand)
    {M : ProofFile.Honest.K12.Light.ManyJob (Local W₀ Rc Xi Tr) X}
    (hM : jobRealW S Fd enter pile no readers weights rand Zp Bs.G₀ = some M) :
    ∃ fs, M.mems[0]? = some (memK1 (K1.firstJob S Zp Bs.G₀) readers senderI
        ((firstParOf Zp Bs.G₀).sent.size - 1) fs) ∧
      (firstParOf Zp Bs.G₀).sent.size - 1 < (firstParOf Zp Bs.G₀).sent.size ∧
      (shapeAt (firstParOf Zp Bs.G₀) ((firstParOf Zp Bs.G₀).sent.size - 1)).mainRows = 0 := by
  unfold jobRealW at hM
  obtain ⟨F, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  refine ⟨_, rfl, ?_, first_no_main_head h O⟩
  show (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
    (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1 <
    (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp)).sent.size
  rw [VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h)]
  exact first_last_lt

end AtFullSide.K12

#print axioms AtFullSide.K12.first_no_main_head
#print axioms AtFullSide.K12.first_last_lt
#print axioms AtFullSide.K12.first_member_head
