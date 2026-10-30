-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the two first-chain jobs of the own test, at the written numbers.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/JobsAtW.lean: under the head the public numbers of the jobs that jobRealW hands the own test are PIw and PWw of Sim2/PublicAtW.lean, and W's rides as written. No property of the protocol is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.PublicAtW
import Johnson.HB.LLHARD.PlanInScope
import Johnson.HB.LLHARD.PlanAtQFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K1 (qFull LikeFull firstPar_full parW_full wMsg_full)
open VerifiableInference.Desc.K13.Law (gpFull wMsgFull wMsg_written likeFull_in_scope gpOf_in_scope)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- Under the head the public part's first chain and plan numbers are the written ones. -/
theorem like_head (h : P5J.AtMg o Z D r₀ Zp Np cF) : LikeFull Zp.first ∧ VerifiableInference.Desc.K1.gpOf Zp = gpFull :=
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  ⟨likeFull_in_scope h.scope h.laid.pub hy, gpOf_in_scope h.scope h.laid.pub hy⟩

/-- **The first sending's numbers at the job.** -/
theorem firstPar_head (h : P5J.AtMg o Z D r₀ Zp Np cF) {G : ProofFile.Ground} (hf : G.first = Zp.first) :
    VerifiableInference.Desc.K1.firstPar G.first (VerifiableInference.Desc.K1.gpOf Zp) = PIw := by
  obtain ⟨hl, hg⟩ := like_head h
  rw [hf, hg, firstPar_full hl]

/-- **W's message and numbers at the job.** -/
theorem parW_head (h : P5J.AtMg o Z D r₀ Zp Np cF) {msg : Array OnBytes.OracleNotice}
    (hm : OnBytes.linMessageW Zp.first.lin = some msg) :
    msg = wMsgFull ∧ VerifiableInference.Desc.K1.parW Zp.first (ProofFile.Honest.K1.wGp Zp) 4 msg = PWw := by
  obtain ⟨hl, hg⟩ := like_head h
  have e : msg = wMsgFull := Option.some.inj (hm.symm.trans ((wMsg_full hl).trans wMsg_written))
  subst e
  refine ⟨rfl, ?_⟩
  have hw : ProofFile.Honest.K1.wGp Zp = gpFull := hg
  rw [hw, parW_full hl]

/-- **W's ride at the job.** -/
theorem wFold_head (h : P5J.AtMg o Z D r₀ Zp Np cF) : ProofFile.Honest.K1.wFold Zp.first.lin = ProofFile.Honest.K1.wFold qFull.lin := by
  obtain ⟨hl, -⟩ := like_head h
  rw [hl.lin]
  rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.like_head
#print axioms ProofFile.Honest.K12.Sim2.firstPar_head
#print axioms ProofFile.Honest.K12.Sim2.parW_head
#print axioms ProofFile.Honest.K12.Sim2.wFold_head
