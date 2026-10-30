-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeOwnABFit.lean: the test `allFit` (Pay/MadeOwnAB.lean) says yes at the written shape,
codes and layout, by Lean's kernel, and so, under the head and the opening, at the ground's.

Limits. The head and the opening are premises. The full size alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnAB
import Johnson.Desc.ProofFile.Honest.K2.Law.LightAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The test at the written values. -/
theorem allFit_written : allFit proofSizedFull.codes proofSizedFull.request layoutFull = true := by decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **The test at the ground's values.** -/
theorem allFit_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) :
    allFit Bs.G₀.first.codes Bs.G₀.first.shape Bs.G₀.first.layout = true := by
  obtain ⟨e1, e2, e3⟩ := ProofFile.Honest.K2.Law.first_at_head h O
  rw [e1, e2, e3]
  exact allFit_written

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.allFit_written
#print axioms ProofFile.Honest.K10.allFit_at_head
