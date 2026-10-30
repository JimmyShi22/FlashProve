-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PlanM3AtAll.lean: THE PREMISE W_hPl3 OF THE LAW ON THE SUB-PROTOCOL K1 AT W's
COMMITMENT (k01_kind_paidThree, Johnson/Desc/AtSeats/K01KindPaidThree.lean), AT THE
CLOSED CONSTANT (`hA.𝔇`, Johnson/P5J/MgAtAll.lean), in the premise's own type: one call of
`planM3_written` (Johnson/Desc/AtSeats/K13PlanM3At.lean). One statement with its proof; nothing is
evaluated here.
Premises: hA, hP1, hP2, as in TestsAtAll.lean (this folder); hL, hM: the proximity test's data hold
the written layout and shapes (rfl at dk := ⟨0, LFull, MFull⟩).
What is not claimed. That hP1 or hP2 accept at any files. No member of the head hA. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.AtSeats.K13PlanM3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (LFull MFull PlanM3)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq)
open ProofFile (Cl)

/-- **W_hPl3.** -/
theorem W_hPl3_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true) {dk : K12Data} (hL : dk.L = LFull)
    (hM : dk.M = MFull) : PlanM3 dk.L dk.M hA.𝔇.ms hA.𝔇.pubD.cs hA.𝔇.N := by
  rw [hL, hM]
  exact K13.Law.planM3_written hA.scope hA.laid.pub (laidP_atAll hA) hP1 (cutIs_eq hP2).1 Zl.lay

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.W_hPl3_atAll
