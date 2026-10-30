-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K13KindTight.lean: KIND K13's ROW UNDER THE SHARED HEAD AND
THE ENTRY TESTS' TWO COMPARISONS, WITH THE SECOND ASKED NO WIDER THAN IT IS SPENT.
k13_kindC (K13NineAtAll.lean) takes hP2 : cutIs (F0T …) = true, which
compares the cuts of ALL THREE chains with the written lists; the row spends the first chain's
alone. Here the premise is that one equation:
  hC : cutOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = cutFirstFull.
A weaker premise, so a stronger statement. No letter of the files beneath turns: their bricks
(planM3_written, inFront355_of_cut, inFront_written, nine_atAll, capB_atAll, indexTree_atAll) are
tight already and are called here.
  inFront355_atCut   hn : 1 ≤ inFront355 cF, from hC
  planM3_atCut       hPl at the written data d12Full, from hA, hP1, hC
  **k13_kindD**      hA.Kind 𝔏 KindName.K13 from hA, q₁ q₂ q₃, hP1, hC
  k13_kindC_of_D     the form with hP2 follows (cutIs_eq)

Of hA the proof of k13_kindD uses at most these fields: scope, reads; of «laid»: pub, value, planOk,
data, run, asks, opened; of «plan»: shape, laid, named, fit, groups. The five fields of «plan» are
Boolean tests on values computed from the public files; they are not themselves entry tests. None of
these fields is proved in this file: all are assumed with hA.
What is not claimed. That hA, hP1 or hC can be met: NO MEMBER. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13NineAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open OnBytes.Road OnBytes.RunA
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq cutOf cutFirstFull)

/-- hn, from the first chain's cut alone. -/
theorem inFront355_atCut {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl}
    (hC : cutOf (P5J.F0T o Zp Np cF).first.blocksInOrder = cutFirstFull) : 1 ≤ inFront355 cF := by
  rw [inFront355_of_cut (cF := cF) hC, inFront_written]
  decide

/-- hPl at the written data, from the first chain's cut alone. -/
theorem planM3_atCut {o : ProofFile.SecondHashFunctionArgument} {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA o Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hC : cutOf (P5J.F0T o Zp Np cF).first.blocksInOrder = cutFirstFull) :
    PlanM3 d12Full.L d12Full.M hA.𝔇.ms hA.𝔇.cs hA.𝔇.N :=
  planM3_written hA.scope hA.laid.pub
    (hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data hA.laid.asks)
    hP1 hC Zl.lay

/-- **Kind K13's row, counted form, under the shared head, the first comparison's accept and the
first chain's cut.** -/
theorem k13_kindD {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hC : cutOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = cutFirstFull) :
    hA.Kind 𝔏 KindName.K13 :=
  k13_kindA_tight hA 𝔏 q₁ q₂ q₃ d12Full (capB_atAll hA hP1) (indexTree_atAll hA hP1)
    (inFront355_atCut hC) rfl (planM3_atCut hA hP1 hC) (nine_atAll hA hP1)

/-- The form with hP2 follows. -/
theorem k13_kindC_of_D {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true) :
    hA.Kind 𝔏 KindName.K13 :=
  k13_kindD hA 𝔏 q₁ q₂ q₃ hP1 (cutIs_eq hP2).1

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.inFront355_atCut
#print axioms VerifiableInference.Desc.K13.Law.planM3_atCut
#print axioms VerifiableInference.Desc.K13.Law.k13_kindD
#print axioms VerifiableInference.Desc.K13.Law.k13_kindC_of_D
