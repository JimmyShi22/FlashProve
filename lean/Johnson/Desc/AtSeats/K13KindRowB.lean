-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K13KindRowB.lean: KIND K13's ROW FOR THE JOIN, IN THE
COUNTED FORM hA.Kind 𝔏 KindName.K13, WITH NOTHING OF THE KIND's OWN LEFT ON THE LIST OF ROUNDS: the
four premises hCapB, hi, hn, hPl of K13KindRowA.lean are called inside, under the accept
of the entry tests' two comparisons with written values.
  hCapB  capB_atAll (Johnson/Desc/AtSeats/K13CapAtAll.lean): under hP1
  hi     indexTree_atAll (Johnson/Desc/AtSeats/K13PlanM3At.lean): under hP1
  hn     inFront355_atAll (the same file): under hP2
  hPl    planM3_written (the same file): under hP1 and hP2
Main names.
  d12Full              the proximity test's public data at the written values: first tree 0, LFull,
                       MFull (Johnson/HB/LLHARD/LaidWritten.lean): a closed term
  planM3_atFull        hPl at that term
  **k13_kindB_tight**  k13_kindA_tight at d₁₂ := d12Full: hft is rfl



WHAT IS LEFT, EACH WITH ITS KIND.
  hA          the shared head of every counted statement (P5J.AtMgA): conditions on
              the three public files alone: the goals' scope; "the files are read"; "the verifier's
              own value is laid"; seven named tests on the list of rounds; two more equations on
              public data. Which of them the verifier asks is not said here.
  q₁ q₂ q₃    equations on the letter 𝔏: its sub-protocols are the heads and rests of the three flat
              lists of the IOP as written in Lean. Met by laying 𝔏 so (P5J.LaidAt.heads: rfl).
  hP1, hP2    two tests with code on the public files. The entry tests (lawsAsk,
              Johnson/Desc/Laid/ProofAsks.lean) ask both; that "laid" gives their accepts is
              pins_of_laid (Johnson/Goal/Skeleton/PinsOfLaid.lean) with cutIs_of_laid
              (CutIsOfLaid.lean beside it), which are not called here.
  hNine       FACTS ALONG REACHED STATES: at every state that is reached with a typed public part
              and has not failed, nine tests on the state accept. No test of the verifier's: an
              induction along the run owes them. In k13_kindB_tight they stand at the written L
              and M.
What is not claimed. That any premise can be met. No member of hA.Kind. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13KindRowA
import Johnson.Desc.AtSeats.K13PlanM3At
import Johnson.Desc.AtSeats.K13CapAtAll

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
open Johnson.Desc.First.Walk.Tied (RchPub)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq)

/-- The proximity test's public data at the written values. -/
def d12Full : K12.Door.K12Data := ⟨0, LFull, MFull⟩

/-- hPl at the written data. -/
theorem planM3_atFull {o : ProofFile.SecondHashFunctionArgument} {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA o Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hP2 : cutIs (P5J.F0T o Zp Np cF) = true) :
    PlanM3 d12Full.L d12Full.M hA.𝔇.ms hA.𝔇.cs hA.𝔇.N :=
  planM3_written hA.scope hA.laid.pub
    (hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data hA.laid.asks)
    hP1 (cutIs_eq hP2).1 Zl.lay

/-- **Kind K13's row, counted form, tight, under the two comparisons' accepts.** -/
theorem k13_kindB_tight {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
    (hNine : ∀ j x,
      RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁
          0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j x → x.1.2.failed = none →
      NineK13 hA.𝔇.cs hA.𝔇.shape hA.𝔇.layout d12Full x.1.2) :
    hA.Kind 𝔏 KindName.K13 :=
  k13_kindA_tight hA 𝔏 q₁ q₂ q₃ d12Full (capB_atAll hA hP1) (indexTree_atAll hA hP1)
    (inFront355_atAll hP2) rfl (planM3_atFull hA hP1 hP2) hNine

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.planM3_atFull
#print axioms VerifiableInference.Desc.K13.Law.k13_kindB_tight
