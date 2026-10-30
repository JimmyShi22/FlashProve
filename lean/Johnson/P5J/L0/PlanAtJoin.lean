-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/L0/PlanAtJoin.lean: THE LAST STEP OF PlanAtHead.lean, WHICH ONLY THE PORTED WORLD CAN SAY:
`PlanOk₃` AT THE HEAD AT THE JOIN's OWN LETTERS THEMSELVES: ms₂ := `Sh.ms A`, Ns := `numbersSh (Sh.t₁ A)
(Sh.layU A) (Sh.layO A) (0, 0) (0, 0)`, A := `Sh.planAt Zp Np (F0T o Zp Np cF)`. Here the shared
table's constant (Johnson/Desc/K14/Law/SharedConstAt.lean) stands beside `PlanOk₃` in one file.

  `sevenJ`: the join's seven letters, as one `ShSeven`.
  `planJ_is`: `PlanJ` at `sevenJ` IS `PlanOk₃` at these terms: by rfl.
  **`planOk₃_at_join`**: `planOk₃_of_core` at `sevenJ`, its end written out at the join's own terms.
One definition, two theorems. Limits: PlanAtHead.lean's: a member of the head is proved at `storedPublicFiles`
and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/); `CoreJ` is shown at no
letters. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.L0.PlanAtHead
import Johnson.Desc.K14.Law.SharedConstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J.L0
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)
open _root_.Desc.K14.Law.Fence (msSh numbersSh)
open _root_.Desc.K14.Law (Sh.planAt Sh.ms Sh.t₁ Sh.layU Sh.layO)
open LLT25

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The join's seven letters. -/
def sevenJ (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) : ShSeven :=
  ⟨(Sh.planAt Zp Np (F0T o Zp Np cF)).Q.S, (Sh.planAt Zp Np (F0T o Zp Np cF)).rad2 0,
    (Sh.planAt Zp Np (F0T o Zp Np cF)).rad5 0, (Sh.planAt Zp Np (F0T o Zp Np cF)).rad5 1,
    Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF)), Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF)),
    Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF))⟩

/-- **`PlanJ` at the join's seven is `PlanOk₃` at the join's own terms.** -/
theorem planJ_is (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (dB : RDT) (dt : List RDT)
    (Ld : VerifiableInference.Desc.K12.Door.Laid) :
    PlanJ o Z D Zp Np cF (sevenJ o Zp Np cF) dB dt Ld =
      PlanOk₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) (At.arr Zp) dB dt
        (At.ms Zp Z.lay) (Sh.ms (Sh.planAt Zp Np (F0T o Zp Np cF))) (At.N Zp cF)
        (numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF)))
          (Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF)))
          (0, 0) (0, 0))
        fullLinks (First.flatPlaces true fullLinks true) H2K.Member.rWFull
        ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) Ld := rfl

/-- **`PlanOk₃` AT THE HEAD, AT THE JOIN's OWN TERMS.** -/
theorem planOk₃_at_join (h : AtMg o Z D r Zp Np cF) (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (hn : 1 < (D.at frS.P.T.a).t₂)
    (hE : (At.N Zp cF).index.1 < (D.at frS.P.T.a).t₁ ∧ (At.N Zp cF).w.1 < (D.at frS.P.T.a).t₁)
    (hT : sampledBelow ((D.at frS.P.T.a).t₁ + (D.at frS.P.T.a).t₂) (At.N Zp cF)
        ((openSets fullLinks (First.flatPlaces true fullLinks true)
        (start fullLinks))[(First.flatPlaces true fullLinks true).length]?.getD []) = true ∧
      (At.N Zp cF).w ∈ sampledIn (At.N Zp cF)
        ((openSets fullLinks (First.flatPlaces true fullLinks true)
        (start fullLinks))[(First.flatPlaces true fullLinks true).length]?.getD []) ∧
      (At.N Zp cF).index ∈ sampledIn (At.N Zp cF)
        ((openSets fullLinks (First.flatPlaces true fullLinks true)
        (start fullLinks))[(First.flatPlaces true fullLinks true).length]?.getD []))
    (C : ∀ dB dt, StretchJ o D Zp Np cF dB dt →
      CoreJ o Z D Zp Np cF (sevenJ o Zp Np cF) dB dt Ld) :
    ∃ dB dt, PlanOk₃ o ProofFile.pureRoad.links Zp Np cF (D.at frS.P.T.a) (F0T o Zp Np cF) (At.arr Zp) dB dt
      (At.ms Zp Z.lay) (Sh.ms (Sh.planAt Zp Np (F0T o Zp Np cF))) (At.N Zp cF)
      (numbersSh (Sh.t₁ (Sh.planAt Zp Np (F0T o Zp Np cF)))
        (Sh.layU (Sh.planAt Zp Np (F0T o Zp Np cF))) (Sh.layO (Sh.planAt Zp Np (F0T o Zp Np cF)))
        (0, 0) (0, 0))
      fullLinks (First.flatPlaces true fullLinks true) H2K.Member.rWFull
      ((At.N Zp cF).treesAt none) 0 1 (vAt Zp (At.N Zp cF)) Ld :=
  planOk₃_of_core h (sevenJ o Zp Np cF) Ld hn hE hT C

end P5J.L0

#print axioms P5J.L0.planJ_is
#print axioms P5J.L0.planOk₃_at_join
