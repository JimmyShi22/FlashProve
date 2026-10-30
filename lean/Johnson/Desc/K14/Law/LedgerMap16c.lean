-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K14.Law.LedgerFieldE
import Johnson.P5J.LettersAt
import Johnson.P5J.DecFree
import Johnson.P5J.MgAtAll
import Johnson.Desc.K14.Law.SharedConstCodesAt
import Johnson.P5T.PlanSeatsTie
import Johnson.Goal.Numbers.RealShape
import Johnson.Goal.Numbers.WrittenInScope
import Johnson.HB.LLHARD.FiveWritten
import Johnson.HB.LLHARD.TreesWritten
import Johnson.Desc.K14.Law.SharedConstFarAt
import Johnson.Desc.K14.Law.SharedConstFive
/- a harness: «five» (the third of hO's named tests) at the closed constant P5J.mgAtAll, in scope, from the written
fact. Nothing is claimed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open VerifiableInference.Desc.Sound (LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.K13.Law (WRow evalLaidB wSitsB wSeatB wSitsItem)
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc (Strs)
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)



set_option linter.unusedVariables false
theorem map16_five
    (Dw : WholeD)
    (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (oL : ProofFile.SecondHashFunctionArgument)
    (Zs : VerifierAndGoals.PublicFiles)
    (rP : LPFD.Full.RunPF)
    (Np : H2U.Places4)
    (hpinS : VerifiableInference.PlanWritten.sizedPinnedAt Zp.p.X.P Zp.p.chains.made = true)
    (hpinF : VerifiableInference.PlanWritten.firstPinnedAt Zp.p.X.P Zp.first = true)
    (xLook : VerifiableInference.Desc.First.Look.Place)
    (hAtMgA : P5J.AtMgA oL Zs Dw rP Zp Np cF xLook)
    (eCodes : P5J.At.cs Zp = (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes)
    (hMadePinnedP1 : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first
      Zp.made = true) :
    (Sh.fiveNums (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub P5J.At.Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2))
          (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links Zp k14_real.choose map14_hx
          ((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
              (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      hpinS hpinF
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))
              ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
          oL Zs rP hAtMgA.scope
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          Np (eCodes ▸ P5J.At.smp Zp) (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
          (P5J.At.EAt Zs) (P5J.mgAtAll hAtMgA) hAtMgA.laid.pub hpinS hpinF)).Nodup := by
  have hlaidAll : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP) := hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks
  have SS := P5T.seats_in_scope hAtMgA.scope hAtMgA.laid.pub hMadePinnedP1 hlaidAll
  have Wr := written_in_scope hAtMgA.scope hAtMgA.laid.pub hpinS hpinF hlaidAll map14_hx
  have hf : fiveTen (Sh.nums (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub P5J.At.Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2))
          (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links Zp k14_real.choose map14_hx
          ((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
              (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      hpinS hpinF
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))
              ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
          oL Zs rP hAtMgA.scope
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          Np (eCodes ▸ P5J.At.smp Zp) (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
          (P5J.At.EAt Zs) (P5J.mgAtAll hAtMgA) hAtMgA.laid.pub hpinS hpinF)) = fiveTen numsFull := by
    funext q
    rcases q with _ | _ | m
    · exact congrArg (·.w) SS.2.2
    · exact congrArg (·.index) SS.2.2
    · have t := Sh.tenants_in_scope hAtMgA.scope hlaidAll hAtMgA.laid.value Wr Johnson.G.t1_written Np m
      rw [real_shape map14_hx] at t
      exact t
  have e : P5T.harrB (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fiveTen (Sh.nums (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub P5J.At.Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2))
          (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links Zp k14_real.choose map14_hx
          ((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
              (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      hpinS hpinF
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))
              ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
          oL Zs rP hAtMgA.scope
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          Np (eCodes ▸ P5J.At.smp Zp) (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
          (P5J.At.EAt Zs) (P5J.mgAtAll hAtMgA) hAtMgA.laid.pub hpinS hpinF))) fiveAll = true := by
    rw [hf, SS.2.1]
    exact five_written
  exact of_decide_eq_true ((Sh.five_is_harrB _ _).symm.trans e)
end Desc.K14.Law

#print axioms Desc.K14.Law.map16_five
