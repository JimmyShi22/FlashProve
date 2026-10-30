-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K14.Law.LedgerMap15
import Johnson.Desc.K14.Law.LedgerFieldLaid
import Johnson.P5J.LettersAt
import Johnson.HB.LLHARD.TreesWritten
/- a harness: hI, hV of the map «binder ↦ term», held by Lean against the binders' own types as
k14_field_e_all (at the closed constant P5J.mgAtAll) has them. Nothing is claimed. -/
set_option autoImplicit false
namespace Desc.K14.Law
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.K12

theorem map16_hI_hV (oL : ProofFile.SecondHashFunctionArgument) (Zs : VerifierAndGoals.PublicFiles) (Dw : OnBytes.Maker.WholeD)
    (rP : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (hZs : VerifierAndGoals.InScope Zs = true)
    (hlaid : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP))
    (hpub : ProofFile.pureRoad.pub oL Zs.pol Zs.lay Zs.KL = .ok Zp)
    (hdesc : ProofFile.onlineDescription oL Zs.pol Zs.lay Zs.KL = .ok (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                     ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                     ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                     Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                     (VerifiableInference.Desc.K12.Seat.tests Np)))
    (hMadePinnedP1 : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first
      Zp.made = true) :
    ((P5J.At.N Zp cF).index.1 < ((Desc.K14.Law.Sh.t₁ (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))) ∧
    ((P5J.At.N Zp cF).w.1 < ((Desc.K14.Law.Sh.t₁ (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))) := by
  have T := map15_t1 oL Zs Dw rP Zp Np cF hZs hlaid hdesc
  have H := Johnson.G.hI_hV_t1_in_scope hZs hpub hMadePinnedP1 hlaid
  constructor
  · show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).index.1 <
      (VerifiableInference.Desc.oraclesOf (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.blocksInOrder).length
    rw [T]
    exact H.1
  · show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).w.1 <
      (VerifiableInference.Desc.oraclesOf (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.blocksInOrder).length
    rw [T]
    exact H.2
end Desc.K14.Law

#print axioms Desc.K14.Law.map16_hI_hV
