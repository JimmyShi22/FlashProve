-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K14.Law.LedgerSeatOwed
import Johnson.Desc.Sound.SeamDesc
import Johnson.Loose.H2K12.NineTenAtLaid
/- a harness: the number of trees that the first chain of the IOP as written in Lean tells, at the seat, in
scope, is the written data's, and that is a numeral. Nothing is claimed. -/
set_option autoImplicit false
namespace Desc.K14.Law
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.K12


theorem map15_t1 (oL : ProofFile.SecondHashFunctionArgument) (Zs : VerifierAndGoals.PublicFiles) (Dw : OnBytes.Maker.WholeD)
    (rP : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (hZs : VerifierAndGoals.InScope Zs = true)
    (hlaid : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP))
    (hdesc : ProofFile.onlineDescription oL Zs.pol Zs.lay Zs.KL = .ok (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                     ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                     ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                     Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                     (VerifiableInference.Desc.K12.Seat.tests Np))) :
    (VerifiableInference.Desc.oraclesOf (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.blocksInOrder).length = Johnson.G.writtenPFull.t₁ := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hlaid
  have e := Except.ok.inj (hF.symm.trans hdesc)
  subst e
  obtain ⟨_, _, _, _, _, _, hDW, _⟩ := H2K.JointK.nine_facts_laid Unit Zs hZs oL Dw rP hlaid
  rw [(Desc.K14.Law.Fence.counts_of_planOk _ _ _ hp hD).1, hDW]
end Desc.K14.Law

#print axioms Desc.K14.Law.map15_t1
