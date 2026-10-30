-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.HB.LLHARD.WrittenInScope
import Johnson.HB.LLHARD.K12FitTop
import Johnson.Loose.H2K12.FirstTieAtSeats
import Johnson.Loose.H2K12.OmegaIsSome
import Johnson.Desc.K14.Law.LedgerSeatOwed
import Johnson.Desc.K14.Law.SharedConst
import Johnson.Desc.K14.Law.LedgerToldFitOwed
import Johnson.Second.Seam.SplitWritten
/- a harness: tA, tB, fSp9, fSp10, hn, hTold, hx of the map «binder ↦ term», held by Lean against the
binders' own types as ledger_field_seat (the seventh form, at the seat) has them. Nothing is claimed. -/
set_option autoImplicit false
namespace Desc.K14.Law
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.K12
open H2K.JointK (descN pGu pGomega)

variable (oL : ProofFile.SecondHashFunctionArgument) (Zs : VerifierAndGoals.PublicFiles) (Dw : OnBytes.Maker.WholeD) (rP : LPFD.Full.RunPF)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
  (x : OnBytes.Params.LinSized)
  (hZs : VerifierAndGoals.InScope Zs = true)
  (hlaid : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP))
  (hpub : ProofFile.pureRoad.pub oL Zs.pol Zs.lay Zs.KL = .ok Zp)
  (hNp : H2U.placesOfMade Zp.made = .ok Np)
  (hdesc : ProofFile.onlineDescription oL Zs.pol Zs.lay Zs.KL = .ok (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                     ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                     ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                     Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                     (VerifiableInference.Desc.K12.Seat.tests Np)))
  (hpinS : VerifiableInference.PlanWritten.sizedPinnedAt Zp.p.X.P Zp.p.chains.made = true)
  (hpinF : VerifiableInference.PlanWritten.firstPinnedAt Zp.p.X.P Zp.first = true)
  (hx : VerifiableInference.Desc.K1.realSized = some (x, Johnson.G.codesFull2))

include hlaid hdesc in
/-- The whole test on the list of rounds accepts, and the seat's pin, at the description `descN`. -/
theorem map14_plan :
    (descN oL ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF).planOk = true ∧
      VerifiableInference.PlanWritten.seatPinnedProof Zs.pol
        (descN oL ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF) = true := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hlaid
  have e := Except.ok.inj (hF.symm.trans hdesc)
  subst e
  exact ⟨hp, LPFD.asks_written hs⟩

include hZs hlaid hpub hNp hdesc in
theorem map14_stagesU :
    (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U).nums.stages = H2K.Member.piUFull.nums.stages :=
  (congrArg (·.stages) (H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ Np.U
    (H2K.JointK.plan_at_seat_U oL Zp ProofFile.pureRoad.links Np cF
      (map14_plan oL Zs Dw rP Zp Np cF hlaid hdesc).1))).trans
    (H2K.Sizes.place_U_of_full (H2K.Sizes.atFull_of_pubPlain hZs hpub) hNp).1

include hZs hlaid hpub hNp hdesc in
theorem map14_tA :
    FirstTie H2K.Member.setAt H2K.Member.szUFull (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U)
      H2K.Member.rUFull :=
  H2K.JointK.firstTie_in_scope_U hZs Zp hpub ProofFile.pureRoad.links Np cF hNp
    (map14_plan oL Zs Dw rP Zp Np cF hlaid hdesc).1

include hZs hlaid hpub hNp hdesc in
theorem map14_tB :
    FirstTie H2K.Member.setAt H2K.Member.szOFull
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (Np.O.getD Np.U)) H2K.Member.rOFull := by
  have P := map14_plan oL Zs Dw rP Zp Np cF hlaid hdesc
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope hZs Zp ProofFile.pureRoad.links Np cF P.1 P.2
  rw [hO, Option.getD_some]
  exact H2K.JointK.firstTie_in_scope_O hZs Zp hpub ProofFile.pureRoad.links Np nO hO cF hNp P.1

include hZs hlaid hpub hNp hdesc in
theorem map14_stagesO :
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (Np.O.getD Np.U)).nums.stages =
      H2K.Member.piOFull.nums.stages := by
  have P := map14_plan oL Zs Dw rP Zp Np cF hlaid hdesc
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope hZs Zp ProofFile.pureRoad.links Np cF P.1 P.2
  rw [hO, Option.getD_some]
  exact (congrArg (·.stages) (H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO
    (H2K.JointK.plan_at_seat_O oL Zp ProofFile.pureRoad.links Np nO hO cF P.1))).trans
    (H2K.Sizes.place_O_of_full (H2K.Sizes.atFull_of_pubPlain hZs hpub) hNp nO hO).1

include hZs hlaid hpub hpinS hpinF hx in
theorem map14_hn : 2 ^ Zp.first.binding.logLeaves ≤ 64 :=
  (written_in_scope hZs hpub hpinS hpinF hlaid hx).slots

theorem map14_hTold : ToldFitOwed := fun x h => Second.Seam.toldFit_written x h

theorem map14_hx : VerifiableInference.Desc.K1.realSized =
    some (k14_real.choose, Johnson.G.codesFull2) := k14_real.choose_spec.1

include hZs hlaid hpub hNp hdesc hpinS hpinF hx in
theorem map14_fSp9 {Xi : Type} (G : FileDescription Xi) (pLast) (rad2 rad5 Wr) :
    ∀ a₀ rest, (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U).nums.stages = a₀ :: rest →
      0 < (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplit.maskRows ∧
      (p14Of Zp.p.chains (beforePointOf Np)).codes.base.size ≤
        (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplit.code ∧
      ((Sh.layO (ShPlan.mk (p14Of Zp.p.chains (beforePointOf Np)) G pLast rad2 rad5 Wr 2)).shapes.getD
        ((Sh.layO (ShPlan.mk (p14Of Zp.p.chains (beforePointOf Np)) G pLast rad2 rad5 Wr 2)).tree.getD
          1 0) default).logN ≤ a₀.Z.a := by
  have W := written_in_scope hZs hpub hpinS hpinF hlaid hx
  have hS : (p14Of Zp.p.chains (beforePointOf Np)).S = x.shape := W.shape
  have hc : (p14Of Zp.p.chains (beforePointOf Np)).codes = Johnson.G.codesFull2 := W.codes
  unfold Sh.layO
  show ∀ a₀ rest, (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U).nums.stages = a₀ :: rest →
      0 < (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplit.maskRows ∧
      (p14Of Zp.p.chains (beforePointOf Np)).codes.base.size ≤
        (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplit.code ∧
      (((OnBytes.layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes
        (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S)).getD default).shapes.getD
        (((OnBytes.layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes
          (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S)).getD default).tree.getD 1 0)
        default).logN ≤ a₀.Z.a
  rw [hS, hc]
  exact Second.Seam.fSp_written_U x hx _ (map14_stagesU oL Zs Dw rP Zp Np cF hZs hlaid hpub hNp hdesc)
include hZs hlaid hpub hNp hdesc hpinS hpinF hx in
theorem map14_fSp10 {Xi : Type} (G : FileDescription Xi) (pLast) (rad2 rad5 Wr) :
    ∀ a₀ rest, (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (Np.O.getD Np.U)).nums.stages = a₀ :: rest →
      0 < (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplit.maskRows ∧
      (p14Of Zp.p.chains (beforePointOf Np)).codes.base.size ≤
        (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplit.code ∧
      ((Sh.layO (ShPlan.mk (p14Of Zp.p.chains (beforePointOf Np)) G pLast rad2 rad5 Wr 2)).shapes.getD
        ((Sh.layO (ShPlan.mk (p14Of Zp.p.chains (beforePointOf Np)) G pLast rad2 rad5 Wr 2)).tree.getD
          1 0) default).logN ≤ a₀.Z.a := by
  have W := written_in_scope hZs hpub hpinS hpinF hlaid hx
  have hS : (p14Of Zp.p.chains (beforePointOf Np)).S = x.shape := W.shape
  have hc : (p14Of Zp.p.chains (beforePointOf Np)).codes = Johnson.G.codesFull2 := W.codes
  unfold Sh.layO
  show ∀ a₀ rest, (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (Np.O.getD Np.U)).nums.stages = a₀ :: rest →
      0 < (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplit.maskRows ∧
      (p14Of Zp.p.chains (beforePointOf Np)).codes.base.size ≤
        (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplit.code ∧
      (((OnBytes.layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes
        (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S)).getD default).shapes.getD
        (((OnBytes.layTrees (p14Of Zp.p.chains (beforePointOf Np)).codes
          (withOmega (p14Of Zp.p.chains (beforePointOf Np)).S)).getD default).tree.getD 1 0)
        default).logN ≤ a₀.Z.a
  rw [hS, hc]
  exact Second.Seam.fSp_written_O x hx _ (map14_stagesO oL Zs Dw rP Zp Np cF hZs hlaid hpub hNp hdesc)
end Desc.K14.Law

#print axioms Desc.K14.Law.map14_plan
#print axioms Desc.K14.Law.map14_stagesU
#print axioms Desc.K14.Law.map14_stagesO
#print axioms Desc.K14.Law.map14_tA
#print axioms Desc.K14.Law.map14_tB
#print axioms Desc.K14.Law.map14_hn
#print axioms Desc.K14.Law.map14_hTold
#print axioms Desc.K14.Law.map14_hx
#print axioms Desc.K14.Law.map14_fSp9
#print axioms Desc.K14.Law.map14_fSp10
