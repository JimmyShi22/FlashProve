-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Run.lean: the run made of what was heard (Att/K05RunHeard.lean), field by
field.

Main names:
  `run_x0`, `run_rM`, `run_rD`, `run_rE`, `run_th`, `run_rV`, `run_pt`, `run_s`, `run_bF`, `run_bK`,
    `run_bH`: by definition: the
    first statement; the riders, the draws and the pairs' scalars, read.
  `run_oM`, `run_oD` (under the units' claims), `run_oE`, `run_oVM`, `run_oVD`, `run_oF`, `run_oK`,
    `run_oH` (under the tail's
    claims): the eight outputs are the data's own (SumH.out). So the library's plain_st, plain_eps,
      plain_vals, plain_ini,
    plain_last read each output off what was heard.
  `run_y0`, `run_yE`, `run_yVM`: the statements between.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RunHeard
import OnBytes.Tie.Pv.Psc.PscRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model Johnson.L5.Layers
open OnBytes.Tie.Pv.Att (UnitsH TailH SumH UnitsClaims seenAfter ownTrs)

variable {K : Type} [Field K] [Fintype K] {X Mg : Type} {ρ : Reading K}

section
variable (P : OwnPar K Mg X) (x0 : X) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
  (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail)

theorem run_x0 : (runHeard P x0 du dt).x = x0 := rfl
theorem run_rM : (runHeard P x0 du dt).rM = du.1.rd := rfl
theorem run_rD : (runHeard P x0 du dt).rD = du.2.1.rd := rfl
theorem run_rE : (runHeard P x0 du dt).rE = dt.dE.rd := rfl
theorem run_th : (runHeard P x0 du dt).th = ρ.val dt.xV := rfl
theorem run_rV : (runHeard P x0 du dt).rV = dt.dVM.rd := rfl
theorem run_pt : (runHeard P x0 du dt).pt = rd ρ _ dt.pts := rfl
theorem run_s : (runHeard P x0 du dt).s = rd ρ _ dt.mx := rfl
theorem run_bF : (runHeard P x0 du dt).bF = ρ.val dt.xF := rfl
theorem run_bK : (runHeard P x0 du dt).bK = ρ.val dt.xD := rfl
theorem run_bH : (runHeard P x0 du dt).bH = ρ.val dt.xH := rfl

theorem run_oM (hu : UnitsClaims _ du (x0, [])) : (runHeard P x0 du dt).oM = du.1.out := by
  have h : du.1.Claim (x0, []) := hu.1
  show shortV P.uM.T.our.par P.uM.T.fix (P.uM.cl (x0, []) du.1.rd) (unrideN P.uM.T.our.par P.uM.n du.1.tr) = _
  rw [show P.uM.cl (x0, []) du.1.rd = (ρ.val du.1.t, du.1.st) from h]
  rfl

theorem run_oD (hu : UnitsClaims _ du (x0, [])) : (runHeard P x0 du dt).oD = du.2.1.out := by
  have h : du.2.1.Claim (x0, [List.ofFn du.1.rd]) := hu.2.1
  show shortV P.uD.T.our.par P.uD.T.fix (P.uD.cl (x0, [List.ofFn du.1.rd]) du.2.1.rd)
    (unrideN P.uD.T.our.par P.uD.n du.2.1.tr) = _
  rw [show P.uD.cl (x0, [List.ofFn du.1.rd]) du.2.1.rd = (ρ.val du.2.1.t, du.2.1.st) from h]
  rfl

theorem run_oE (ht : dt.Claims (seenAfter _ du (x0, []))) : (runHeard P x0 du dt).oE = dt.dE.out := by
  have h := ht.cE
  show shortV P.sE.T.our.par P.sE.T.fix (P.sE.cl (x0, [List.ofFn du.1.rd, List.ofFn du.2.1.rd]) dt.dE.rd)
    (unrideN P.sE.T.our.par P.sE.n dt.dE.tr) = _
  rw [show P.sE.cl (x0, [List.ofFn du.1.rd, List.ofFn du.2.1.rd]) dt.dE.rd = (ρ.val dt.dE.t, dt.dE.st) from h]
  rfl

theorem run_y0 : (runHeard P x0 du dt).y0 = seenAfter _ du (x0, []) := rfl

theorem run_yE (ht : dt.Claims (seenAfter _ du (x0, []))) :
    ((runHeard P x0 du dt).yE, (runHeard P x0 du dt).th) = dt.x2 (seenAfter _ du (x0, [])) := by
  show ((((runHeard P x0 du dt).y0, (runHeard P x0 du dt).rE), (runHeard P x0 du dt).oE), _) = _
  rw [run_oE P x0 du dt ht]
  rfl

theorem run_oVM (ht : dt.Claims (seenAfter _ du (x0, []))) : (runHeard P x0 du dt).oVM = dt.dVM.out := by
  show shortV P.sVM.T.our.par P.sVM.T.fix
    (P.sVM.cl ((runHeard P x0 du dt).yE, (runHeard P x0 du dt).th) dt.dVM.rd)
    (unrideN P.sVM.T.our.par P.sVM.n dt.dVM.tr) = _
  rw [run_yE P x0 du dt ht,
    show P.sVM.cl (dt.x2 (seenAfter _ du (x0, []))) dt.dVM.rd = (ρ.val dt.dVM.t, dt.dVM.st) from ht.cVM]
  rfl

theorem run_yVM (ht : dt.Claims (seenAfter _ du (x0, []))) :
    (runHeard P x0 du dt).yVM = dt.x3 (seenAfter _ du (x0, [])) := by
  show ((((runHeard P x0 du dt).yE, (runHeard P x0 du dt).th), (runHeard P x0 du dt).rV),
    (runHeard P x0 du dt).oVM) = _
  rw [run_yE P x0 du dt ht, run_oVM P x0 du dt ht]
  rfl

theorem run_oVD (ht : dt.Claims (seenAfter _ du (x0, []))) : (runHeard P x0 du dt).oVD = dt.dVD.out := by
  show shortV P.sVD.T.our.par P.sVD.T.fix (P.sVD.cl (runHeard P x0 du dt).yVM dt.dVD.rd)
    (unrideN P.sVD.T.our.par P.sVD.n dt.dVD.tr) = _
  rw [run_yVM P x0 du dt ht,
    show P.sVD.cl (dt.x3 (seenAfter _ du (x0, []))) dt.dVD.rd = (ρ.val dt.dVD.t, dt.dVD.st) from ht.cVD]
  rfl

theorem run_oF (ht : dt.Claims (seenAfter _ du (x0, []))) : (runHeard P x0 du dt).oF = dt.dF.out := by
  show shortV P.sF.T.our.par P.sF.T.fix
    (P.sF.cl ((((((runHeard P x0 du dt).yVM, dt.dVD.rd), (runHeard P x0 du dt).oVD), rd ρ _ dt.pts), rd ρ _ dt.mx),
      ρ.val dt.xF) dt.dF.rd) (unrideN P.sF.T.our.par P.sF.n dt.dF.tr) = _
  rw [run_yVM P x0 du dt ht, run_oVD P x0 du dt ht]
  show shortV P.sF.T.our.par P.sF.T.fix (P.sF.cl (dt.x6 (seenAfter _ du (x0, []))) dt.dF.rd) _ = _
  rw [show P.sF.cl (dt.x6 (seenAfter _ du (x0, []))) dt.dF.rd = (ρ.val dt.dF.t, dt.dF.st) from ht.cF]
  rfl

theorem run_oK (ht : dt.Claims (seenAfter _ du (x0, []))) : (runHeard P x0 du dt).oK = dt.dD.out := by
  show shortV P.sD.T.our.par P.sD.T.fix
    (P.sD.cl (((((((((runHeard P x0 du dt).yVM, dt.dVD.rd), (runHeard P x0 du dt).oVD), rd ρ _ dt.pts),
      rd ρ _ dt.mx), ρ.val dt.xF), dt.dF.rd), (runHeard P x0 du dt).oF), ρ.val dt.xD) dt.dD.rd)
    (unrideN P.sD.T.our.par P.sD.n dt.dD.tr) = _
  rw [run_yVM P x0 du dt ht, run_oVD P x0 du dt ht, run_oF P x0 du dt ht]
  show shortV P.sD.T.our.par P.sD.T.fix (P.sD.cl (dt.x8 (seenAfter _ du (x0, []))) dt.dD.rd) _ = _
  rw [show P.sD.cl (dt.x8 (seenAfter _ du (x0, []))) dt.dD.rd = (ρ.val dt.dD.t, dt.dD.st) from ht.cD]
  rfl

theorem run_oH (ht : dt.Claims (seenAfter _ du (x0, []))) : (runHeard P x0 du dt).oH = dt.dH.out := by
  show shortV P.sH.T.our.par P.sH.T.fix
    (P.sH.cl ((((((((((((runHeard P x0 du dt).yVM, dt.dVD.rd), (runHeard P x0 du dt).oVD), rd ρ _ dt.pts),
      rd ρ _ dt.mx), ρ.val dt.xF), dt.dF.rd), (runHeard P x0 du dt).oF), ρ.val dt.xD), dt.dD.rd),
      (runHeard P x0 du dt).oK), ρ.val dt.xH) dt.dH.rd)
    (unrideN P.sH.T.our.par P.sH.n dt.dH.tr) = _
  rw [run_yVM P x0 du dt ht, run_oVD P x0 du dt ht, run_oF P x0 du dt ht, run_oK P x0 du dt ht]
  show shortV P.sH.T.our.par P.sH.T.fix (P.sH.cl (dt.x10 (seenAfter _ du (x0, []))) dt.dH.rd) _ = _
  rw [show P.sH.cl (dt.x10 (seenAfter _ du (x0, []))) dt.dH.rd = (ρ.val dt.dH.t, dt.dH.st) from ht.cH]
  rfl

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.run_oH
