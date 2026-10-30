-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Outs.lean: what the eight outputs of the run made of what was heard read
of the verifier's draws.

Main names:
  `pointAt_ini`, `ptN_read`: an output's point (the library's ptN) is the verifier's challenges,
    read (pt), as functions
    on the natural numbers.
  `RunPts`, `run_pts`: at the run: the eight points, and that each sumcheck has heard as many
    challenges as its letters
    have variables. At every parameter record.
  `run_zE`, `run_zVM`, `run_zVD`: the lookup's end point in three outputs' public states is the
    first statement's.
  `run_thVM`, `run_thVD`, `run_tg`, `run_tg_read`, `run_fn`, `gam_read`: the batching element, the
    first cut of the drawn point,
    the feature part of the point of the score at the index.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Rows
import Cb.Pv.Att.End.FirstOut
import Johnson.Road.FormsKeysEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH)
open VerifiableInference.Desc.Part
open Cb.Pv.Att.End (ptN pointAt)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K}

theorem pointAt_ini (T : PlainSc K) (o : T.our.par.Out) :
    pointAt T o = ldPartIni T.nv T.deg (pDummy K T.DY) o.pt :=
  ldPartVars_ini K T.nv T.deg T.dat (pDummy K T.DY) (pDummyD K T.DY) o.pt

/-- **An output's point is the verifier's challenges, read** (Att/K05Weights.lean's nat_ini, in the
library's ptN and pt). -/
theorem ptN_read {M Y : Type} (S : SumL K M Y) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf) :
    ptN S.T D.out = OnBytes.Road.pt ρ (chal hh) := by
  unfold ptN
  rw [pointAt_ini]
  exact nat_ini S D hs hD h

/-- The eight outputs' points, and how many challenges each sumcheck has heard. o1 o2: the two
units' records. -/
structure RunPts {Mg X : Type} (P : OwnPar K Mg X) (u : P.Run) (h : Heard) (o1 o2 : ℕ × MaskedSum.Heard) : Prop where
  xM : ptN P.uM.T u.oM = OnBytes.Road.pt ρ (chal o1.2)
  nM : (chal o1.2).size = P.uM.T.nv
  xD : ptN P.uD.T u.oD = OnBytes.Road.pt ρ (chal o2.2)
  nD : (chal o2.2).size = P.uD.T.nv
  xE : ptN P.sE.T u.oE = OnBytes.Road.pt ρ (chal h.division)
  nE : (chal h.division).size = P.sE.T.nv
  xVM : ptN P.sVM.T u.oVM = OnBytes.Road.pt ρ (chal h.below)
  nVM : (chal h.below).size = P.sVM.T.nv
  xVD : ptN P.sVD.T u.oVD = OnBytes.Road.pt ρ (chal h.on)
  nVD : (chal h.on).size = P.sVD.T.nv
  xF : ptN P.sF.T u.oF = OnBytes.Road.pt ρ (chal h.atIndex)
  nF : (chal h.atIndex).size = P.sF.T.nv
  xK : ptN P.sD.T u.oK = OnBytes.Road.pt ρ (chal h.key)
  nK : (chal h.key).size = P.sD.T.nv
  xH : ptN P.sH.T u.oH = OnBytes.Road.pt ρ (chal h.cells)
  nH : (chal h.cells).size = P.sH.T.nv

/-- **At the run made of what was heard.** -/
theorem run_pts {Mg X : Type} (P : OwnPar K Mg X) (x0 : X) {x : Params.AttentionRounds} {p1 p2 : ℕ × ℕ}
    (hsc : x.score = [p1, p2]) {h : Heard} {G : Fork} {L : Lists} (b2 : Said x h G L)
    (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail)
    (d1 : UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt x h L)
    (cu : OnBytes.Tie.Pv.Att.UnitsClaims (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))
    (ct : dt.Claims (OnBytes.Tie.Pv.Att.seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) :
    ∃ o1 o2, h.scores.toList = [o1, o2] ∧ RunPts (ρ := ρ) P (runHeard P x0 du dt) h o1 o2 := by
  have bu := b2.units
  rw [hsc] at bu d1
  obtain ⟨o1, o2, v1, H1, v2, H2, hos, hlu, ⟨_, _, a3, _⟩, ⟨_, _, a3', _⟩⟩ := units_two bu
  rw [hos, hlu] at d1
  obtain ⟨z1, of1, z2, of2, _⟩ := d1
  refine ⟨o1, o2, hos, ?_⟩
  constructor
  · rw [run_oM P x0 du dt cu]; exact ptN_read _ du.1 z1 of1 a3
  · exact chal_size _ du.1 z1 of1 a3
  · rw [run_oD P x0 du dt cu]; exact ptN_read _ du.2.1 z2 of2 a3'
  · exact chal_size _ du.2.1 z2 of2 a3'
  · rw [run_oE P x0 du dt ct]; exact ptN_read _ dt.dE d2.zE d2.oE b2.sE
  · exact chal_size _ dt.dE d2.zE d2.oE b2.sE
  · rw [run_oVM P x0 du dt ct]; exact ptN_read _ dt.dVM d2.zM d2.oM b2.sM
  · exact chal_size _ dt.dVM d2.zM d2.oM b2.sM
  · rw [run_oVD P x0 du dt ct]; exact ptN_read _ dt.dVD d2.zVD d2.oVD b2.sVD
  · exact chal_size _ dt.dVD d2.zVD d2.oVD b2.sVD
  · rw [run_oF P x0 du dt ct]; exact ptN_read _ dt.dF d2.zF d2.oF b2.sF
  · exact chal_size _ dt.dF d2.zF d2.oF b2.sF
  · rw [run_oK P x0 du dt ct]; exact ptN_read _ dt.dD d2.zD d2.oD b2.sD
  · exact chal_size _ dt.dD d2.zD d2.oD b2.sD
  · rw [run_oH P x0 du dt ct]; exact ptN_read _ dt.dH d2.zH d2.oH b2.sH
  · exact chal_size _ dt.dH d2.zH d2.oH b2.sH

/-! ## What the outputs' public states read -/

section States
variable {Mg X : Type} (P : OwnPar K Mg X) (x0 : X) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
  (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail)

theorem run_zE : AttSeg.Pub.z (runHeard P x0 du dt).oE.st = P.zOf x0 := rfl
theorem run_zVM : AttSeg.Pub.z (runHeard P x0 du dt).oVM.st = P.zOf x0 := rfl
theorem run_zVD : AttSeg.Pub.z (runHeard P x0 du dt).oVD.st = P.zOf x0 := rfl
theorem run_thVM : AttSeg.Pub.th (runHeard P x0 du dt).oVM.st = ρ.val dt.xV := rfl
theorem run_thVD : AttSeg.Pub.th (runHeard P x0 du dt).oVD.st = ρ.val dt.xV := rfl
theorem run_tg : (P.pubZ (runHeard P x0 du dt).z).tg = Blocks.nat (cutPt P.g1 P.g2 (rd ρ _ dt.pts)).1 := rfl

theorem run_tg_read (j : ℕ) (hj : j < P.g1) :
    (P.pubZ (runHeard P x0 du dt).z).tg j = ρ.val (dt.pts.getD j zeroE) :=
  nat_cut1 P.g1 P.g2 dt.pts j hj

/-- The feature part of the point of the score at the index, in the state of the key's output. -/
theorem run_fn {x : Params.AttentionRounds} {h : Heard} {G : Fork} {L : Lists} (b2 : Said x h G L)
    (d2 : TailOfP dt x h L)
    (ct : dt.Claims (OnBytes.Tie.Pv.Att.seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) (j : ℕ) :
    (Prod.fst (runHeard P x0 du dt).oK.st).fn j = ρ.val ((chal h.atIndex).getD (P.D.lT + P.D.lg + j) zeroE) := by
  show Blocks.nat (P.sF.ptOf (runHeard P x0 du dt).yF) (P.D.lT + P.D.lg + j) = _
  have e : P.sF.ptOf (runHeard P x0 du dt).yF =
      ldPartIni P.sF.T.nv P.sF.T.deg (pDummy K P.sF.T.DY) (runHeard P x0 du dt).oF.pt :=
    ldPartVars_ini K P.sF.T.nv P.sF.T.deg P.sF.T.dat (pDummy K P.sF.T.DY) (pDummyD K P.sF.T.DY) _
  rw [e, run_oF P x0 du dt ct]
  exact congrFun (nat_ini _ dt.dF d2.zF d2.oF b2.sF) _

omit [Fintype K] in
/-- The batching element of the value products, as K5's record holds it. -/
theorem gam_read {x : Params.AttentionRounds} {h : Heard} {G : Fork} {L : Lists} (b2 : Said x h G L) :
    ρ.val (h.gam.getD 1 zeroE) = ρ.val L.xV := by
  rw [b2.gam, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    powersFrom_read ρ L.xV 2 oneE 1 (by norm_num), ρ.one]
  ring

end States

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.run_pts
