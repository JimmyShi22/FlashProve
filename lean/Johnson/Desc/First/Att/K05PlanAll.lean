-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PlanAll.lean: the facts on the plan that the statements on the kind K5
take and that no test of the verifier asks, as one test.

Definitions, statement and proof.
Main names:
  `planOkAll cf S fs`: `planOkLaw` cf S fs (Johnson/Desc/First/Att/Claims/PlanLaw.lean) and
    `unitsOk` S fs (Johnson/Desc/First/Att/K05UnitsOk.lean).
  `PlanAll`, `plan_all`: at a shape that `shapeHid` returns, a yes gives `PlanLaw` and the seven
    units with their `UnitIs`.
  `lookAll_of_plan`: `PlanAll` and `KeyPtsAre` (Johnson/Desc/First/Att/K05LookAll.lean) give the
    place's two score units, the first below the diagonal, the second on it, and `LookAll` at them.
Used: `planOkLaw`, `plan_law`, `unitsOk`, `units_all`, `lookAll_of_units`,
`callsFit_a01`; no routine in a context.
Limits: `planOkAll` reads of cf its list of lines alone: it does not tie cf to (S, fs); the premise
of `plan_all` that `shapeHid` lid cf has returned (S, fs) does: whoever asks the one has to ask the
other. That a running text asks either is not shown in this file or in what it imports. `planOkAll`
is evaluated in no file of this tree. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PlanLaw
import Johnson.Desc.First.Att.K05UnitsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

/-- **The one test on the plan.** -/
def planOkAll (cf : Attention.Cfg) (S : Attention.Shape) (fs : Model.Forest.Shape) : Bool :=
  K5Law.planOkLaw cf S fs && unitsOk S fs

/-- What a yes gives. -/
structure PlanAll (cf : Attention.Cfg) (S : Attention.Shape) (fs : Model.Forest.Shape) : Prop where
  law : K5Law.PlanLaw cf S fs
  units : ∃ r1 r2 u1 u2 wl ix wh, UnitsAll S fs r1 r2 u1 u2 wl ix wh

theorem plan_all {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape}
    (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (h : planOkAll cf S fs = true) : PlanAll cf S fs := by
  unfold planOkAll at h
  rw [Bool.and_eq_true] at h
  exact ⟨K5Law.plan_law hid h.1, units_all h.2⟩

/-- **LookAll from the one test and the lookup's kind's record.** -/
theorem lookAll_of_plan {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 X : Type}
    (P0 : Cb.Pv.Att.OwnPar K M0 X) {cf : Attention.Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape}
    (hD : P0.D = OnBytes.Road.L5.dimOf S) (hC : P0.C = OnBytes.Road.L5.callsOf fs) (A : PlanAll cf S fs)
    (zk : Array (Array E)) (x0 : X) (Kp : KeyPtsAre ρ P0.C (P0.zOf x0) zk) :
    ∃ u1 u2, (geoOf S).scores = [u1, u2] ∧ u1.below = true ∧ u2.below = false ∧
      LookAll P0 S zk u1 u2 ρ x0 := by
  obtain ⟨r1, r2, u1, u2, wl, ix, wh, U⟩ := A.units
  exact ⟨u1, u2, U.sco, U.below, U.on,
    lookAll_of_units P0 hD hC (OnBytes.Road.L5.callsFit_a01 A.law.fit) U zk x0 Kp⟩

end VerifiableInference.Desc.First.Att.P
