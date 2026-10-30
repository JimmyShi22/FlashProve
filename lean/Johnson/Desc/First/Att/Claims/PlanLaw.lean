-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PlanLaw.lean: kind K5: the plan facts that the laws on the kind's
claims take and that no test of the verifier asks, as one Boolean on the configuration, the shape
and the lookup's shape.

Main names:
  `posOk g`, `posG_of_ok`: six numbers of the place are positive: PosG
    (Johnson/Desc/First/Att/Claims/TablesSpec.lean).
  `planOkLaw cf S fs`: usualB cf (Johnson/Road/Lane5AttLaid.lean), CallsFit S fs
    (Johnson/Road/Lane5CallsOf.lean), numsB S (Johnson/Road/Lane5KvCheck.lean) and posOk (geoOf S),
    all at once.
  `PlanLaw cf S fs`, `plan_law`: what a yes gives at a shape that shapeHid returns: UsualCalls,
    CallsFit, NumsA, PosG, and with them PlaceIs (place_of_hid,
    Johnson/Desc/First/Att/Claims/PlaceOf.lean) and KeyNums (keyNums_of_hid,
    Johnson/Desc/First/Att/Claims/KeyNumsOf.lean).
Limits: UsualCalls is no test of the verifier (Johnson/Road/Lane5AttLaid.lean says so of itself):
the verifier takes other call lists, and groups with two shifts; at another list this file says
nothing. No test of the verifier asks planOkLaw: at a plan where it says no, the laws that take its
facts say nothing. That it says yes at a plan is an evaluation's word; no file of this tree
evaluates it. The tests unitOk on the seven units (Johnson/Desc/First/Att/K05LookAll.lean), which
the law on the hearing takes, are not in it: that file stands above this one.
Used of OnBytes and Johnson/Road: plain records; usualB, usual_of_test, CallsFit and its instance of
Decidable, numsB, numsA_of_numsB, callAt.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5KvCheck
import Johnson.Desc.First.Att.Claims.KeyNumsOf
import Johnson.Desc.First.Att.Claims.TablesSpec

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road
open OnBytes.Road.L5 (callAt)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo geoOf)

/-- Six numbers of the place are positive. -/
def posOk (g : Geo) : Bool :=
  decide (0 < g.NAs) && decide (0 < g.kAs / g.NAs) && decide (0 < g.fillH) &&
    decide (0 < g.fillO * g.T / 2 ^ g.la) && decide (0 < g.fillQ * g.T / 2 ^ g.la) && decide (0 < g.kbA)

theorem posG_of_ok {g : Geo} (h : posOk g = true) : PosG g := by
  simp only [posOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **The plan facts that the laws on the kind's claims take and that no test of the verifier asks.** -/
def planOkLaw (cf : Attention.Cfg) (S : Attention.Shape) (fs : Model.Forest.Shape) : Bool :=
  L5.usualB cf && decide (L5.CallsFit S fs) && L5.numsB S && posOk (geoOf S)

/-- What a yes gives, at a shape that shapeHid returns. -/
structure PlanLaw (cf : Attention.Cfg) (S : Attention.Shape) (fs : Model.Forest.Shape) : Prop where
  usual : L5.UsualCalls cf
  fit : L5.CallsFit S fs
  nums : L5.NumsA S
  pos : PosG (geoOf S)
  place : PlaceIs S (callAt S 0) (callAt S 1) (callAt S 2) (callAt S 3)
  key : KeyNums S (callAt S 1)

theorem plan_law {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape}
    (hid : shapeHid lid cf = Except.ok (S, fs)) (h : planOkLaw cf S fs = true) : PlanLaw cf S fs := by
  simp only [planOkLaw, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have U := L5.usual_of_test h1
  have NA := L5.numsA_of_numsB h3
  exact ⟨U, h2, NA, posG_of_ok h4, place_of_hid hid U, keyNums_of_hid hid U h2 NA⟩

end K5Law
