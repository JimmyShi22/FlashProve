-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/KeptEnv.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE. Where K4Plan holds: the head of
W/GroundOfHear.lean. Nothing on soundness, on completeness or on any other property.
No property is claimed.

Behind an accepting decision of the layers' own rounds (sub-protocol K4): the group and the layout
in what was heard are the plan's.

  `kept_env`   o.v.g = p.g and o.v.y = p.P.y, from KeptAtS, K4Plan and "the seat holds o".
-/
import Johnson.Road.K4.W.ItemOfKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Own)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.K4.InT (kept_open)
open VerifiableInference.Desc.First (S)

/-- **The group and the layout behind an accepting decision.** CONDITIONAL: on K, A and ho. -/
theorem kept_env {p : Par} {s s' : S} (K : KeptAtS p s s') {h : Layer.Shape}
    {pc : List (List String)} {tl : HTailF2} {D : Dim} (A : K4Plan h pc p.P p.g tl D) {o : Own}
    (ho : seatS.own s' = some o) : o.v.g = p.g ∧ o.v.y = p.P.y := by
  obtain ⟨a, a', fo, o', G, t, u, _, _, ha', _, eo, _, _, hh⟩ := kept_open K
  have hown : seatS.own s' = some o' := by
    show (match s'.here with | .lay a => a.own | _ => none) = _
    rw [ha']
    exact eo
  obtain rfl : o' = o := Option.some.inj (hown.symm.trans ho)
  obtain ⟨vg, vy, _⟩ := ground_of_hear hh (plan_tokens A s.tokv)
  exact ⟨vg, vy⟩

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.kept_env
