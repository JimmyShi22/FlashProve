-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/KeptGround.lean: CONDITIONAL.

Not shown here. THAT A DECISION ACCEPTS ANYWHERE: KeptAtS is a hypothesis; no example is known.
Where K4Plan holds: the head of W/GroundOfHear.lean. Nothing on soundness, on completeness or on any
other property. No property is claimed.

The public facts on the layout (`K4Ground`, W/Ground.lean) at what the hearing left, behind an
accepting decision of the layers' own rounds (sub-protocol K4): by `ground_of_hear`
(W/GroundOfHear.lean), as `kept_env` (W/KeptEnv.lean) has the group and the layout.

  `kept_ground`   there are laid tables r and named points pts with K4Ground at the state's own o.
-/
import Johnson.Road.K4.W.KeptEnv

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

/-- **K4Ground behind an accepting decision.** CONDITIONAL: on K, A and ho. -/
theorem kept_ground {p : Par} {s s' : S} (K : KeptAtS p s s') {h : Layer.Shape}
    {pc : List (List String)} {tl : HTailF2} {D : Dim} (A : K4Plan h pc p.P p.g tl D) {o : Own}
    (ho : seatS.own s' = some o) :
    ∃ r pts, K4Ground h pc o.v p.P.rd r tl o.H o.hd o.hd2 pts o.funs D := by
  obtain ⟨a, a', fo, o', G, t, u, _, _, ha', _, eo, _, _, hh⟩ := kept_open K
  have hown : seatS.own s' = some o' := by
    show (match s'.here with | .lay a => a.own | _ => none) = _
    rw [ha']
    exact eo
  obtain rfl : o' = o := Option.some.inj (hown.symm.trans ho)
  obtain ⟨_, _, r, pts, G'⟩ := ground_of_hear hh (plan_tokens A s.tokv)
  exact ⟨r, pts, G'⟩

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.kept_ground
