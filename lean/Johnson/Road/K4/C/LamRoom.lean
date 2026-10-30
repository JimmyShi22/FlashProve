-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/LamRoom.lean: CONDITIONAL.

What is here. The plan of the hashed rounds has room for the first gated product's coordinates: D.lL
+ lF D ≤ Q.hp.lamS, wherever the honest side's data of the batched sumcheck are made and their end
values are there. K4Plan does not read that plan; the test of that function on the placed panels
does: these coordinates are the bits of the down product's panel, which has D.lL + lF D of them
(`down_nums`, C/DownPanel.lean) and lies below 2 ^ lamS (`stack_panelsFit`, C/PanelsFitOf.lean).

  `lam_room`   D.lL + lF D ≤ Q.hp.lamS.

Not shown here. THAT THE FUNCTION WHICH MAKES THE BATCHED SUMCHECK's DATA RETURNS AND THAT ITS END
VALUES ARE THERE: hypotheses (Johnson/Desc/ProofFile/Honest/K4/Law/W/MakersReturn.lean has both at a
state behind the member's step, from the public test k4Fits); GatedNums: from K4Plan
(C/GatedNums.lean). THIS IS THE ROAD FROM A RUN: a fact on the plan is drawn from two returns of the
honest side's functions; a road from the plan alone is open. That they hold together: beside trials
at a small synthetic plan no example is known. Nothing on soundness, on completeness or on any other
property. No property is claimed.
-/
import Johnson.Road.K4.C.StackTrue
import Johnson.Road.K4.C.StackSidesOf
import Johnson.Road.K4.C.DownPanel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open Inst.Model.FFSeg (Dim lF)
open OnBytes.Desc.First.K4.Honest

/-- **The batched sumcheck has room for the first gated product's coordinates.** CONDITIONAL: on
the two returns and N. -/
theorem lam_room {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {SD : StackData} {D : Dim}
    (h : stackData Q w p shownT = some SD) {rs : Array E} {l : List E}
    (he : SD.endsAt rs = some l) (N : GatedNums Q D) : D.lL + lF D ≤ Q.hp.lamS := by
  obtain ⟨_, _, _, dn, _, _, _, hdn, _⟩ := endsAt_all he
  obtain ⟨_, hw, _, _⟩ := down_nums h N dn hdn
  have hQ : SD.S.Q = Q := (sides_fields (stack_open h).1).1
  have top := ((stack_panelsFit h).each dn
    (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hdn))).top
  rw [hw, hQ] at top
  exact (Nat.pow_le_pow_iff_right (by decide)).mp (Nat.le_trans (Nat.le_add_left _ _) top)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.lam_room
