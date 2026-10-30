-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LamRoomOfFit.lean: CONDITIONAL.

What is here. The plan of the hashed rounds has room for the coordinates of both gated products:
D.lL + lF D ≤ lamS and lFe D ≤ lamS (`lam_room_of_fit`), wherever the honest side's function for the
batched sumcheck returns a job of its call's shape, at any input, sampled values and shown values,
and that call states at least one end value. So the sizes that Law/W/FitGated.lean asks of the
batched sumcheck's challenges follow from the stack's clause of the public test k4MakersFit
(Law/W/FitStack.lean, FitStackPub.lean). By `lam_room` (Johnson/Road/K4/C/LamRoom.lean), whose two
returns are drawn out of the clause by Law/StackCube.lean's stack_ends_some; the second inequality
by lF D = lFe D + 1 (Johnson/Road/K4/C/GatedNums.lean).

  `lam_room_of_fit`   the two inequalities.

Not shown here. K4Plan (ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES);
that the function returns (hj); that the job has the shape (hf); that the call states an end value
(hn): hypotheses. THIS IS STILL THE ROAD FROM A RUN: a fact on the plan is drawn from a return of
the honest side's function; a road from the plan's own numbers is open. Nothing on soundness, on
completeness or on any other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackCube
import Johnson.Road.K4.C.LamRoom
import Johnson.Road.K4.C.GatedNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (lam_room gatedNums_of_plan sides_fields stack_open)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim lF lFe)

/-- **THE PLAN OF THE HASHED ROUNDS HAS ROOM FOR BOTH GATED PRODUCTS' COORDINATES.** CONDITIONAL: on
every hypothesis named. -/
theorem lam_room_of_fit {Q : K4Pub} {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)}
    {tl : HTailF2} {D : Dim} (A : K4Plan hS pc Q.P Q.g tl D) {w : K4In} {p : Pts}
    {shownT : Array E} {j : Job} {n : ℕ} (hj : jobStack Q w p shownT = some j)
    (hf : k4JobFits (k4PlainShape Q.hp.lamS 2 n) j = true) (hn : 0 < n) :
    D.lL + lF D ≤ Q.hp.lamS ∧ lFe D ≤ Q.hp.lamS := by
  have N := gatedNums_of_plan A
  unfold jobStack at hj
  obtain ⟨SD, hSD, rfl⟩ := Option.map_eq_some_iff.mp hj
  have hQ : SD.S.Q = Q := (sides_fields (stack_open hSD).1).1
  rw [← hQ] at hf
  obtain ⟨l, he, _⟩ := stack_ends_some hf hn (List.replicate SD.S.Q.hp.lamS zeroE)
    (by rw [List.length_replicate]; rfl)
  have h1 := lam_room hSD he N
  have h2 := N.ffe
  exact ⟨h1, by omega⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.lam_room_of_fit
