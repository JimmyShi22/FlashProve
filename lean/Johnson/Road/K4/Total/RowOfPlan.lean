-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/RowOfPlan.lean: BEHIND A YES OF K4's BLOCK THE PUBLIC TEST hasRow
(Johnson/Top/H0/Walk/FrameRow.lean: the frame's reader of the pending row returns), AT THE PLAN's
OWN LAYOUT AND NUMBER OF CLAIMS, SAYS YES, UNDER THAT YES AND TWO TESTS WITH CODE: rowB, on the plan
(Johnson/Road/K4/Total/PlanRowDefs.lean), and roomFor, on the state in front
(Johnson/Road/K4/Total/RoomFor.lean). Statements and proofs: a join.

  `rowSkel_refl`: a leaving has its own skeleton.
  **`hasRow_of_plan`**: KeptAtS p s s' (had at a yes: kept_atS) · rowB p.P p.g p.hp.NCL lin · room
    for n entries at s, n at least 1: then hasRow p.P.wsLay p.hp.NCL lin s'.
No new argument: row_returns_of_plan, hasRow_core, roomB_of_roomFor.
**Limits.** rowB AND roomFor ARE PREMISES: neither is said to be true anywhere; NO RUN OF EITHER IS
CITED HERE. The letters of hasRow are filled with p.P.wsLay and p.hp.NCL; lin is free: that these
are the letters at which a table of public items asks the test is not said. It says that the reader
returns, not what the row says. Nothing on soundness. K04_law, the law of K4's block itself, IS NOT
PROVED. Met through Lean at no member.


-/
import Johnson.Road.K4.Total.RowAtKept
import Johnson.Road.K4.Total.PlanRow
import Johnson.Road.K4.Total.RoomFor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Params (LinShape)
open OnBytes.Flat (All2)
open OnBytes.Road.K4 (KeptAtS)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Law (hasRow)

/-- A leaving has its own skeleton. -/
theorem rowSkel_refl (w : WsForkOut) : RowSkel w w :=
  ⟨rfl, All2.refl (fun _ => ⟨rfl, All2.refl (fun _ => ⟨rfl, rfl, rfl⟩) _⟩) _⟩

/-- **Behind a yes of K4's block: two tests with code (room for n entries, n at least 1) give hasRow
at p.P.wsLay and p.hp.NCL.** -/
theorem hasRow_of_plan {p : Par} {s s' : S} {lin : LinShape} {n : Nat} (K : KeptAtS p s s')
    (hB : rowB p.P p.g p.hp.NCL lin = true) (hn : 1 ≤ n) (hroom : roomFor n s = true) :
    hasRow p.P.wsLay p.hp.NCL lin s' = true := by
  obtain ⟨a, fo, o, G, _, _, _, _, _, _, _, hleft, hR, _, _, t, u, hh⟩ := K
  have hw : (wsPending p.P.wsLay o.wo p.hp.NCL lin).toOption.isSome = true :=
    row_returns_of_plan hh (n := p.hp.NCL) (lin := lin) hB
  exact hasRow_core hleft hR (rowSkel_refl o.wo) hw (roomB_of_roomFor hn hroom)

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.rowSkel_refl
#print axioms OnBytes.Desc.First.K4.Total.hasRow_of_plan
