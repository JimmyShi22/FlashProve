-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MemberPlanes.lean: TWO PUBLIC LINES ON THE PLANES' MATRIX b OF A GROUP OF LAYERS, AT
THE RECORD THAT THE VERIFIER's OWN `publicOf` RETURNS, in the letters of a place of K4's block. One
statement: `Fo.PlaneMatG.public_planeMatB`
(OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean), whose test `Fo.planeMatB`
(OnBytes/Tie/Pv/Lookup/Ends/FoLookLayerReads.lean) holds both lines, written out.

  `planes_pub`: where the place holds the record's layers and the group's plan: of the matrix number
    iB of the plan's list: its number of rows, divided by 2 ^ lmb and rounded down, is 1; and it has
    at least as many columns as the planes have (`Fo.planeCols` of the plan's shape of the lookup).

A theorem from `publicOf`'s return alone: no test, no run, no sizes, whichever group. Premises that
stay: the place holds the record's layers (hP) and the group's plan (hG). Limits. It speaks at THE
PLAN's shape of the lookup, p.P.y.fo; a caller who needs the two lines at the shape that a hearing
HEARD owes the tie of the two shapes: no statement here gives it.
-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG
import Johnson.Desc.First.K4.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (matIx)
open OnBytes.Model.Verify (Public publicOf)
open OnBytes.Desc.First.K4 (Par)

/-- **The planes' matrix: its rows over 2 ^ lmb, rounded down, are 1, and it has columns enough**,
at `publicOf`'s own record, where the place holds the record's layers and the group's plan. -/
theorem planes_pub {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {p : Par}
    {tk : Array Nat} (h : publicOf pol KL lay = .ok X) (hP : p.P = { X.layers with tokv := tk })
    (hG : X.G[p.g]? = some p.hp) :
    (p.hp.tl.mats.getD (matIx p.P.y).iB {}).m / 2 ^ p.P.y.h.lmb = 1 ∧
      _root_.Fo.planeCols p.P.y.fo p.P.y.h.lmb ≤ (p.hp.tl.mats.getD (matIx p.P.y).iB {}).k := by
  have b := _root_.Fo.PlaneMatG.public_planeMatB h p.g p.hp hG
  simp only [_root_.Fo.planeMatB, Bool.and_eq_true, decide_eq_true_eq] at b
  rw [hP]
  exact ⟨b.1.2, b.2⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.planes_pub
