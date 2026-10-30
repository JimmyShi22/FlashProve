-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MemberK.lean: THE RECORD `Plan4L.ValueIs` (Johnson/Road/K4/CloseSevenK.lean) HOLDS
OF THE VALUE AT THE REFERENCE SIZES (`refL`, Johnson/Road/K4/RefValue.lean) AT THE RECORD's OWN nT
AND nI, WHEREVER THE TEST `recordB` SAYS TRUE, IN A GROUP THAT IS NOT THE FIRST, at the record that
the verifier's own `publicOf` returns. One statement: `ref_nine`, laid into the record.

What is a theorem, what a run and what a premise: the head of RefValue.lean.
-/
import Johnson.Road.K4.RefValue
import Johnson.Road.K4.CloseSevenK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (nEndT)
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Road.Alg (recordB)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers Par)

variable {M Xs : Type} {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {p : Par}
  {tk : Array Nat}

/-- **`ValueIs` holds of the value at the record's own two numbers of end values**, under the
premises of `ref_nine` (among them: the test `recordB` says true; the group is not the first; K4's
text covers the record; the section's table of scales is `sclX X p.g`). -/
theorem ref_valueIs [scl : Scl] (hscl : scl = sclX X p.g) (R : RefLetters M Xs) (hg : p.g < 12)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hc : covers X.layers = true) :
    Plan4L.ValueIs (refL R p.g hg (nEndT X.layers.y)
        (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0))))
      p (layerShape X.P) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ref_nine hscl R hg h t hP hG hg0 hc rfl
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ref_valueIs
