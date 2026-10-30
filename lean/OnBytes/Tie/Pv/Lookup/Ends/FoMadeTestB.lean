-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoMadeTestB.lean: the test Fo.shapesB
(OnBytes/Tie/Pv/Lookup/Ends/FoShapesBDefs.lean) says yes at every record that
Verify.publicOf returns.

 - callEqB_refl, callsEqB_refl, shapeEqB_refl: the three tests of equality say yes at equal things.
 - test_of_made: Fo.Made gives madeB = true (the converse of made_of_test,
   OnBytes/Tie/Pv/Lookup/Ends/FoShapes.lean).
 - public_shapesB: Verify.publicOf pol KL layout = .ok X gives shapesB X = true.
So a premise "shapesB X = true at what publicOf makes of the call's own files" asks nothing.

Not claimed: that publicOf returns; anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model

theorem callEqB_refl (a : Call) : callEqB a a = true := by
  simp [callEqB]

theorem callsEqB_refl (a : Array Call) : callsEqB a a = true := by
  simp [callsEqB, callEqB_refl]

theorem shapeEqB_refl (a : Forest.Shape) : shapeEqB a a = true := by
  simp [shapeEqB, callsEqB_refl]

/-- The test says yes where the record is made so. -/
theorem test_of_made {calls : Array Call} {lid : ℕ} {fs : Forest.Shape}
    (h : Made calls lid fs) : madeB calls lid fs = true := by
  obtain ⟨h0, e0, e1⟩ := h
  unfold madeB
  rw [e0]
  show shapeEqB fs { h0 with pub := fs.pub } = true
  rw [← e1]
  exact shapeEqB_refl fs

/-- **The test shapesB says yes at every record that publicOf returns.** -/
theorem public_shapesB {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : shapesB X = true := by
  obtain ⟨mG, mGz, mA, mH, mHz⟩ := Pub.public_made h
  unfold shapesB shapeParts
  rw [List.all_eq_true]
  intro p hp
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (((rfl | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | rfl | rfl
  · exact test_of_made mG
  · exact test_of_made (mGz x.2 x.1 (by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simpa using this))
  · exact test_of_made (mA x.2 x.1 (by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simpa using this)).1
  · exact test_of_made (mA x.2 x.1 (by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simpa using this)).2
  · exact test_of_made mH
  · exact test_of_made mHz

end Fo
