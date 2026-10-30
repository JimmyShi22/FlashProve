-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Fold.lean: SMALL GENERAL LAWS.

Not shown here. Nothing on any protocol: each law reads a loop of the program in the field. No
property is claimed.

Two loops that add a product at each step, and their steps (maddE, maddS: OnBytes/Field/Ext.lean),
read in the library's extension field by Reading.gl (OnBytes/Model/HideLaws.lean), as sums over
lists.

  gl_maddE, gl_maddS    one step.
  gl_foldl_maddE        a loop over a list that adds c x times d x.
  gl_foldl_maddS        the same with a word of the base field for one factor.
-/
import OnBytes.Model.HideLaws
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model

/-- One step, all three in the extension field. -/
theorem gl_maddE (a s x : E) :
    Reading.gl.val (maddE a s x) = Reading.gl.val a + Reading.gl.val s * Reading.gl.val x :=
  Slice.readE_maddE a s x

/-- One step with a word of the base field. -/
theorem gl_maddS (a : E) (s : F) (x : E) :
    Reading.gl.val (maddS a s x) =
      Reading.gl.val a + Reading.gl.val (ofF s) * Reading.gl.val x := by
  show Slice.readE (maddS a s x) = Slice.readE a + Slice.readE (ofF s) * Slice.readE x
  rw [Slice.readE_maddS, Slice.readE_ofF, Algebra.smul_def]

/-- A loop over a list that adds c x times d x. -/
theorem gl_foldl_maddE {α : Type} (c d : α → E) : ∀ (l : List α) (s : E),
    Reading.gl.val (l.foldl (fun s x => maddE s (c x) (d x)) s) =
      Reading.gl.val s + (l.map fun x => Reading.gl.val (c x) * Reading.gl.val (d x)).sum
  | [], s => by simp
  | x :: l, s => by
    rw [List.foldl_cons, gl_foldl_maddE c d l, gl_maddE, List.map_cons, List.sum_cons, add_assoc]

/-- The same with a word of the base field for one factor. -/
theorem gl_foldl_maddS {α : Type} (c : α → F) (d : α → E) : ∀ (l : List α) (s : E),
    Reading.gl.val (l.foldl (fun s x => maddS s (c x) (d x)) s) =
      Reading.gl.val s + (l.map fun x => Reading.gl.val (ofF (c x)) * Reading.gl.val (d x)).sum
  | [], s => by simp
  | x :: l, s => by
    rw [List.foldl_cons, gl_foldl_maddS c d l, gl_maddS, List.map_cons, List.sum_cons, add_assoc]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.gl_maddE
#print axioms OnBytes.Road.K4.C.gl_maddS
#print axioms OnBytes.Road.K4.C.gl_foldl_maddE
#print axioms OnBytes.Road.K4.C.gl_foldl_maddS
