-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ClaimsPaid.lean: THREE OF THE PREMISES OF Johnson/Road/K4/ClaimsHeard.lean, PAID:
the reading of the program's 1/2, and, from the record `Plan4.Meets`
(Johnson/Road/K4/PlanMaps.lean), the two premises on sizes, at the public record with whatever
tokens laid in. Three short statements.

  `gl_half`: the reading in the library's extension field takes the program's inverse of 2 to a
    number whose double is 1 (by `gl_inv`, `gl_numerals`, `gl_two_ne_zero`).
  `Plan4.Meets.dimIsT`: `DimIs Q.full.D (Verify.layerNumbers { p.P with tokv := tk } p.hp p.g)`: the
    program's record of sizes does not read the tokens.
  `Plan4.Meets.lamM`: the layout's number of layers with routed experts is the library's.

Limits. Equations between numbers and one between two elements of a field.
-/
import Johnson.Road.K4.PlanMaps
import Johnson.Road.Rows.LayerEnds34Ref
import Cb.Pv.Head.NormGl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Tie.Pv.Lay.At (DimIs)

/-- **The reading of the program's 1/2.** -/
theorem gl_half : Reading.gl.val (invE (ofNat 2)) * 2 = 1 := by
  rw [Rows.gl_inv, gl_numerals.ofNat, Nat.cast_ofNat]
  exact inv_mul_cancel₀ Cb.Pv.Head.gl_two_ne_zero

variable [scl : Scl] {M X : Type} {Q : Plan4 Cb.Gl.E M X} {p : Par} {hS : Layer.Shape}
  {pc : List (List String)}

/-- **The library's sizes are the program's own record's, with whatever tokens laid in.** -/
theorem Plan4.Meets.dimIsT (A : Q.Meets p hS pc) (tk : Array Nat) :
    DimIs Q.full.D (Verify.layerNumbers { p.P with tokv := tk } p.hp p.g) :=
  A.dimIs

/-- **The layers with routed experts.** -/
theorem Plan4.Meets.lamM (A : Q.Meets p hS pc) (tk : Array Nat) :
    ({ p.P with tokv := tk } : Layer.Pub).y.LamM = Q.full.D.ne :=
  (laySizes_of_layout A.hy).LamM.trans (ne_tie A.Z).symm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.gl_half
#print axioms OnBytes.Road.K4.Plan4.Meets.dimIsT
#print axioms OnBytes.Road.K4.Plan4.Meets.lamM
