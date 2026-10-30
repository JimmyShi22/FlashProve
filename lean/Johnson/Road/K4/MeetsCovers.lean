-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/MeetsCovers.lean: WHAT `Plan4.Meets` (Johnson/Road/K4/PlanMaps.lean) ALREADY SAYS OF
THE SHAPE: routed experts and five limbs, by the text's own test `covers`
(OnBytes/Desc/First/K4/Rounds.lean); so the record `SevenSizes` follows from `Meets` and the own
fields of the value with its slots and orders laid (`Plan4L`: h5, h6). Four short statements.

  `covers_shape`: where K4's text covers a public record: its shape has five limbs, routed experts
    and more than one bit of layers.
  `Plan4.Meets.p3`, `Plan4.Meets.xl`: so of the shape hS of `Meets`, which the layout holds.
  `sevenSizes_of_meets`: `sevenSizes_K` (Johnson/Road/K4/SevenPaid.lean) without its two premises on
    the shape.

Limits. Facts on numbers and two switches. That `Meets` holds at a run's place is a premise.

-/
import Johnson.Road.K4.SevenPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (covers Par)

/-- What the text's test says of the shape. -/
theorem covers_shape {P : Layer.Pub} (hc : covers P = true) :
    P.y.h.xl = 5 ∧ P.y.h.p3 = true ∧ 1 < P.y.h.ll := by
  unfold covers at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, p3⟩, c3⟩, -⟩, -⟩ := hc
  exact ⟨beq_iff_eq.mp c1, p3, by simpa using c3⟩

variable [scl : Scl] {M X : Type}

/-- The shape has routed experts. -/
theorem Plan4.Meets.p3 {Q : Plan4 Cb.Gl.E M X} {p : Par} {hS : Layer.Shape}
    {pc : List (List String)} (A : Q.Meets p hS pc) : hS.p3 = true := by
  rw [← (laySizes_of_layout A.hy).shape]
  exact (covers_shape A.hc).2.1

/-- The shape has five limbs. -/
theorem Plan4.Meets.xl {Q : Plan4 Cb.Gl.E M X} {p : Par} {hS : Layer.Shape}
    {pc : List (List String)} (A : Q.Meets p hS pc) : hS.xl = 5 := by
  rw [← (laySizes_of_layout A.hy).shape]
  exact (covers_shape A.hc).1

/-- **The forty-one sizes, from `Meets`** and the own fields h5, h6 of the value with its slots and
orders laid. -/
theorem sevenSizes_of_meets {QL : Plan4L Cb.Gl.E M X} {par : Par} {hS : Layer.Shape}
    {pcl : List (List String)} (A : QL.plan.Meets par hS pcl) (tk : Array Nat) :
    SevenSizes QL.plan.full { par.P with tokv := tk } par.hp (par.P.y.lPd - par.P.y.ls)
      (hS.d / par.P.y.S2) par.P.y.ls :=
  sevenSizes_K A A.p3 A.xl tk

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.covers_shape
#print axioms OnBytes.Road.K4.Plan4.Meets.p3
#print axioms OnBytes.Road.K4.Plan4.Meets.xl
#print axioms OnBytes.Road.K4.sevenSizes_of_meets
