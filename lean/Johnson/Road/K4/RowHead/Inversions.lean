-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowHead/Inversions.lean: WHERE THE LAYERS' LAYOUT RETURNS, ITS TWINS WITHOUT THE
STOPPING LINES (Johnson/Road/K4/RowHead/Twins.lean) RETURN THE SAME: general in the shape and the
calls' lines; nothing is evaluated; no range is asked: a routine that has returned has passed its
own tests. Statements with their proofs.

  `base_inv`: layoutBase h pc = .ok y ⟹ baseNoStops h pc = .ok y.
  `shape_inv`: Forest.shape calls lid = .ok fo ⟹ Forest.shapeNoAsk calls lid = .ok fo.
  `look_inv`: layoutLook y0 = .ok y ⟹ ∃ fo pub kbm, Forest.shapeNoAsk ‹the calls' records› y0.h.lidb
    = .ok fo ∧ Forest.planeCols fo y0.h.lmb = .ok kbm ∧ y = { y0 with cl := ‹the records›, fo := {
    fo with pub := pub }, kbm := kbm }.
  **`layout_inv`**: Layer.layout h pc = .ok y ⟹ ∃ y0 fo pub kbm, the three at once.

Limits. ONE DIRECTION, FROM A RETURN. Nothing on soundness.
-/
import Johnson.Road.K4.RowHead.Twins
import Johnson.Road.FormsKeysLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road (ok_of_bind ok_of_refuse)

/-- layoutBase is its twin where the three stopping lines pass. -/
theorem base_eq_noStops (h : Layer.Shape) (pc : List (List String))
    (h0 : ([h.eps1, h.eps2].any fun e => decide (e < 1) || decide (e ≥ 2 ^ 59)) = false)
    (h1 : tensorsFill [("x", (⟨0, h.xl, 1, h.d⟩ : TenAt))] (h.xl * h.d) (2 ^ (h.la - h.lt))
      "stream" = .ok ())
    (h2 : tensorsFill (((layTensors (tensorAsks h (2 ^ h.ll) (2 ^ h.ll / 2)
        (h.H * h.dh + h.Gk * h.dh) (h.H * h.dh) (h.Gk * h.dh)) #[0, 0, 0, 0]).1.filter
          fun t => t.mat == 3).map fun t => (t.name, t.place))
      ((layTensors (tensorAsks h (2 ^ h.ll) (2 ^ h.ll / 2) (h.H * h.dh + h.Gk * h.dh)
        (h.H * h.dh) (h.Gk * h.dh)) #[0, 0, 0, 0]).2.getD 3 0) (2 ^ (h.la - h.lt)) "qa" = .ok ()) :
    layoutBase h pc = baseNoStops h pc := by
  unfold layoutBase baseNoStops
  simp only [h0, h1, h2]
  rfl

/-- **Where the first half returns, its twin returns the same.** -/
theorem base_inv {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (hy : layoutBase h pc = .ok y) : baseNoStops h pc = .ok y := by
  have hy0 := hy
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e0, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨u1, f1, hy⟩ := ok_of_bind hy
  obtain ⟨u2, f2, -⟩ := ok_of_bind hy
  exact (base_eq_noStops h pc e0 f1 f2).symm.trans hy0

/-- **Where the forest's numbers are made, they are made without the tests on the calls.** -/
theorem shape_inv {calls : Array Call} {lid : ℕ} {fo : Forest.Shape}
    (h : Forest.shape calls lid = .ok fo) : Forest.shapeNoAsk calls lid = .ok fo := by
  unfold Forest.shape at h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  exact h

/-- **Where the second half returns.** -/
theorem look_inv {y0 y : Layer.Lay} (hy : layoutLook y0 = .ok y) :
    ∃ (fo : Forest.Shape) (pub : Array ℕ) (kbm : ℕ),
      Forest.shapeNoAsk (y0.calls.mapIdx fun q cd => y0.callRecord q cd) y0.h.lidb = .ok fo ∧
      Forest.planeCols fo y0.h.lmb = .ok kbm ∧
      y = { y0 with cl := y0.calls.mapIdx fun q cd => y0.callRecord q cd,
                    fo := { fo with pub := pub }, kbm := kbm } := by
  unfold layoutLook at hy
  obtain ⟨_, -, hy⟩ := ok_of_bind hy
  obtain ⟨fo, hfo, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨kbm, hk, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  cases hy
  exact ⟨fo, pub, kbm, shape_inv hfo, hk, rfl⟩

/-- **Where the layers' layout returns: the three at once.** -/
theorem layout_inv {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (hy : Layer.layout h pc = .ok y) :
    ∃ (y0 : Layer.Lay) (fo : Forest.Shape) (pub : Array ℕ) (kbm : ℕ),
      baseNoStops h pc = .ok y0 ∧
      Forest.shapeNoAsk (y0.calls.mapIdx fun q cd => y0.callRecord q cd) y0.h.lidb = .ok fo ∧
      Forest.planeCols fo y0.h.lmb = .ok kbm ∧
      y = { y0 with cl := y0.calls.mapIdx fun q cd => y0.callRecord q cd,
                    fo := { fo with pub := pub }, kbm := kbm } := by
  unfold Layer.layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  obtain ⟨fo, pub, kbm, a, b, c⟩ := look_inv h1
  exact ⟨y0, fo, pub, kbm, base_inv h0, a, b, c⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.base_eq_noStops
#print axioms OnBytes.Road.K4.base_inv
#print axioms OnBytes.Road.K4.shape_inv
#print axioms OnBytes.Road.K4.look_inv
#print axioms OnBytes.Road.K4.layout_inv
