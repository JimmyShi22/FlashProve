-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/LayoutCaps.lean: bounds on the numbers of a layer sub-proof's shape, and four
numbers of its layout, from the layout routine's yes.

"Layer.layout" (OnBytes/Model/LayerLayout.lean) tests the shape h and derives the layout y. This
file walks its first half once: it keeps the tests as far as the one on the heads, passes the others
by, and says what the kept tests and the last record give.

Main names.
 - LayoutCaps h y: 4 ≤ lt ≤ 16; 1 ≤ ll ≤ 6; d and f at most 2 ^ 20; lt < la ≤ 16;
   H + Gk ≤ 64; and y.h = h, y.ls = la - lt, y.lPd = ceilLog2 d, y.NI = 2 * 2 ^ ll.
 - layoutBase_caps, layoutLook_keeps, layout_caps: from the two halves of the routine, and from the
   whole.
 - **polLayout_caps**: Verify.polLayout pol = .ok (P, y) gives LayoutCaps (Verify.layerShape P) y.

Limits. Only the tests named above are drawn; the routine makes many more. Nothing on the other
fields of the layout. The program does not import this file.


-/
import OnBytes.Tie.Pv.Lookup.Ends.BatRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Fit

open Fo.BatRows (bindE_ok)

/-- A refusal that did not happen. -/
theorem not_refused {b : Bool} {name : String} {u : Unit} (h : refuseIf b name = .ok u) :
    b = false := by
  unfold refuseIf at h
  cases b with
  | false => rfl
  | true => cases h

/-- Bounds on the shape's numbers, and four numbers of the layout. -/
structure LayoutCaps (h : Layer.Shape) (y : Layer.Lay) : Prop where
  lt4 : 4 ≤ h.lt
  lt : h.lt ≤ 16
  ll1 : 1 ≤ h.ll
  ll : h.ll ≤ 6
  d : h.d ≤ 2 ^ 20
  f : h.f ≤ 2 ^ 20
  laLt : h.lt < h.la
  la : h.la ≤ 16
  heads : h.H + h.Gk ≤ 64
  yh : y.h = h
  ls : y.ls = h.la - h.lt
  lPd : y.lPd = ceilLog2 h.d
  NI : y.NI = 2 * 2 ^ h.ll

/-- The first half of the layout. -/
theorem layoutBase_caps {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layoutBase h pc = .ok y) : LayoutCaps h y := by
  unfold Layer.layoutBase at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, e2, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, e6, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, e9, e⟩ := bindE_ok e
  have b2 := not_refused e2
  have b6 := not_refused e6
  have b9 := not_refused e9
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at b2 b6 b9
  have hy : y.h = h ∧ y.ls = h.la - h.lt ∧ y.lPd = ceilLog2 h.d ∧ y.NI = 2 * 2 ^ h.ll := by
    repeat' first
      | (obtain ⟨_, _, e⟩ := bindE_ok e)
      | (split at e)
    all_goals (cases e; exact ⟨rfl, rfl, rfl, rfl⟩)
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    hy.1, hy.2.1, hy.2.2.1, hy.2.2.2⟩

/-- The second half keeps the four numbers. -/
theorem layoutLook_keeps {y0 y : Layer.Lay} (e : Layer.layoutLook y0 = .ok y) :
    y.h = y0.h ∧ y.ls = y0.ls ∧ y.lPd = y0.lPd ∧ y.NI = y0.NI := by
  unfold Layer.layoutLook at e
  dsimp only at e
  repeat' first
    | (obtain ⟨_, _, e⟩ := bindE_ok e)
    | (split at e)
  all_goals (cases e; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- The whole layout. -/
theorem layout_caps {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layout h pc = .ok y) : LayoutCaps h y := by
  unfold Layer.layout at e
  obtain ⟨y0, e0, e⟩ := bindE_ok e
  have C := layoutBase_caps e0
  obtain ⟨k1, k2, k3, k4⟩ := layoutLook_keeps e
  exact ⟨C.lt4, C.lt, C.ll1, C.ll, C.d, C.f, C.laLt, C.la, C.heads, k1.trans C.yh, k2.trans C.ls,
    k3.trans C.lPd, k4.trans C.NI⟩

/-- **The scan and the layout.** -/
theorem polLayout_caps {pol : ByteArray} {P : PolScan} {y : Layer.Lay}
    (e : Verify.polLayout pol = .ok (P, y)) : LayoutCaps (Verify.layerShape P) y := by
  unfold Verify.polLayout at e
  obtain ⟨P0, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨y0, hy, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact layout_caps hy

end OnBytes.Model.Fit

#print axioms OnBytes.Model.Fit.layoutBase_caps
#print axioms OnBytes.Model.Fit.layoutLook_keeps
#print axioms OnBytes.Model.Fit.layout_caps
#print axioms OnBytes.Model.Fit.polLayout_caps
