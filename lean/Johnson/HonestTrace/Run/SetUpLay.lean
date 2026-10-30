-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpLay.lean

The layers' layout under other values of three free numbers. Theorems alone; no definition.

Main theorems (on OnBytes/Model/LayerLayout.lean):
* "layout_eps": where "Layer.layout h pc" returns y, it also returns at the shape h with eps1,
  eps2, epsF set to e1, e2, eF, and returns y with these three set in its shape. Asked:
  1 ≤ e1 < 2^59 and 1 ≤ e2 < 2^59. Nothing is asked of eF.
* "layoutBase_eps", "layoutLook_eps": the like of the two halves of "Layer.layout"; the two bounds
  are asked by the first alone, the second asks nothing of e1, e2, eF.

Limits. Conditional: no shape at which "Layer.layout" returns is shown here. The file has one
"local macro", "step": a tactic alone.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.LPFPol.PublicAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open LPFPol (bind_ok refuseIf_no)

local macro "step " k:ident : tactic =>
  `(tactic| (obtain ⟨a, ha, $k:ident⟩ := exc_bind $k
             refine (bind_ok ha).trans ?_
             clear ha
             try dsimp only at $k:ident
             try dsimp only))

theorem layoutBase_eps {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (hy : Layer.layoutBase h pc = .ok y) {e1 e2 eF : Nat}
    (h1 : 1 ≤ e1 ∧ e1 < 2 ^ 59) (h2 : 1 ≤ e2 ∧ e2 < 2 ^ 59) :
    Layer.layoutBase { h with eps1 := e1, eps2 := e2, epsF := eF } pc =
      .ok { y with h := { y.h with eps1 := e1, eps2 := e2, epsF := eF } } := by
  unfold Layer.layoutBase at hy ⊢
  dsimp only at hy ⊢
  iterate 7 step hy
  obtain ⟨_, _, hy⟩ := exc_bind hy
  refine (bind_ok (a := ()) (refuseIf_no ?_)).trans ?_
  · have q1 : (decide (e1 < 1) || decide (e1 ≥ 2 ^ 59)) = false := by
      rw [decide_eq_false (by omega), decide_eq_false (by omega)]
      rfl
    have q2 : (decide (e2 < 1) || decide (e2 ≥ 2 ^ 59)) = false := by
      rw [decide_eq_false (by omega), decide_eq_false (by omega)]
      rfl
    show ([e1, e2].any fun e => decide (e < 1) || decide (e ≥ 2 ^ 59)) = false
    simp only [List.any_cons, List.any_nil, q1, q2, Bool.or_false]
  try dsimp only at hy
  try dsimp only
  repeat step hy
  obtain rfl := Except.ok.inj hy
  rfl

theorem layoutLook_eps {y y1 : Layer.Lay} (hy : Layer.layoutLook y = .ok y1) (e1 e2 eF : Nat) :
    Layer.layoutLook { y with h := { y.h with eps1 := e1, eps2 := e2, epsF := eF } } =
      .ok { y1 with h := { y1.h with eps1 := e1, eps2 := e2, epsF := eF } } := by
  unfold Layer.layoutLook at hy ⊢
  dsimp only at hy ⊢
  repeat step hy
  obtain rfl := Except.ok.inj hy
  rfl

theorem layout_eps {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (hy : Layer.layout h pc = .ok y) {e1 e2 eF : Nat}
    (h1 : 1 ≤ e1 ∧ e1 < 2 ^ 59) (h2 : 1 ≤ e2 ∧ e2 < 2 ^ 59) :
    Layer.layout { h with eps1 := e1, eps2 := e2, epsF := eF } pc =
      .ok { y with h := { y.h with eps1 := e1, eps2 := e2, epsF := eF } } := by
  unfold Layer.layout at hy ⊢
  obtain ⟨y0, h0, hy⟩ := exc_bind hy
  refine (bind_ok (layoutBase_eps h0 h1 h2)).trans ?_
  exact layoutLook_eps hy e1 e2 eF

end SetUp

end HonestTraceRun

#print axioms HonestTraceRun.SetUp.layoutBase_eps
#print axioms HonestTraceRun.SetUp.layoutLook_eps
#print axioms HonestTraceRun.SetUp.layout_eps
