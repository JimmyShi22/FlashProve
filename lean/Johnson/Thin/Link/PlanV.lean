-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Thin/Link/PlanV.lean: in what the verifier program computes from the three configuration
files, the size of the vocabulary that the checks of the layers hold is the one of the parameter
file's shape.

Why. `Head.coveredOf` tests a request's tokens against `p.X.P.h.V`
(OnBytes/Model/VerifyStages.lean); the first group of layers tests them once more, against
`p.X.layers.V` (`ClaimEnv.claimE`, OnBytes/Model/LayerPanels.lean, called in
OnBytes/Model/Layer.lean). These are two fields of a record. Whoever says that a request which
passes the first test passes the second needs that the first number is at most the second.

Statements and proofs: the program's text is opened bind by bind. `Verify.publicOf`
(OnBytes/Model/VerifyPublic.lean) makes the layers' public numbers by `Layer.Pub.of`
(OnBytes/Model/LayerPlan.lean) at `P.h.V`, and that routine lays its argument into the field V.

Main names:
  `pubOf_V`: what `Layer.Pub.of y sc rope wsLay V tokv set` returns has V in its field V.
  `publicOf_V`: `Verify.publicOf pol KL layout = .ok X → X.layers.V = X.P.h.V`.




Limits: of an X that `Verify.publicOf` returns alone: at an arbitrary value of the type the two
fields are free. Nothing on the other fields. Nothing on soundness.
-/
import OnBytes.Model.Verify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Thin.Link
open OnBytes OnBytes.Model

/-- A step of a computation that can refuse. -/
private theorem ok_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e =>
    have h' : (Except.error e : Except ε β) = .ok b := h
    cases h'
  | ok a => exact ⟨a, rfl, h⟩

/-- `Layer.Pub.of` lays its argument V into the field V. -/
theorem pubOf_V {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {L : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok L) : L.V = V := by
  unfold Layer.Pub.of at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  cases h
  rfl

/-- `Verify.publicOf` makes the layers' public numbers at the shape's V. Lean lays the rest of that
text into both arms of its two ifs, so the binds are opened by a loop and every equation is kept. -/
theorem publicOf_V {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) : X.layers.V = X.P.h.V := by
  unfold Verify.publicOf at h
  obtain ⟨⟨P, y⟩, -, h⟩ := ok_bind h
  repeat (any_goals (first
    | (obtain ⟨_, _, h⟩ := ok_bind h)
    | (split at h)
    | (dsimp only at h)))
  all_goals
    cases h
    exact pubOf_V (by assumption)

end Cb.Thin.Link

