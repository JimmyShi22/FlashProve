-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPadShape.lean.
The shape in the record that Forest.pad returns is made by the byte-level verifier's own routines.

States:
  ask_ok: the test of the numbers of padding keys, as Forest.pad writes it (toBool), says that
    Forest.pubAsk returns.
  pad_shape: the record's shape is the chain's: the shape with these numbers filled in.
  pad_shapeOf: along the chain of Fo.PadCut the record's shape meets Fo.ShapeOf.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadCut
import OnBytes.Tie.Pv.Lookup.Port.FoHeard

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem ask_ok {ε : Type} {x : Except ε Unit} (h : x.toBool = true) : x = .ok () := by
  cases x with
  | error e => exact absurd h (by simp [Except.toBool])
  | ok u => rfl

section
variable {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx}
  {g : Forest.Heard} {M : PadMid}

theorem pad_shape (P : PadCut calls pub lid F c g F' c' M) : g.shape = M.h pub := by
  rw [P.heard]
  rfl

theorem pad_shapeOf (P : PadCut calls pub lid F c g F' c' M) : ShapeOf calls pub lid g.shape :=
  ⟨M.h0, P.shape, ask_ok P.ask, pad_shape P⟩

end
end Fo
