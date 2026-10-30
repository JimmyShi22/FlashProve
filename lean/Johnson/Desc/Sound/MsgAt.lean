-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MsgAt.lean: from the rule of composition's own type of oracles at a boundary
(`Frame.E`, ChainRule.lean) to the plain functions of Johnson/Desc/Msg.lean. Three definitions.
NOTHING IS PROVED IN THIS FILE.
  `colAt Fr y j x`: the column at leaf x of the tree number j: by the library's `posL` in the
    frame's list.
  `cellAt Fr y x`: the stored table's symbol at x.
  `strsOf Fr y`: both, as a `Strs`. So a relation that is typed over (S, Strs, W) is laid at a
    boundary of the rule as `fun a w => R a.1 (strsOf Fr a.2) w`.
Limits: where the library's `posL` gives no position the column is empty; beyond the stored table's
depth there is no symbol. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Msg
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker
open _root_.Run.PQ (CK SgX)

/-- The column at leaf x of the tree number j. -/
def colAt (Fr : Frame) (y : Fr.E.Str) (j x : ℕ) : List UInt64 := ((posL Fr.all j x).map y.2).getD []

/-- The stored table's symbol at x. -/
def cellAt (Fr : Frame) (y : Fr.E.Str) (x : ℕ) : Option (ℕ × List UInt64) :=
  if h : x < 2 ^ Fr.a then some (y.1 ⟨x, h⟩) else none

/-- The oracles at a boundary, as plain functions. -/
def strsOf (Fr : Frame) (y : Fr.E.Str) : Strs := ⟨cellAt Fr y, colAt Fr y⟩

end VerifiableInference.Desc.Sound
