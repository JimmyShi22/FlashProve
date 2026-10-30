-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFCellIdnOK.lean: the sources of the bits of the token and the channel, and two lemmas on
vertices, for the identity (J11) on the embedding of the tokens (`j11Fam`,
Cm/TargetSegFFCellIdnOK.lean).

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

The head of Cm/SegFFCellIdn.lean says what the families are.

Main names:
  `σT`, `σJ`: the sources of the bits of the token and of the channel: the inner vertex b · 2^18 + t
    has 41 variables: channel 0 .. 12, position 13 .. 22, token 23 .. 40.
  `enc2`, `enc2_lt`: what a vertex a · 2^10 + i encodes.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFCellIdn
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef)

variable [scl : Scl]

/-- the sources of the bits of the token and of the channel, among the 41 variables of the inner
vertex -/
def σT : List Src := Src.run 23 18
def σJ : List Src := Src.run 0 13

theorem enc2 {a i : ℕ} (hi : i < 2 ^ 10) :
    (a * 2 ^ 10 + i) / 2 ^ 10 = a ∧ (a * 2 ^ 10 + i) % 2 ^ 10 = i := by omega

theorem enc2_lt {n a i : ℕ} (ha : a < 2 ^ n) (hi : i < 2 ^ 10) : a * 2 ^ 10 + i < 2 ^ (n + 10) := by
  rw [pow_add]
  nlinarith [Nat.two_pow_pos 10]

end Cm.Seg
