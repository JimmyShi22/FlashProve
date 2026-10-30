-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/AtDot.lean: the premises of the (Dot) joint, by name: a structure of Prop on
the record in front of K14's second part of the last chain. No theorem.

The four fields.
  lin: the shape is lawful at the statement's codes (`linOk`).
  w: the message at W's number is there and has the plan's shape of W.
  omega: Omega, in the border's copy of the shared statement, has the plan's shape of Omega.
  weights: every vector of the border's row weights is well-formed (`Tensor.ok`).
Who gives which: Johnson/Desc/Third/Law/AtDotStart.lean: at the record that the start returns, lin
and w are given by the start's yes; omega and weights are taken there as premises.

Limits. No record is shown here at which it holds. At a record without a border `omega` and
`weights` hold idly (`lin` and `w` do not); the block's yes gives a border. What the joint makes of
the four is not in this file. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.K14BatchLinearConstraintsSecondPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third.Law

/-- **The premises of the joint, by name**: all on the record in front of the block. -/
structure AtDot (p : P₁₄) (s : S₃) : Prop where
  lin : linOk s.st.codes p.S = true
  w : ∃ x, s.st.oracles[s.loc.w]? = some x ∧ x.shape = p.S.w
  omega : ∀ b y, s.loc.border = some b → b.shared.st.oracles[b.shared.omega]? = some y →
    y.shape = p.S.omega
  weights : ∀ b, s.loc.border = some b → ∀ g ∈ b.g, g.ok = true

end VerifiableInference.Desc.Third.Law
