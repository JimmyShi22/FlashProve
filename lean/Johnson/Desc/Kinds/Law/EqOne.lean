-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/EqOne.lean: the kinds' equality weight is the library's (the lookups' rider's law speaks of
OnBytes.Model.eqOne). `eq_eq_eqOne`: HeadParts.lean's `eq z i` is
OnBytes/Model/Frame.lean's `eqOne z i`, as records, at a point of at most 63 coordinates. The premise
is needed: from 64 coordinates on eqOne is 0 at every index (its test eqIndexOK), and `eq` is not.
No Mathlib.
-/
import OnBytes.Model.Frame
import Johnson.Desc.Kinds.HeadParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)

theorem eq_eq_eqOne (z : Point) (i : Nat) (hz : z.size ≤ 63) :
    eq z i = OnBytes.Model.eqOne z i := by
  unfold eq OnBytes.Model.eqOne OnBytes.Model.eqIndexOK
  by_cases h : i < 2 ^ z.size
  · simp only [h, hz, if_true, decide_true, Bool.and_self]
    rfl
  · simp only [h, if_false, decide_false, Bool.and_false, Bool.false_eq_true]
    rfl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.eq_eq_eqOne
