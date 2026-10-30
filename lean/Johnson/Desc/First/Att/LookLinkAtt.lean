-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/LookLinkAtt.lean: the place of an attention link's lookup bears that link's
number.

  `lookAt_att_link`: where the proof covers attention and the record has group g's plan, the place
    that lookAt returns at link 2 g + 1 has link = 2 g + 1. By lookAt's own text
    (Johnson/Desc/First/Look/LookAt.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GuardArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (lookAt)

/-- The place bears the link's number. -/
theorem lookAt_att_link {W : Verify.Public} {g : ℕ} {a : Attention.Plan}
    {x : VerifiableInference.Desc.First.Look.Place} (h4 : W.p4 = true) (ha : W.A[g]? = some a)
    (hx : lookAt W (2 * g + 1) false = some x) : x.link = 2 * g + 1 := by
  have hn : ((2 * g + 1 == 2 * W.NGr) = false) := by
    rw [beq_eq_false_iff_ne]
    omega
  have h0 : (((2 * g + 1) % 2 == 0) = false) := by
    rw [beq_eq_false_iff_ne]
    omega
  have eg : (2 * g + 1) / 2 = g := by omega
  unfold lookAt at hx
  simp only [h4, if_true, hn, h0, eg, ha, Option.bind_some, Bool.false_eq_true, if_false] at hx
  obtain rfl := Option.some.inj hx
  rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.lookAt_att_link
