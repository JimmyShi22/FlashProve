-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardArms.lean: kind K5: the door's rows (K5Asks.rowW,
Johnson/Desc/First/Att/GuardO.lean) have an arm "a link has no plan or no place", in which every row
is false whatever its test. This file says when that arm is not reached.

Main names:
  `lookAt_att_some`: where the proof covers attention and the record has group g's plan, the
    lookup's place at link 2 g + 1 is there. By lookAt's own text
    (Johnson/Desc/First/Look/LookAt.lean); no test is asked.
  `arms_unreached`: **where the record has a plan for every group below its number of groups, every
    link of the rows' walk has its plan and its place**: so each row evaluates its own test at every
    link.
Limits. That a record has a plan for every group is a premise here. Behind a return of the proof
file's description it follows from the row K05_sits, which is not imported.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GuardAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (lookAt)

/-- The place of an attention link's lookup is there wherever the group's plan is. -/
theorem lookAt_att_some {W : Verify.Public} {g : ℕ} {a : Attention.Plan} (h4 : W.p4 = true)
    (ha : W.A[g]? = some a) : ∃ x, lookAt W (2 * g + 1) false = some x := by
  have hn : ((2 * g + 1 == 2 * W.NGr) = false) := by
    rw [beq_eq_false_iff_ne]
    omega
  have h0 : (((2 * g + 1) % 2 == 0) = false) := by
    rw [beq_eq_false_iff_ne]
    omega
  have eg : (2 * g + 1) / 2 = g := by omega
  unfold lookAt
  simp only [h4, if_true, hn, h0, eg, ha, Option.bind_some, Bool.false_eq_true, if_false]
  exact ⟨_, rfl⟩

/-- **Every link of the rows' walk has its plan and its place.** -/
theorem arms_unreached {W : Verify.Public} (hA : ∀ g < W.NGr, ∃ a, W.A[g]? = some a) :
    ∀ y ∈ attLinksN W, ∃ a x, W.A[y.2]? = some a ∧ lookAt W y.1 false = some x := by
  intro y hy
  obtain ⟨h4, e1, hg⟩ := attLinks_mem hy
  obtain ⟨a, ha⟩ := hA y.2 hg
  obtain ⟨x, hx⟩ := lookAt_att_some h4 ha
  exact ⟨a, x, ha, by rw [e1]; exact hx⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.lookAt_att_some
#print axioms VerifiableInference.Desc.First.Att.P.arms_unreached
