-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/SmallNearSize.lean: "the digits' array is near" (nearA) from ONE test with
code on public values, and five equations on the open link's context. A rider to
Johnson/Desc/First/Batch/SmallNearPlan.lean, which stands unturned. A definition with code,
statements and proofs.

Why. near_of_plan has one premise on how far the link has come: the frame's list of own messages is
at most as long as the number j of the array's message. Where that list's length is known as a
number n₀ of the plan (in front of the smallness test's draw: the messages of the link's moments 0
and 1), the premise is the comparison n₀ ≤ j: one conjunct more of the test.
  aheadPlanSizeB n₀ sent own arr lay shape l t
                      aheadPlanB, and the number of the array's message is at least n₀
  near_of_plan_size   where the state's part has the four values of near_of_plan, the frame's own
                      messages are n₀, and the test accepts: nearA sent own a t = true
  Negative tests: the test rejects an empty list of arrays; and it rejects wherever aheadPlanB does.

Can the premises be met? The test is evaluated at no plan here; the five equations are shown at no
state here. That all hold together is not shown.
Limits. One way. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.SmallNearPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- The test on the plan, with "the array's message is not among the first n₀ of the link". -/
def aheadPlanSizeB (n₀ : Nat) (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))
    (arr : Array (Nat × String)) (lay : Params.ReqLayout) (shape : Params.ReqShape) (l t : Nat) :
    Bool :=
  aheadPlanB sent own arr lay shape l t && (msgOfArray arr lay l t).any fun j => decide (n₀ ≤ j)

/-- **The digits' array is near: from one test on public values and five equations.** -/
theorem near_of_plan_size (n₀ : Nat) (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))
    (a : Part) (arr : Array (Nat × String)) (lay : Params.ReqLayout) (shape : Params.ReqShape)
    (l t : Nat) (e1 : a.L.arrayOf = arr) (e2 : a.L.check.rows.layout = lay)
    (e3 : a.L.check.frame.shape = shape) (e4 : a.L.check.frame.link = l)
    (e5 : a.L.check.frame.own.size = n₀)
    (hB : aheadPlanSizeB n₀ sent own arr lay shape l t = true) : nearA sent own a t = true := by
  unfold aheadPlanSizeB at hB
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hB
  cases hj : msgOfArray arr lay l t with
  | none =>
    rw [hj] at h2
    cases h2
  | some j =>
    rw [hj] at h2
    have h3 : n₀ ≤ j := of_decide_eq_true h2
    exact near_of_plan sent own a arr lay shape l t j e1 e2 e3 e4 h1 hj (by rw [e5]; exact h3)

/-! ### Negative tests -/

/-- The test rejects an empty list of arrays. -/
theorem aheadPlanSizeB_no_array (n₀ : Nat) (sent : Nat → List (Nat × Nat))
    (own : List (Nat × Nat)) (lay : Params.ReqLayout) (shape : Params.ReqShape) (l t : Nat) :
    aheadPlanSizeB n₀ sent own #[] lay shape l t = false := rfl

/-- It rejects wherever the test without the comparison does. -/
theorem aheadPlanSizeB_of_no (n₀ : Nat) (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))
    (arr : Array (Nat × String)) (lay : Params.ReqLayout) (shape : Params.ReqShape) (l t : Nat)
    (h : aheadPlanB sent own arr lay shape l t = false) :
    aheadPlanSizeB n₀ sent own arr lay shape l t = false := by
  unfold aheadPlanSizeB
  rw [h]
  rfl

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.near_of_plan_size
#print axioms VerifiableInference.Desc.K9.aheadPlanSizeB_no_array
#print axioms VerifiableInference.Desc.K9.aheadPlanSizeB_of_no
