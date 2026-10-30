-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/SmallNearPlan.lean: "the digits' array is near" (nearA,
Johnson/Desc/First/Batch/SmallBehindDraw.lean) from ONE test with code on the plan's values and ONE
premise on the verifier's state. Definitions with code, statements and proofs.

Why. near_of_unsent (Johnson/Desc/First/Batch/SmallNear.lean) has eight premises. Seven of them read
the open link's list of arrays, the layout, the request's shape, the link's number and the plan's
seats: values that the plan fixes. One reads how far the link has come: the frame's list of own
messages is not yet as long as the number of the array's message.
  msgOfArray arr lay l t   the number, in link l, of the message that holds array number t of the
                           link's list; none where the list or the layout has no such array of
                           link l
  aheadPlanB sent own arr lay shape l t
                           the seven, as one test: array t of the list is of link l; the layout has
                           it; the shape has its message; that message's moment is not 0; the plan
                           has a seat for it at that moment; the seat is one of own
  near_of_plan             where the state's part has these four values (four equations), the test
                           accepts, and the frame's own messages are at most as many as that
                           number: nearA sent own a t = true
  Negative tests: the test rejects an empty list of arrays and an empty list of seats to read.

Can the premises be met? The test is evaluated at no plan here. The four equations and the premise
on the state are shown at no state here. That all hold together is not shown.
Limits. One way. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.SmallNear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- The number, in link l, of the message that holds array number t of the link's list. -/
def msgOfArray (arr : Array (Nat × String)) (lay : Params.ReqLayout) (l t : Nat) : Option Nat :=
  (arr[t]?).bind fun b => if b.1 == l then (reqArray lay l b.2).map (·.message) else none

/-- The seven premises on the plan, as one test. -/
def aheadPlanB (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))
    (arr : Array (Nat × String)) (lay : Params.ReqLayout) (shape : Params.ReqShape) (l t : Nat) :
    Bool :=
  match msgOfArray arr lay l t, shape.link[l]? with
  | some j, some sh =>
    match sh.messages[j]? with
    | some M =>
      M.moment != 0 &&
        match (sent M.moment)[((sh.messages.take j).filter fun y => y.moment == M.moment).length]?
        with
        | some x => own.contains x
        | none => false
    | none => false
  | _, _ => false

/-- **The digits' array is near: from the test on the plan and one premise on the state.** -/
theorem near_of_plan (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat)) (a : Part)
    (arr : Array (Nat × String)) (lay : Params.ReqLayout) (shape : Params.ReqShape) (l t j : Nat)
    (e1 : a.L.arrayOf = arr) (e2 : a.L.check.rows.layout = lay)
    (e3 : a.L.check.frame.shape = shape) (e4 : a.L.check.frame.link = l)
    (hB : aheadPlanB sent own arr lay shape l t = true) (hj : msgOfArray arr lay l t = some j)
    (h3 : a.L.check.frame.own.size ≤ j) : nearA sent own a t = true := by
  subst e1 e2 e3 e4
  unfold aheadPlanB at hB
  rw [hj] at hB
  unfold msgOfArray at hj
  obtain ⟨b, hb, hj⟩ := Option.bind_eq_some_iff.1 hj
  by_cases hl : (b.1 == a.L.check.frame.link) = true
  · rw [if_pos hl] at hj
    obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hb' : a.L.arrayOf[t]? = some (a.L.check.frame.link, b.2) := by
      rw [hb, ← eq_of_beq hl]
    cases hs : a.L.check.frame.shape.link[a.L.check.frame.link]? with
    | none =>
      rw [hs] at hB
      cases hB
    | some sh =>
      rw [hs] at hB
      cases hM : sh.messages[A.message]? with
      | none =>
        simp only [hM] at hB
        cases hB
      | some M =>
        simp only [hM, Bool.and_eq_true, bne_iff_ne, ne_eq] at hB
        obtain ⟨h6, h78⟩ := hB
        cases hx : (sent M.moment)[((sh.messages.take A.message).filter fun y =>
            y.moment == M.moment).length]? with
        | none =>
          rw [hx] at h78
          cases h78
        | some x =>
          rw [hx] at h78
          exact near_of_unsent sent own a t b.2 A sh M x hb' hA h3 hs hM h6 hx
            (List.contains_iff_mem.1 h78)
  · rw [if_neg hl] at hj
    cases hj

/-! ### Negative tests -/

/-- The test rejects an empty list of arrays. -/
theorem aheadPlanB_no_array (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))
    (lay : Params.ReqLayout) (shape : Params.ReqShape) (l t : Nat) :
    aheadPlanB sent own #[] lay shape l t = false := rfl

/-- The test rejects where no seat may be read. -/
theorem aheadPlanB_no_own (sent : Nat → List (Nat × Nat)) (arr : Array (Nat × String))
    (lay : Params.ReqLayout) (shape : Params.ReqShape) (l t : Nat) :
    aheadPlanB sent [] arr lay shape l t = false := by
  unfold aheadPlanB
  split
  · split
    · split
      · simp
      · simp
    · rfl
  · rfl

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.near_of_plan
#print axioms VerifiableInference.Desc.K9.aheadPlanB_no_array
#print axioms VerifiableInference.Desc.K9.aheadPlanB_no_own
