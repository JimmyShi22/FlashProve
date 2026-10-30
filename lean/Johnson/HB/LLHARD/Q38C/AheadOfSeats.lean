-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38C/AheadOfSeats.lean: what the list of rounds says of an array that is still
ahead (`K9.aheadIn`, Johnson/Desc/First/Batch/Ahead.lean), AS A VALUE, WITH THE SEAT THAT THE
LOOKUPS' LETTERS GIVE. One statement with its proof; nothing is evaluated.

  `ahead_of_seats`: from e1 to e5, the five equations on the open segment's context of
    `near_of_plan_size` (Johnson/Desc/First/Batch/SmallNearSize.lean), in its letters; hnear: its
    test `aheadPlanSizeB` accepts; hS: the seat equation accepts (`aheadSeatsB`,
    Johnson/HB/LLHARD/Q38C/AheadSeats.lean): there are the array's entry bn, the array A, the
    segment's shape sh and the message M, and `aheadIn sent own a bn` is ⟨A, seat A.message,
    M.shape⟩.

WHAT OF hnear IS SPENT: array number t of the segment's list is the segment's own; the layout has
it; the shape has the segment, and the segment the array's oracle message; that message is not among
the first n₀. What hnear says beside, on a seat in "sent" and that it may be read, is not spent: hS
says it, of the lookups' seat. The clause bn.1 = l in the end is handed on for whoever wants it.

By `aheadIn_of_unsent` (Johnson/HB/LLHARD/Q38A/AheadInOfUnsent.lean); the case tree follows
`near_of_plan` (Johnson/Desc/First/Batch/SmallNearPlan.lean), which ends in a Bool and drops the
value.

Can the premises be met? hS at the full size: Johnson/HB/LLHARD/Q38C/AheadSeatsWritten.lean. hnear
is a named test. The five equations are facts on a reached state: shown elsewhere.

WHICH ROWS OF THE HEAD IT SPENDS, BY THE CODE: none: it reads no field of the head.

Limits. Nothing on soundness.
-/
import Johnson.HB.LLHARD.Q38C.AheadSeats
import Johnson.HB.LLHARD.Q38A.AheadInOfUnsent
import Johnson.Desc.First.Batch.SmallNearSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc

/-- **What the list of rounds says of an array that is still ahead, as a value**: from five
equations on the open segment's context, the test that the array's oracle message is ahead, and the
seat equation. -/
theorem ahead_of_seats (n₀ : Nat) (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))
    (a : K9.Part) (arr : Array (Nat × String)) (lay : Params.ReqLayout) (shape : Params.ReqShape)
    (seat : Nat → Nat × Nat) (l t : Nat) (e1 : a.L.arrayOf = arr)
    (e2 : a.L.check.rows.layout = lay) (e3 : a.L.check.frame.shape = shape)
    (e4 : a.L.check.frame.link = l) (e5 : a.L.check.frame.own.size = n₀)
    (hnear : K9.aheadPlanSizeB n₀ sent own arr lay shape l t = true)
    (hS : aheadSeatsB shape sent own seat l n₀ = true) :
    ∃ bn A sh M, arr[t]? = some bn ∧ bn.1 = l ∧ reqArray lay l bn.2 = some A ∧
      shape.link[l]? = some sh ∧ sh.messages[A.message]? = some M ∧
      K9.aheadIn sent own a bn = some ⟨A, seat A.message, M.shape⟩ := by
  subst e1 e2 e3 e4 e5
  unfold K9.aheadPlanSizeB at hnear
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hnear
  cases hj : K9.msgOfArray a.L.arrayOf a.L.check.rows.layout a.L.check.frame.link t with
  | none =>
    rw [hj] at h2
    cases h2
  | some j =>
    rw [hj] at h2
    have h3 : a.L.check.frame.own.size ≤ j := of_decide_eq_true h2
    unfold K9.aheadPlanB at h1
    rw [hj] at h1
    unfold K9.msgOfArray at hj
    obtain ⟨b, hb, hj⟩ := Option.bind_eq_some_iff.1 hj
    by_cases hl : (b.1 == a.L.check.frame.link) = true
    · rw [if_pos hl] at hj
      obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 hj
      cases hs : a.L.check.frame.shape.link[a.L.check.frame.link]? with
      | none =>
        rw [hs] at h1
        cases h1
      | some sh =>
        rw [hs] at h1
        cases hM : sh.messages[A.message]? with
        | none =>
          simp only [hM] at h1
          cases h1
        | some M =>
          obtain ⟨h6, h7, h8⟩ := c_aheadSeats_at hS hs hM h3
          refine ⟨b, A, sh, M, hb, eq_of_beq hl, hA, rfl, hM, ?_⟩
          have eb : b = (a.L.check.frame.link, b.2) := by rw [← eq_of_beq hl]
          rw [eb]
          exact aheadIn_of_unsent sent own a b.2 A sh M (seat A.message) hA h3 hs hM h6 h7 h8
    · rw [if_neg hl] at hj
      cases hj

end Q38

#print axioms Q38.ahead_of_seats
