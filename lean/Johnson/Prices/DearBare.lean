-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/DearBare.lean: the neighbour of `shared_dear` (Johnson/Prices/Dear.lean) at a round's
own error, without the planner's addition for the round's draws.

`dearBare s r`: the round's own error, `PlanRound.error`, is above 2 ^ (work - target - 1); one
exact comparison (`dearBare_sound`). `places_of_marks`: a test f on rounds that says of the 60 typed
rounds of `sharedTail` what `sharedTailMarks` says, and yes of the typed LOC, says yes at each of
the 34 places of every shared plan at the typed sizes. `shared_bare`: so do `dear` and `dearBare`
together. `term_above`: at the target 128, for a round with `dearBare`, every number kappa that is
at least 1 and every b: 64 * (kappa ^ b * (error / 2 ^ work)) is above 2 / 2 ^ 128; it is above 2 ^
-123 (`term_above_123`).

By `decide +kernel`, that is, evaluated by Lean's kernel at the written numbers, and turning with
them: `sharedTail_both`, `sharedLoc_both`.

Main definitions: `dearBare`, `both`.
Main theorems: `dearBare_sound`, `places_of_marks`, `shared_bare`, `term_above_123`, `term_above`.
What is not claimed: what the head of Johnson/Prices/Dear.lean does not claim. That any law takes a
shared round's error 64 times, or has a term of the form kappa ^ b * (c / 2 ^ work) at c the round's
own error: no such law is imported. A price is an upper bound that the planner charges: that 64
prices are above a number says that this accounting does not reach the number, not that a prover's
chance is large.

-/
import Johnson.Prices.Dear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices

/-- The round's own error is above half of 2 ^ (work - target). -/
def dearBare (s : Setting) (r : PlanRound) : Bool :=
  !r.error.le (Binary.twoTo ((r.entry.work : Int) - (s.target : Int) - 1))

/-- **What `dearBare` says, in rational numbers.** -/
theorem dearBare_sound {s : Setting} {r : PlanRound} (h : dearBare s r = true) :
    (2 : ℚ) ^ ((r.entry.work : ℤ) - (s.target : ℤ) - 1) < r.error.val := by
  unfold dearBare at h
  simp only [Bool.not_eq_true'] at h
  have h2 := Binary.lt_of_not_le _ _ h
  rw [Binary.val_twoTo] at h2
  exact h2

/-- Both tests. -/
def both (s : Setting) (r : PlanRound) : Bool := dear s r && dearBare s r

/-- The 60 rounds of `sharedTail`, one by one. By evaluation in Lean's kernel. -/
theorem sharedTail_both :
    (sharedTail.map fun y => both recordSet (y.round recordSet .shared)) = sharedTailMarks := by
  decide +kernel

/-- The typed LOC. By evaluation in Lean's kernel. -/
theorem sharedLoc_both : both recordSet (sharedLoc.round recordSet .shared) = true := by
  decide +kernel

/-- **From the marks of the typed rounds to the 34 places of every shared plan at such sizes.** -/
theorem places_of_marks (f : PlanRound → Bool)
    (hT : (sharedTail.map fun y => f (y.round recordSet .shared)) = sharedTailMarks)
    (hL : f (sharedLoc.round recordSet .shared) = true) {codes : Codes} {x : LinSized}
    {P : Planned} (hx : AtRecord x) (h : sharedPlan recordSet codes x = .ok P) :
    ∀ i ∈ dearPlaces, ∃ r, P.rounds[i]? = some r ∧ f r = true := by
  obtain ⟨h7, h3⟩ := shared_rounds_at hx h
  intro i hi
  have hi' : i = 3 ∨ i ∈ dearPlaces.tail := by
    simpa [dearPlaces] using hi
  rcases hi' with rfl | hi'
  · exact ⟨_, h3, hL⟩
  · rw [dearPlaces_marks.2] at hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    obtain ⟨hj1, hj2⟩ := List.mem_filter.mp hj
    have hj60 : j < 60 := List.mem_range.mp hj1
    have hlen : sharedTail.length = 60 := by
      have := congrArg List.length hT
      simpa [sharedTailMarks] using this
    have hget : P.rounds[j + 7]? = (P.rounds.drop 7)[j]? := by
      rw [List.getElem?_drop, Nat.add_comm]
    have hj' : j < sharedTail.length := by omega
    refine ⟨(sharedTail[j]).round recordSet .shared, ?_, ?_⟩
    · rw [hget, h7, List.getElem?_map, List.getElem?_append_left hj', List.getElem?_eq_getElem hj']
      rfl
    · have e := congrArg (fun l => l.getD j false) hT
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj',
        Option.map_some, Option.getD_some] at e
      rw [e]
      simpa [List.getD_eq_getElem?_getD] using hj2

/-- **At each of the 34 places: the round holds, and its whole error and its own error are above 2 ^
(work - target - 1).** -/
theorem shared_bare {codes : Codes} {x : LinSized} {P : Planned} (hx : AtRecord x)
    (h : sharedPlan recordSet codes x = .ok P) :
    ∀ i ∈ dearPlaces, ∃ r, P.rounds[i]? = some r ∧ dear recordSet r = true ∧
      dearBare recordSet r = true := by
  intro i hi
  obtain ⟨r, hr, hb⟩ := places_of_marks (both recordSet) sharedTail_both sharedLoc_both hx h i hi
  unfold both at hb
  rw [Bool.and_eq_true] at hb
  exact ⟨r, hr, hb.1, hb.2⟩

/-- At the target 128: 64 times kappa ^ b times the round's own error over 2 ^ work is above 2 ^
-123. -/
theorem term_above_123 {s : Setting} {r : PlanRound} (h : dearBare s r = true)
    (ht : s.target = 128) {kappa : ℚ} (hk : 1 ≤ kappa) (b : ℕ) :
    (2⁻¹ : ℚ) ^ 123 < 64 * (kappa ^ b * (r.error.val / 2 ^ r.entry.work)) := by
  have h1 := dearBare_sound h
  rw [ht] at h1
  have hw : (0 : ℚ) < 2 ^ r.entry.work := by positivity
  have e : (2 : ℚ) ^ ((r.entry.work : ℤ) - ((128 : ℕ) : ℤ) - 1) =
      2 ^ r.entry.work * (2⁻¹ : ℚ) ^ 129 := by
    rw [sub_sub, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, inv_pow, div_eq_mul_inv]
    norm_num
  rw [e] at h1
  have h2 : (2⁻¹ : ℚ) ^ 129 < r.error.val / 2 ^ r.entry.work := by
    rw [lt_div_iff₀ hw, mul_comm]
    exact h1
  have hkb : (1 : ℚ) ≤ kappa ^ b := one_le_pow₀ hk
  have h3 : r.error.val / 2 ^ r.entry.work ≤ kappa ^ b * (r.error.val / 2 ^ r.entry.work) :=
    le_mul_of_one_le_left (div_nonneg (Binary.val_nonneg r.error) hw.le) hkb
  have h4 : (2⁻¹ : ℚ) ^ 123 = 64 * (2⁻¹ : ℚ) ^ 129 := by norm_num
  rw [h4]
  linarith

/-- **So it is above 2 / 2 ^ 128.** -/
theorem term_above {s : Setting} {r : PlanRound} (h : dearBare s r = true) (ht : s.target = 128)
    {kappa : ℚ} (hk : 1 ≤ kappa) (b : ℕ) :
    (2 : ℚ) / 2 ^ 128 < 64 * (kappa ^ b * (r.error.val / 2 ^ r.entry.work)) :=
  lt_trans (by norm_num) (term_above_123 h ht hk b)

end OnBytes.Params.Prices
