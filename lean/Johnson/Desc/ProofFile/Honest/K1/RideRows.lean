-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/RideRows.lean: THE SHARED "SENDING" (the kind K1): A RIDING TABLE
OF MORE THAN ONE ROW: BEYOND ITS PLACES IT HOLDS 0 · THE TWO ROWS AT ⟨5, 1⟩ WRITTEN OUT · ON rowsR
NO OTHER PLACE OF A RIDING MESSAGE's MASK HOLDS ANYTHING BUT 0. PUBLIC IN FORM. Six theorems; no
definition. NO NEW ARGUMENT: CALLS OF TWO OTHER HOUSES' LAWS.

  - lay_far (h ≤ k): from place 2 k - h + 1 on Ride.lay at ⟨k, h⟩ is 0. By lay_eq
    (Johnson/SendSim/At/RideLay.lean) and plan_places (Honest/K14/SendingsPlan.lean).
  - lay_w_row0, lay_w_row1: AT ⟨5, 1⟩, the numbers of the rider of W's sending
    (Law/RideAtPlans.lean): row 0: c 2, 0, c 3, c 4, c 5, c 6, c 7, c 9, c 10, c 8 · row 1: c 2 + c
    0, c 1, c 3, c 4, c 5, c 6, c 7, c 9, c 10, c 8. By lay_eq at the two written plans (closed
    evaluations of the other house's plan 5 1 b).
  - lay_w_row0_alone: A CONTROL FOR lay_fixes (RideFixes.lean): from row 0 alone the values do not
    follow: "1 at number 0, else 0" and "0 everywhere" lay the same row 0.
  - ride_sizes_more: what the public test rideFits says at every h: 2 ^ h mask rows; h ≤ k; 1 ≤ k;
    the 2 k - h + 1 places lie inside the mask code's message length.
  - no_other_ride_more: ON rowsR, under sendFits, at a message whose table rides at R: at a row
    from 2 ^ R.h on, or at a place beyond 2 R.k - R.h, the mask holds 0. no_other_ride's like
    (Honest/K1/NoOther.lean), without h0 : R.h = 0.

KIN, TOLD; NONE IS RESTATED. What stands at each place, at every R: lay_eq with plan, firstPlan
(RideLay.lean); the laws on plan (SendingsPlan.lean: plan_place, plan_once, plan_rows_low,
plan_rows_high and others). Additive: lay_add (RideLay.lean); on rowsR: mask_add
(Johnson/SendSim/At/Rows.lean). rows_of_ride (Rows.lean) is ride_sizes_more's first clause under
sendFits. Rows written out at ⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩: Johnson/SendSim/At/RiderTwoTie.lean,
RiderTwoOnePlace.lean, RiderThreeOnePlace.lean.

Limits. IT SAYS WHAT STANDS WHERE, AND NOTHING ELSE. On the rows alone. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlan
import Johnson.Desc.ProofFile.Honest.K1.RideOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)
open OnBytes.SendSim.At (plan sumAt lay_eq)
open ProofFile.Honest.K14 (plan_places)

/-- **BEYOND ITS PLACES A RIDING TABLE HOLDS 0.** -/
theorem lay_far (k h b : ℕ) (c : ℕ → GE) (j : ℕ) (hh : h ≤ k) (hj : 2 * k - h + 1 ≤ j) :
    (⟨k, h⟩ : Ride).lay c b j = 0 := by
  rw [lay_eq]
  exact List.getD_eq_default _ _ (by
    rw [List.length_map]
    exact (plan_places hh).symm ▸ hj)

/-- **AT ⟨5, 1⟩, ROW 0.** -/
theorem lay_w_row0 (c : ℕ → GE) :
    (List.range 10).map ((⟨5, 1⟩ : Ride).lay c 0) =
      [c 2, 0, c 3, c 4, c 5, c 6, c 7, c 9, c 10, c 8] := by
  have p : plan 5 1 0 = [[2], [], [3], [4], [5], [6], [7], [9], [10], [8]] := by decide
  have e : ∀ j, (⟨5, 1⟩ : Ride).lay c 0 j =
      (([[2], [], [3], [4], [5], [6], [7], [9], [10], [8]] : List (List ℕ)).map
        (sumAt c)).getD j 0 := fun j => by
    rw [lay_eq]
    exact congrArg (fun L => (List.map (sumAt c) L).getD j 0) p
  simp [List.range_succ, e, sumAt]

/-- **AT ⟨5, 1⟩, ROW 1.** -/
theorem lay_w_row1 (c : ℕ → GE) :
    (List.range 10).map ((⟨5, 1⟩ : Ride).lay c 1) =
      [c 2 + c 0, c 1, c 3, c 4, c 5, c 6, c 7, c 9, c 10, c 8] := by
  have p : plan 5 1 1 = [[2, 0], [1], [3], [4], [5], [6], [7], [9], [10], [8]] := by decide
  have e : ∀ j, (⟨5, 1⟩ : Ride).lay c 1 j =
      (([[2, 0], [1], [3], [4], [5], [6], [7], [9], [10], [8]] : List (List ℕ)).map
        (sumAt c)).getD j 0 := fun j => by
    rw [lay_eq]
    exact congrArg (fun L => (List.map (sumAt c) L).getD j 0) p
  simp [List.range_succ, e, sumAt]

/-- A control: from row 0 alone the values do not follow. -/
theorem lay_w_row0_alone :
    (∀ j, (⟨5, 1⟩ : Ride).lay (fun i => if i = 0 then (1 : GE) else 0) 0 j =
      (⟨5, 1⟩ : Ride).lay (fun _ => (0 : GE)) 0 j) ∧
    (fun i => if i = 0 then (1 : GE) else 0) 0 ≠ (fun _ : Nat => (0 : GE)) 0 := by
  refine ⟨fun j => ?_, by simp⟩
  by_cases hj : j < 10
  · have e0 := lay_w_row0 (fun i => if i = 0 then (1 : GE) else 0)
    have e1 := lay_w_row0 (fun _ => (0 : GE))
    have e : (List.range 10).map ((⟨5, 1⟩ : Ride).lay (fun i => if i = 0 then (1 : GE) else 0) 0) =
        (List.range 10).map ((⟨5, 1⟩ : Ride).lay (fun _ => (0 : GE)) 0) := by
      rw [e0, e1]
      simp
    exact (List.map_inj_left.1 e) j (List.mem_range.2 hj)
  · rw [lay_far 5 1 0 _ j (by omega) (by omega), lay_far 5 1 0 _ j (by omega) (by omega)]

/-- What rideFits says, at every h. -/
theorem ride_sizes_more (codes : Codes) (s : OracleShape) (R : Ride)
    (h : rideFits codes s R = true) :
    s.maskRows = 2 ^ R.h ∧ R.h ≤ R.k ∧ 1 ≤ R.k ∧
      2 * R.k - R.h + 1 ≤ (codes.mask.getD s.maskCode default).ell := by
  simp only [rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **ON rowsR: NO OTHER PLACE**: at a riding table of 2 ^ h rows. -/
theorem no_other_ride_more (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k r p : Nat) (R : Ride)
    (hf : sendFits P ride = true) (hk : k < P.sent.size) (hr : ride k = some R)
    (hh : 2 ^ R.h ≤ r ∨ 2 * R.k - R.h < p) : (rowsR P ride data cs k).mask r p = 0 := by
  obtain ⟨hm, hle, -, -⟩ := ride_sizes_more _ _ _ (fits_ride P ride k _ hf hk hr)
  by_cases hin : r < (shapeAt P k).maskRows ∧
      p < (P.codes.mask.getD (shapeAt P k).maskCode default).ell
  · rw [ride_coin P ride data cs k r p _ hr hin.1 hin.2]
    have hr2 : r < 2 ^ R.h := hm ▸ hin.1
    obtain ⟨kk, hhh⟩ := R
    exact lay_far kk hhh r _ p hle (by
      have : 2 * kk - hhh < p := by
        rcases hh with h1 | h1
        · exact absurd hr2 (by simpa using h1)
        · exact h1
      omega)
  · simp only [rowsR, hr]
    rw [if_neg hin]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lay_far
#print axioms ProofFile.Honest.K1.lay_w_row0
#print axioms ProofFile.Honest.K1.lay_w_row1
#print axioms ProofFile.Honest.K1.lay_w_row0_alone
#print axioms ProofFile.Honest.K1.ride_sizes_more
#print axioms ProofFile.Honest.K1.no_other_ride_more
