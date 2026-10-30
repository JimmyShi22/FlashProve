-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/SumStepsProofs.lean: the proofs of Cb/Gen/SumSteps.lean (for the sumcheck protocol: a
polynomial summand written as a sequence of steps of degree at most 2). No protocol.

A step that names only variables below n has the same value on Y and Y' that agree below n
(`QStep.eval_congr`). Filling in step l changes the variable nc + l alone, which, by `S.Tri`, no
earlier step names; so after all steps each auxiliary variable is its step at the final values.
Backward, again by `S.Tri`: by induction on l, numbers that satisfy the rows and are right on the
first nc variables agree with the filled values below nc + l.
-/
import Cb.Gen.SumSteps
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace Cb
open Blocks

variable {E : Type} [CommRing E]

theorem linSum_congr {Y Y' : ℕ → E} {n : ℕ} (hY : ∀ j, j < n → Y j = Y' j) :
    ∀ {ts : List (E × ℕ)}, (∀ t ∈ ts, t.2 < n) → linSum Y ts = linSum Y' ts
  | [], _ => rfl
  | t :: ts, h => by
      have ih := linSum_congr hY (ts := ts) fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
      unfold linSum at ih ⊢
      simp only [List.map_cons, List.sum_cons, ih, hY _ (h t List.mem_cons_self)]

theorem termSum_congr_below {Y Y' : ℕ → E} {n : ℕ} (hY : ∀ j, j < n → Y j = Y' j) :
    ∀ {ts : List (E × ℕ × ℕ)}, (∀ t ∈ ts, t.2.1 < n ∧ t.2.2 < n) → termSum Y ts = termSum Y' ts
  | [], _ => rfl
  | t :: ts, h => by
      have ih := termSum_congr_below hY (ts := ts) fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
      unfold termSum at ih ⊢
      simp only [List.map_cons, List.sum_cons, ih,
        hY _ (h t List.mem_cons_self).1, hY _ (h t List.mem_cons_self).2]

/-- A step that names only variables below n (`q.Below n`) has the same value on Y and Y' that
agree below n. -/
theorem QStep.eval_congr {q : QStep E} {n : ℕ} (hq : q.Below n)
    {Y Y' : ℕ → E} (hY : ∀ j, j < n → Y j = Y' j) : q.eval Y = q.eval Y' := by
  unfold QStep.eval
  rw [linSum_congr hY hq.1, termSum_congr_below hY hq.2]

namespace Steps
variable (S : Steps E) (Y0 : ℕ → E)

/-- Later steps do not change a variable below nc + l. -/
theorem fill_of_lt : ∀ (l k : ℕ) (j : ℕ), j < S.nc + l → S.fill Y0 (l + k) j = S.fill Y0 l j
  | _, 0, _, _ => rfl
  | l, k + 1, j, hj => by
      show Function.update (S.fill Y0 (l + k)) (S.nc + (l + k)) _ j = _
      rw [Function.update_of_ne (by omega)]
      exact fill_of_lt l k j hj

theorem vals_of_lt {l : ℕ} (hl : l ≤ S.na) {j : ℕ} (hj : j < S.nc + l) :
    S.vals Y0 j = S.fill Y0 l j := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hl
  unfold vals
  rw [hk]
  exact S.fill_of_lt Y0 l k j hj

theorem vals_aux (hT : S.Tri) {l : ℕ} (hl : l < S.na) :
    S.vals Y0 (S.nc + l) = (S.step l).eval (S.vals Y0) := by
  rw [S.vals_of_lt Y0 (l := l + 1) hl (by omega)]
  show Function.update (S.fill Y0 l) (S.nc + l) _ (S.nc + l) = _
  rw [Function.update_self]
  exact QStep.eval_congr (hT l hl.le) fun j hj => (S.vals_of_lt Y0 hl.le hj).symm

end Steps

theorem hold_vals : Spec.hold_vals := fun _ _ S Y0 hT =>
  ⟨⟨fun _ hl => S.vals_aux Y0 hT hl, rfl⟩,
    fun _ hj => S.vals_of_lt Y0 (l := 0) (Nat.zero_le _) (by omega)⟩

theorem out_of_hold : Spec.out_of_hold := by
  intro E _ S Y0 a aEnd hT h0 hH
  have key : ∀ l, l ≤ S.na → ∀ j, j < S.nc + l → a j = S.vals Y0 j := by
    intro l
    induction l with
    | zero =>
      exact fun _ j hj => (h0 j (by omega)).trans (S.vals_of_lt Y0 (l := 0) (Nat.zero_le _) hj).symm
    | succ l ih =>
      intro hl j hj
      by_cases hjl : j < S.nc + l
      · exact ih (by omega) j hjl
      · obtain rfl : j = S.nc + l := by omega
        rw [hH.1 l hl, S.vals_aux Y0 hT hl]
        exact QStep.eval_congr (hT l (by omega)) (ih (by omega))
  refine ⟨?_, key S.na le_rfl⟩
  rw [hH.2]
  exact QStep.eval_congr (hT S.na le_rfl) (key S.na le_rfl)

theorem val_list_sum {N : Type} [Fintype N] (y : N → E) (A : ℕ → Form N E) : ∀ ts : List (E × ℕ),
    Form.val y (ts.map fun t => t.1 • A t.2).sum = linSum (fun j => Form.val y (A j)) ts
  | [] => by simp [linSum]
  | t :: ts => by
      have ih := val_list_sum y A ts
      unfold linSum at ih ⊢
      simp only [List.map_cons, List.sum_cons, map_add, map_smul, smul_eq_mul, ih]

theorem ledger_true_iff : Spec.ledger_true_iff := by
  intro E N _ _ S A fEnd y hT
  have hov : ∀ j, j < S.nc + S.na → (S.ledger A fEnd).opv y j = Form.val y (A j) := by
    intro j hj
    show Form.val y (((List.range (S.nc + S.na)).map A).getD j 0) = _
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simp
  have hts : ∀ l, l ≤ S.na →
      termSum ((S.ledger A fEnd).opv y) (S.step l).quad =
        termSum (fun j => Form.val y (A j)) (S.step l).quad :=
    fun l hl =>
      termSum_congr_below (n := S.nc + S.na) hov fun t ht =>
        ⟨by have := ((hT l hl).2 t ht).1; omega, by have := ((hT l hl).2 t ht).2; omega⟩
  have hrow : ∀ l, Form.val y (S.rowForm A fEnd l) =
      Form.val y (if l < S.na then A (S.nc + l) else fEnd) - (S.step l).c0 -
        linSum (fun j => Form.val y (A j)) (S.step l).lin := by
    intro l
    unfold Steps.rowForm
    rw [map_sub, map_sub, Form.val_const, val_list_sum]
  have hiff : ∀ l, l ≤ S.na →
      (Form.val y (S.rowForm A fEnd l) = termSum ((S.ledger A fEnd).opv y) (S.step l).quad ↔
        Form.val y (if l < S.na then A (S.nc + l) else fEnd) =
          (S.step l).eval fun j => Form.val y (A j)) := by
    intro l hl
    rw [hrow, hts l hl]
    unfold QStep.eval
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  constructor
  · rintro ⟨_, h2⟩
    have h3 : ∀ l, l ≤ S.na →
        Form.val y (if l < S.na then A (S.nc + l) else fEnd) =
          (S.step l).eval fun j => Form.val y (A j) := fun l hl =>
      (hiff l hl).1
        (h2 (S.rowForm A fEnd l, (S.step l).quad)
          (List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩))
    refine ⟨fun l hl => ?_, ?_⟩
    · have := h3 l hl.le
      rwa [if_pos hl] at this
    · have := h3 S.na le_rfl
      rwa [if_neg (lt_irrefl _)] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun _ hf => absurd hf List.not_mem_nil, fun r hr => ?_⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
    have hl' : l ≤ S.na := by have := List.mem_range.1 hl; omega
    refine (hiff l hl').2 ?_
    by_cases hlt : l < S.na
    · rw [if_pos hlt]; exact h1 l hlt
    · obtain rfl : l = S.na := by omega
      rw [if_neg hlt]; exact h2

end Cb
