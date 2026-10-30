-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BatCount.lean: how many drawn elements can save a false row in the
batching of the rows on a group (`Bat.combine`, OnBytes/Iop/Bat.lean). Definitions, statements and
proofs.

  `hornerPoly l`: the polynomial a_0 + a_1 X + a_2 X^2 + .. of a list; `eval_hornerPoly`: its value
    at y is `hornerSum y l`; `natDegree_hornerPoly`, `hornerPoly_ne_zero`.
  `card_hornerSum_zero`: if one entry of a list is not 0, at most (the list's length - 1) elements y
    of a finite field make the sum under the powers of y vanish.
  `combine_few`: THE TABLES ARE FIXED FIRST. If one of the rows does not hold on them, then for at
    most (the number of rows - 1) values of the drawn element does the batching return a row that
    holds on the group's tables.
It rests on `combine_defect` (BatApply.lean, beside this file).

Limits. ONE OBJECT: the count is at fixed tables tab, TM, TZ. Nothing says which tables a prover is
bound to, that there is only one such object, or how a word that is only close to a code is read as
a table: so this is no bound on a prover's chance. The conditions of BatApply.lean are asked. The
count is over values of the field, not over what a round of a file draws.

-/
import Johnson.Desc.First.Close.Law.BatApply
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes
open Polynomial

variable {K : Type} [Field K]

/-- The polynomial a_0 + a_1 X + a_2 X^2 + .. of a list. -/
noncomputable def hornerPoly : List K → K[X]
  | [] => 0
  | a :: l => C a + X * hornerPoly l

theorem eval_hornerPoly (y : K) : ∀ l : List K, (hornerPoly l).eval y = hornerSum y l
  | [] => by simp [hornerPoly, hornerSum]
  | a :: l => by simp [hornerPoly, hornerSum, eval_hornerPoly y l]

theorem natDegree_hornerPoly : ∀ l : List K, (hornerPoly l).natDegree ≤ l.length - 1
  | [] => by simp [hornerPoly]
  | [a] => by simp [hornerPoly]
  | a :: b :: l => by
    have ih := natDegree_hornerPoly (b :: l)
    have h1 : (X * hornerPoly (b :: l)).natDegree ≤ 1 + (hornerPoly (b :: l)).natDegree :=
      natDegree_mul_le.trans (Nat.add_le_add_right natDegree_X_le _)
    have h2 : (C a + X * hornerPoly (b :: l)).natDegree ≤
        max (C a).natDegree (X * hornerPoly (b :: l)).natDegree := natDegree_add_le _ _
    show (C a + X * hornerPoly (b :: l)).natDegree ≤ _
    rw [natDegree_C] at h2
    simp only [List.length_cons] at ih ⊢
    omega

theorem hornerPoly_ne_zero : ∀ l : List K, (∃ a ∈ l, a ≠ 0) → hornerPoly l ≠ 0
  | [], h => by
    obtain ⟨a, ha, -⟩ := h
    cases ha
  | a :: l, h => by
    intro h0
    have c0 : (hornerPoly (a :: l)).coeff 0 = a := by simp [hornerPoly]
    rw [h0, coeff_zero] at c0
    have hq : hornerPoly l = 0 := by
      have : X * hornerPoly l = 0 := by
        have h1 : C a + X * hornerPoly l = 0 := h0
        rw [← c0, C_0, zero_add] at h1
        exact h1
      exact (mul_eq_zero.1 this).resolve_left X_ne_zero
    obtain ⟨b, hb, hb0⟩ := h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hb0 c0.symm
    · exact hornerPoly_ne_zero l ⟨b, hb, hb0⟩ hq

/-- **If one entry of a list is not 0, at most (the list's length - 1) elements y make the sum under
the powers of y vanish.** -/
theorem card_hornerSum_zero [Fintype K] [DecidableEq K] (l : List K) (h : ∃ a ∈ l, a ≠ 0) :
    (Finset.univ.filter fun y : K => hornerSum y l = 0).card ≤ l.length - 1 := by
  have hp := hornerPoly_ne_zero l h
  have hsub : (Finset.univ.filter fun y : K => hornerSum y l = 0) ⊆
      (hornerPoly l).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot.def, eval_hornerPoly]
    exact (Finset.mem_filter.1 hy).2
  calc (Finset.univ.filter fun y : K => hornerSum y l = 0).card
      ≤ (hornerPoly l).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (hornerPoly l).roots := Multiset.toFinset_card_le _
    _ ≤ (hornerPoly l).natDegree := card_roots' _
    _ ≤ l.length - 1 := natDegree_hornerPoly l

open Classical in
/-- **At fixed tables, a false row is saved by few drawn elements.** -/
theorem combine_few [Fintype K] (ρ : Model.Reading K) (S : Statement) (g : Nat) (input : RunInput)
    (hM : MainBlocksOk S input.layout) (hZ : MaskBlocksOk S input.layout)
    (hr : ∀ r ∈ input.rows.toList, RowFits S r ∧ MaskFits S input.layout r) (N : ℕ)
    (hN : input.layout.top ≤ N) (tab : ℕ → Part → ℕ → K) (TM TZ : ℕ → K)
    (hTM : ∀ o J, mainWeight (K := K) S input.layout o J ≠ 0 →
      TM J = tab o .main (mainBack S input.layout o J))
    (hTZ : ∀ o J, maskWeight (K := K) S input.layout o J ≠ 0 →
      TZ J = tab o .mask (maskBack S input.layout o J))
    (hbad : ∃ r ∈ input.rows.toList, rowSumIn ρ S input.layout N tab r ≠ ρ.val r.target) :
    (Finset.univ.filter fun y : K => ∃ x out, ρ.val x = y ∧ Bat.combine S g input x = some out ∧
      groupSum ρ S input.layout N tab TM TZ out = ρ.val out.target).card ≤
        input.rows.size - 1 := by
  have hl : (input.rows.toList.map fun r =>
      rowSumIn ρ S input.layout N tab r - ρ.val r.target).length = input.rows.size := by simp
  rw [← hl]
  refine (Finset.card_le_card ?_).trans (card_hornerSum_zero _ ?_)
  · intro y hy
    obtain ⟨x, out, rfl, hc, he⟩ := (Finset.mem_filter.1 hy).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← combine_defect ρ S g input x out hc hM hZ hr N hN tab TM TZ hTM hTZ, he, sub_self]
  · obtain ⟨r, hm, hne⟩ := hbad
    exact ⟨_, List.mem_map.2 ⟨r, hm, rfl⟩, sub_ne_zero.2 hne⟩

end OnBytes

#print axioms OnBytes.card_hornerSum_zero
#print axioms OnBytes.combine_few
