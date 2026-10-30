-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/LawEquiv.lean: two functions of the same uniform coins with the same distribution differ by a
bijection of the coins.

No protocol occurs in this file. The coins' type is finite and non-empty. Two such functions f and
f' take every value equally often (`cnt_fiber_eq`), so there is a bijection e of the coins with
f a = f' (e a) for all a (`exists_equiv_of_map_eq`).

Use: a statement "the law does not depend on the secret" is turned into a pointwise renaming of the
coins; `map_unif_prod_congr` (Prob/LawKit.lean) combines a renaming of a first coin with equal
distributions over a second. `exists_equiv_of_map_eq` is used in Cb/Gen/CodeProofs.lean
(`hides_iff_equiv`).

Limits: nothing on the form of the bijection; it is obtained by choice.
-/
import Prob.Count

namespace Prob
open scoped ENNReal

variable {α β : Type} [Fintype α] [Nonempty α]

/-- If f and f' have the same distribution under uniform coins, every value is taken equally
often. -/
theorem cnt_fiber_eq (f f' : α → β) (h : (unif α).map f = (unif α).map f') (y : β) :
    cnt (fun a => f a = y) = cnt (fun a => f' a = y) := by
  have h1 : pr ((unif α).map f) {y} = pr ((unif α).map f') {y} := by rw [h]
  rw [pr_map, pr_map] at h1
  have e1 : pr (unif α) (f ⁻¹' {y}) = (cnt (fun a => f a = y) : ℝ≥0∞) / Fintype.card α :=
    pr_unif_eq fun a => f a = y
  have e2 : pr (unif α) (f' ⁻¹' {y}) = (cnt (fun a => f' a = y) : ℝ≥0∞) / Fintype.card α :=
    pr_unif_eq fun a => f' a = y
  rw [e1, e2,
    ENNReal.div_eq_div_iff (card_ne_zero' α) (card_ne_top' α)
      (card_ne_zero' α) (card_ne_top' α)] at h1
  have h2 : (cnt (fun a => f a = y) : ℝ≥0∞) = cnt (fun a => f' a = y) := by
    have h3 := (ENNReal.mul_right_inj (card_ne_zero' α) (card_ne_top' α)).1 h1
    exact h3
  exact_mod_cast h2

/-- If f and f' have the same distribution under uniform coins, a bijection of the coins maps one
function to the other. -/
theorem exists_equiv_of_map_eq (f f' : α → β) (h : (unif α).map f = (unif α).map f') :
    ∃ e : α ≃ α, ∀ a, f a = f' (e a) := by
  classical
  have hc : ∀ y : β, Fintype.card {a // f a = y} = Fintype.card {a // f' a = y} := by
    intro y
    have := cnt_fiber_eq f f' h y
    rw [cnt_eq_card_filter, cnt_eq_card_filter] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact this
  let g : ∀ y : β, {a // f a = y} ≃ {a // f' a = y} := fun y => Fintype.equivOfCardEq (hc y)
  let e : α ≃ α :=
    (Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight g).trans (Equiv.sigmaFiberEquiv f'))
  refine ⟨e, fun a => ?_⟩
  show f a = f' ((g (f a) ⟨a, rfl⟩).1)
  exact ((g (f a) ⟨a, rfl⟩).2).symm

end Prob
