/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/Combinatorics/Enumerative/DoubleCounting.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 3 of the 6 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Double counting after deleting part of the right-hand side

Let `r : α → β → Prop` be a relation between finite sets `s : Finset α` and `t : Finset β`, and
suppose every `a ∈ s` is related to at least `A` elements of `t`. Delete a set `u` of elements of
`β`. Each `a ∈ s` loses at most `#u` of its incidences, so it keeps at least `A - #u` incidences in
`t \ u`. Summing over `s` and double counting gives

  `#s * (A - #u) ≤ ∑ b ∈ t \ u, #{a ∈ s | r a b}`.

In the agreement arguments that use this bound, `s` is a set of candidate points, `t` is a set of
positions (cuts), `r a b` says that `a` agrees with the data at position `b`, and `u` is the set of
positions that must be discarded (for example cuts that vanish identically).

## Main statements

* `Finset.card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff` — deleting `u` removes at most
  `#u` incidences of a single element.
* `Finset.card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff` — the sharp deletion estimate above.
* `Finset.card_mul_sub_add_one_le_sum_card_bipartiteBelow_sdiff` — the weaker form
  `#s * (A - k + 1) ≤ …` under `#u < k` and `k ≤ A`.
* `Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow` and
  `Finset.card_mul_sub_add_one_le_sum_compl_card_bipartiteBelow` — the same two bounds with
  `t = univ` in a finite type, summing over `uᶜ`.
* `Finset.card_mul_sub_le_card_mul_of_card_bad_le` — the deleted set may depend on the element of
  `s`: if each `a ∈ s` is related to all of `t` outside a set `bad a` with `#(bad a) ≤ H`, and each
  `b ∈ t` is related to at most `n` elements of `s`, then `#s * (#t - H) ≤ #t * n`.

## Proof outline

For a single `a`, `{b ∈ t | r a b} \ u = {b ∈ t \ u | r a b}`, and Mathlib's `Finset.le_card_sdiff`
bounds the left side below by `#{b ∈ t | r a b} - #u`. Summing over `a ∈ s` and applying
`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` converts the sum over `s` into a sum of
fibre sizes over `t \ u`. The `A - k + 1` form follows from the sharp form by monotonicity of
truncated subtraction.
-/

namespace Finset

variable {α β : Type*} (r : α → β → Prop)

/-- Deleting a finite set `u` from `t` removes at most `#u` of the elements of `t` related to
`a`: `#{b ∈ t | r a b} - #u ≤ #{b ∈ t \ u | r a b}`. No relation between `u` and `t` is assumed;
elements of `u` outside `t`, or not related to `a`, only make the bound weaker. -/
theorem card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff [DecidableEq β]
    (t u : Finset β) (a : α) [DecidablePred (r a)] :
    #(t.bipartiteAbove r a) - #u ≤ #((t \ u).bipartiteAbove r a) := by
  have h : (t \ u).bipartiteAbove r a = t.bipartiteAbove r a \ u := by
    ext b
    simp only [mem_bipartiteAbove, mem_sdiff]
    tauto
  rw [h]
  exact le_card_sdiff u _

/-- **Double counting after deletion.** If every `a ∈ s` is related to at least `A` elements of
`t`, then after deleting any finite set `u` the fibres over `t \ u` still carry at least
`#s * (A - #u)` incidences:

  `#s * (A - #u) ≤ ∑ b ∈ t \ u, #{a ∈ s | r a b}`.

No hypothesis relates `A` to `#u`. When `#u ≥ A` the left side is `0` because subtraction on `ℕ`
is truncated, and the statement holds trivially. The set `u` need not be contained in `t`. -/
theorem card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff [DecidableEq β]
    [∀ a b, Decidable (r a b)] {s : Finset α} {t : Finset β} (u : Finset β) {A : ℕ}
    (hA : ∀ a ∈ s, A ≤ #(t.bipartiteAbove r a)) :
    #s * (A - #u) ≤ ∑ b ∈ t \ u, #(s.bipartiteBelow r b) := by
  calc
    #s * (A - #u) = ∑ _a ∈ s, (A - #u) := (sum_const_nat fun _ _ ↦ rfl).symm
    _ ≤ ∑ a ∈ s, #((t \ u).bipartiteAbove r a) := by
      refine sum_le_sum fun a ha ↦ ?_
      exact (Nat.sub_le_sub_right (hA a ha) _).trans
        (card_bipartiteAbove_sub_card_le_card_bipartiteAbove_sdiff r t u a)
    _ = ∑ b ∈ t \ u, #(s.bipartiteBelow r b) :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r

/-- `card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff` for `t = univ` in a finite type: if every
`a ∈ s` is related to at least `A` elements of `β`, then for every `u : Finset β`

  `#s * (A - #u) ≤ ∑ b ∈ uᶜ, #{a ∈ s | r a b}`. -/
theorem card_mul_sub_card_le_sum_compl_card_bipartiteBelow [Fintype β] [DecidableEq β]
    [∀ a b, Decidable (r a b)] {s : Finset α} (u : Finset β) {A : ℕ}
    (hA : ∀ a ∈ s, A ≤ #((univ : Finset β).bipartiteAbove r a)) :
    #s * (A - #u) ≤ ∑ b ∈ uᶜ, #(s.bipartiteBelow r b) := by
  simpa only [compl_eq_univ_sdiff] using
    card_mul_sub_card_le_sum_card_bipartiteBelow_sdiff r u hA

end Finset
