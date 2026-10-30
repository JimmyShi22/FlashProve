-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/ShapesMean.lean: what each of the three tests of Johnson/Desc/Own/Shapes.lean
checks, as a proposition in plain facts, with its proof in both directions.

Statements and proofs. It stands beside Johnson/Desc/Own/Shapes.lean: no block imports it, and no
byte of that file is turned.
Main names:
  `colsStand_iff`: colsStand key W cols xs says yes just if, at every number i at which both lists
    have a member, the i-th column bears the key, stands at the i-th position asked for, and has W
    words. It ends at the shorter list: of a column behind the end of xs, and of a position behind
    the end of cols, it asks nothing, and it does not compare the two lengths.
  `InOrder v`: the tensor v has at most 63 variables; it has no dense variable, or the slice of 2 ^
    (number of dense variables) values from `first` on lies inside its vector; each dense variable
    is one of the tensor's variables and has the pair (1, 1); no dense variable is named twice.
  `tensorInOrder_iff`: tensorInOrder v says yes just if InOrder v.
  `formFits_iff`: formFits f vars says yes just if each tensor of f has just vars variables and is
    in order, and each single entry of f has an index below 2 ^ vars.
Limits: No premise stands in the three statements. Whether these tests ask enough is not said here.
No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.Own.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

theorem colsStand_iff (key W : Nat) : ∀ (cols : List (Nat × Nat × List UInt64)) (xs : List Nat),
    colsStand key W cols xs = true ↔
      ∀ (i : Nat) (c : Nat × Nat × List UInt64) (x : Nat), cols[i]? = some c → xs[i]? = some x →
        c.1 = key ∧ c.2.1 = x ∧ c.2.2.length = W
  | [], xs => by
    constructor
    · intro _ i c x h
      cases h
    · intro _
      rfl
  | _ :: _, [] => by
    constructor
    · intro _ i c x _ h
      cases h
    · intro _
      rfl
  | c0 :: cols, x0 :: xs => by
    have ih := colsStand_iff key W cols xs
    unfold colsStand at ih ⊢
    rw [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, ih, Bool.and_eq_true,
      Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq]
    constructor
    · rintro ⟨⟨⟨a, b⟩, c⟩, h⟩ i c' x' hc hx
      cases i with
      | zero =>
        cases hc
        cases hx
        exact ⟨a, b, c⟩
      | succ i => exact h i c' x' hc hx
    · intro h
      obtain ⟨a, b, c⟩ := h 0 c0 x0 rfl rfl
      exact ⟨⟨⟨a, b⟩, c⟩, fun i c' x' hc hx => h (i + 1) c' x' hc hx⟩

/-- A tensor is in order. -/
def InOrder (v : OnBytes.Tensor) : Prop :=
  v.pairs.length ≤ 63 ∧
    (v.denseVars = [] ∨ v.first + 2 ^ v.denseVars.length ≤ v.values.size) ∧
    (∀ d ∈ v.denseVars, v.pairs[d]? = some (OnBytes.oneE, OnBytes.oneE)) ∧ v.denseVars.Nodup

theorem tensorInOrder_iff (v : OnBytes.Tensor) : tensorInOrder v = true ↔ InOrder v := by
  unfold tensorInOrder InOrder
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff,
    decide_eq_true_iff, decide_eq_true_iff, List.isEmpty_iff, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
    exact ⟨a, b, fun x hx => beq_iff_eq.1 (c x hx), d⟩
  · rintro ⟨a, b, c, d⟩
    exact ⟨⟨⟨a, b⟩, fun x hx => beq_iff_eq.2 (c x hx)⟩, d⟩

theorem formFits_iff (f : OnBytes.Form) (vars : Nat) :
    formFits f vars = true ↔
      (∀ v ∈ f.tensors, v.pairs.length = vars ∧ InOrder v) ∧ ∀ e ∈ f.entries, e.1 < 2 ^ vars := by
  unfold formFits
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨a, b⟩
    refine ⟨fun v hv => ?_, fun e he => of_decide_eq_true (b e he)⟩
    have h := a v hv
    rw [Bool.and_eq_true, beq_iff_eq, tensorInOrder_iff] at h
    exact h
  · rintro ⟨a, b⟩
    refine ⟨fun v hv => ?_, fun e he => decide_eq_true (b e he)⟩
    rw [Bool.and_eq_true, beq_iff_eq, tensorInOrder_iff]
    exact a v hv

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.colsStand_iff
#print axioms VerifiableInference.Desc.Own.tensorInOrder_iff
#print axioms VerifiableInference.Desc.Own.formFits_iff
