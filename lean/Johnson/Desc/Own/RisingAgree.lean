-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/RisingAgree.lean: of rising (Johnson/Desc/Own/Rising.lean): that it is the format's
library's Fmt.increasing at all arguments, and what it checks. No block imports this file.
  rising_agrees   Fmt.increasing l = rising l.
  rising_iff      rising l = true just where the list is pairwise rising: of any two places the
                  later holds the greater number.
  rising_lt       the same by places: i < j < l.length → l[i] < l[j].
Nothing on soundness.

-/
import Johnson.Desc.Own.Rising
import Fmt.Rules8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

theorem rising_agrees : ∀ l : List Nat, Fmt.increasing l = rising l
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    simp only [Fmt.increasing, rising, rising_agrees (b :: l)]

/-- Where a list rises from a on, a is below every number of it. -/
theorem below_all : ∀ (l : List Nat) (a : Nat), rising (a :: l) = true → ∀ x ∈ l, a < x
  | [], _, _, x, hx => by cases hx
  | b :: l, a, h, x, hx => by
    simp only [rising, Bool.and_eq_true, decide_eq_true_eq] at h
    cases hx with
    | head => exact h.1
    | tail _ hx' => exact Nat.lt_trans h.1 (below_all l b h.2 x hx')

theorem rising_iff : ∀ l : List Nat, rising l = true ↔ l.Pairwise (· < ·)
  | [] => by simp [rising]
  | [a] => by simp [rising]
  | a :: b :: l => by
    constructor
    · intro h
      have h' := h
      simp only [rising, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact List.Pairwise.cons (below_all (b :: l) a h) ((rising_iff (b :: l)).1 h'.2)
    · intro h
      cases h with
      | cons h1 h2 =>
        simp only [rising, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨h1 b (List.mem_cons_self ..), (rising_iff (b :: l)).2 h2⟩

theorem rising_lt (l : List Nat) (h : rising l = true) (i j : Nat) (hij : i < j)
    (hj : j < l.length) : l[i]'(Nat.lt_trans hij hj) < l[j] :=
  (List.pairwise_iff_getElem.1 ((rising_iff l).1 h)) i j (Nat.lt_trans hij hj) hj hij

end VerifiableInference.Desc.Own
