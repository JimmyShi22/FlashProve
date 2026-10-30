-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/LevStdSim.lean: the places LevPl.std of a level are the fresh
mask entries of the course over the field, in the course's order.

The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean); that the program's run, read in the field, is this
course is not shown in this file.

Statements and proofs. Johnson/Desc/First/Look/KeyLaw/Mid/LevSimA.lean reads the places of a level's
coefficients off the list of fresh mask entries that the course's sumcheck is given (wvF, wcF).
Cb/Pv/KeyLookup/LevStd.lean gives the places as a function of the public record (Lev.offW,
LevPl.std). This file shows that they agree where the fresh entries are slots e b n
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean): the entries number b, .., b + n - 1 in the order
e.

Main names:
  slots_getD: entry i < n of slots e b n is e (b + i). slots_drop: slots e b n without its first two
    is slots e (b + 2) (n - 2).
  wvF_slots, wcF_slots: for 2 k + 3 ≤ n: wvF sl k (slots e b n) r t = sl (e (b + offW k (nmV k r
    t))) and wcF sl k (slots e b n) = sl (e (b + offW k (nmC k))).
  tabD_wv, tabD_wc, tabD_c: at LevPl.std A (sl ∘ e) ix bK bI bT the table's level l has the places
    wvF, wcF of slots e (bT + grp mu l) (2 (mu + l) + 5), and its two values' places are that list's
    entries 2 (mu + l) + 3 and + 4.

Limits: no premise but 2 k + 3 ≤ n. The key levels' like is not stated here.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimA
import Cb.Pv.KeyLookup.LevStd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev

theorem slots_getD (e : ℕ → Slot) (b n i : ℕ) (h : i < n) (d : Slot) :
    (slots e b n).getD i d = e (b + i) := by
  unfold slots
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem slots_drop (e : ℕ → Slot) (b n : ℕ) : (slots e b (n + 2)).drop 2 = slots e (b + 2) n := by
  unfold slots
  rw [← List.map_drop]
  have h : (List.range (n + 2)).drop 2 = (List.range n).map (· + 2) := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_drop, List.getElem?_map]
    by_cases hi : i < n
    · rw [List.getElem?_range (by omega), List.getElem?_range hi]
      show some (2 + i) = some (i + 2)
      rw [Nat.add_comm]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      rfl
  rw [h, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show e (b + (i + 2)) = e (b + 2 + i)
  congr 1
  omega

variable {J : Type} [DecidableEq J] (sl : Slot → J)

omit [DecidableEq J] in
theorem wcF_slots (e : ℕ → Slot) : ∀ (k b n : ℕ), 2 * k + 3 ≤ n →
    wcF sl k (slots e b n) = sl (e (b + offW (E := GE) k (nmC GE k)))
  | 0, b, n, h => by
    show sl ((slots e b n).getD 0 ⟨0, 0⟩) = _
    rw [slots_getD e b n 0 (by omega)]
    rfl
  | k + 1, b, n, h => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    show wcF sl k ((slots e b (n' + 2)).drop 2) = sl (e (b + (2 + offW (E := GE) k (nmC GE k))))
    rw [slots_drop, wcF_slots e k (b + 2) n' (by omega), Nat.add_assoc]

omit [DecidableEq J] in
theorem wvF_slots (e : ℕ → Slot) (t : Fin 2) : ∀ (k b n r : ℕ), 2 * k + 3 ≤ n →
    wvF sl k (slots e b n) r t = sl (e (b + offW (E := GE) k (nmV GE k r t)))
  | 0, b, n, r, h => by
    have ht : t.val < 2 := t.isLt
    show sl ((slots e b n).getD (1 + t.val) ⟨0, 0⟩) = _
    rw [slots_getD e b n (1 + t.val) (by omega)]
    rfl
  | k + 1, b, n, 0, h => by
    have ht : t.val < 2 := t.isLt
    show sl ((slots e b n).getD t.val ⟨0, 0⟩) = _
    rw [slots_getD e b n t.val (by omega)]
    rfl
  | k + 1, b, n, r + 1, h => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    show wvF sl k ((slots e b (n' + 2)).drop 2) r t =
      sl (e (b + (2 + offW (E := GE) k (nmV GE k r t))))
    rw [slots_drop, wvF_slots e t k (b + 2) n' r (by omega), Nat.add_assoc]

section
variable (A : Dat GE) (sl : Slot → A.J) (e : ℕ → Slot) (ix : ℕ → A.J) (bK bI bT : ℕ)

theorem tabD_wv (l : ℕ) :
    (A.tabD (LevPl.std A (fun k => sl (e k)) ix bK bI bT)).wv l =
      wvF sl (A.mu + l) (slots e (bT + grp A.mu l) (2 * (A.mu + l) + 5)) :=
  funext fun r => funext fun t =>
    (wvF_slots sl e t (A.mu + l) (bT + grp A.mu l) (2 * (A.mu + l) + 5) r (by omega)).symm

theorem tabD_wc (l : ℕ) :
    (A.tabD (LevPl.std A (fun k => sl (e k)) ix bK bI bT)).wc l =
      wcF sl (A.mu + l) (slots e (bT + grp A.mu l) (2 * (A.mu + l) + 5)) :=
  (wcF_slots sl e (A.mu + l) (bT + grp A.mu l) (2 * (A.mu + l) + 5) (by omega)).symm

theorem tabD_c (l : ℕ) (b : Bool) :
    (A.tabD (LevPl.std A (fun k => sl (e k)) ix bK bI bT)).c l b =
      sl ((slots e (bT + grp A.mu l) (2 * (A.mu + l) + 5)).getD
        (2 * (A.mu + l) + 3 + (if b then 1 else 0)) ⟨0, 0⟩) := by
  rw [slots_getD e _ _ _ (by cases b <;> simp)]
  show sl (e (bT + grp A.mu l + (2 * (A.mu + l) + 3) + (if b then 1 else 0))) = _
  rw [Nat.add_assoc]

end
end Lk6.Mid

#print axioms Lk6.Mid.wvF_slots
#print axioms Lk6.Mid.wcF_slots
#print axioms Lk6.Mid.tabD_wv
#print axioms Lk6.Mid.tabD_wc
#print axioms Lk6.Mid.tabD_c
