-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedBatch.lean: how many batching elements turn a false list of claims into a true
one form.

The claims of a sub-proof go into one equation, the member (e, claim) under the weight theta^e
(batchAt, LedJoint.lean). If no two exponents are equal, all are at most D, and some claim fails on
the entries m, then at most D elements theta make the one form hold on m. The bound is the largest
exponent, not the number of claims: the exponents may have gaps.

Main theorems: card_batchAt_le, cnt_batchAt_le (the same in the library's count Prob.cnt),
cnt_zip_le (for a ledger under a written list of exponents: the count that a block which draws
theta needs), zip_holds.

What this file does not claim. The entries m and the list are fixed before theta: a list whose forms
hold theta themselves is not covered.


-/
import OnBytes.Tie.Pv.Led.LedJoint
import Prob.Cnt
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole Polynomial

variable {E : Type} [Field E]

theorem eval_monomials (x : E) (v : List (Nat × E)) :
    eval x (v.map fun q => monomial q.1 q.2).sum = (v.map fun q => x ^ q.1 * q.2).sum := by
  induction v with
  | nil => simp
  | cons q v ih => simp [eval_add, eval_monomial, ih, mul_comm]

theorem coeff_monomials_of_not_mem (e : Nat) (v : List (Nat × E)) (h : e ∉ v.map Prod.fst) :
    coeff (v.map fun q => monomial q.1 q.2).sum e = 0 := by
  induction v with
  | nil => simp
  | cons q v ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.map_cons, List.sum_cons, coeff_add, coeff_monomial, ih h.2, add_zero]
    exact if_neg fun k => h.1 k.symm

theorem coeff_monomials (e : Nat) (g : E) (v : List (Nat × E)) (nd : (v.map Prod.fst).Nodup)
    (h : (e, g) ∈ v) : coeff (v.map fun q => monomial q.1 q.2).sum e = g := by
  induction v with
  | nil => cases h
  | cons q v ih =>
    simp only [List.map_cons, List.nodup_cons] at nd
    simp only [List.map_cons, List.sum_cons, coeff_add, coeff_monomial]
    rcases List.mem_cons.1 h with rfl | h'
    · have hn : e ∉ v.map Prod.fst := nd.1
      rw [coeff_monomials_of_not_mem e v hn]
      simp
    · have he : e ∈ v.map Prod.fst := List.mem_map.2 ⟨(e, g), h', rfl⟩
      have ne : q.1 ≠ e := fun k => nd.1 (by rw [k]; exact he)
      rw [if_neg ne, ih nd.2 h', zero_add]

theorem natDegree_monomials (D : Nat) (v : List (Nat × E)) (h : ∀ q ∈ v, q.1 ≤ D) :
    natDegree (v.map fun q => monomial q.1 q.2).sum ≤ D := by
  induction v with
  | nil => simp
  | cons q v ih =>
    simp only [List.map_cons, List.sum_cons]
    exact natDegree_add_le_of_degree_le
      ((natDegree_monomial_le _).trans (h q (List.mem_cons_self ..)))
      (ih fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- A sum of x^e times a value, with exponents that differ and are at most D and with a value that
is not 0, is 0 at no more than D elements x. -/
theorem card_zeros_le [Fintype E] [DecidableEq E] (v : List (Nat × E))
    (nd : (v.map Prod.fst).Nodup) (D : Nat) (hD : ∀ q ∈ v, q.1 ≤ D) (bad : ∃ q ∈ v, q.2 ≠ 0) :
    (Finset.univ.filter fun x : E => (v.map fun q => x ^ q.1 * q.2).sum = 0).card ≤ D := by
  obtain ⟨q, hq, hq0⟩ := bad
  have hP : (v.map fun q => monomial q.1 q.2).sum ≠ 0 := by
    intro h0
    have := coeff_monomials q.1 q.2 v nd hq
    rw [h0, coeff_zero] at this
    exact hq0 this.symm
  calc (Finset.univ.filter fun x : E => (v.map fun q => x ^ q.1 * q.2).sum = 0).card
      ≤ (v.map fun q => monomial q.1 q.2).sum.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_monomials]
        exact hx.2
    _ ≤ Multiset.card (v.map fun q => monomial q.1 q.2).sum.roots := Multiset.toFinset_card_le _
    _ ≤ natDegree (v.map fun q => monomial q.1 q.2).sum := card_roots' _
    _ ≤ D := natDegree_monomials D v hD

variable {J : Type} [Fintype J]

/-- A false list of claims gives a true one form at no more than D elements. -/
theorem card_batchAt_le [Fintype E] [DecidableEq E] (L : List (Nat × Form E J)) (m : J → E)
    (nd : (L.map Prod.fst).Nodup) (D : Nat) (hD : ∀ p ∈ L, p.1 ≤ D)
    (bad : ∃ p ∈ L, ¬ p.2.Holds m) :
    (Finset.univ.filter fun x : E => (batchAt x L).gap m = 0).card ≤ D := by
  have e : ∀ x : E, (batchAt x L).gap m =
      ((L.map fun p => (p.1, p.2.gap m)).map fun q => x ^ q.1 * q.2).sum := by
    intro x
    rw [batchAt_gap, List.map_map]
    rfl
  simp only [e]
  apply card_zeros_le
  · simpa [List.map_map, Function.comp_def] using nd
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hD p hp
  · obtain ⟨p, hp, hb⟩ := bad
    exact ⟨(p.1, p.2.gap m), List.mem_map.2 ⟨p, hp, rfl⟩, hb⟩

/-- The same in the library's count. -/
theorem cnt_batchAt_le [Fintype E] (L : List (Nat × Form E J)) (m : J → E)
    (nd : (L.map Prod.fst).Nodup) (D : Nat) (hD : ∀ p ∈ L, p.1 ≤ D)
    (bad : ∃ p ∈ L, ¬ p.2.Holds m) :
    Prob.cnt (fun x : E => (batchAt x L).Holds m) ≤ D := by
  classical
  have h := card_batchAt_le L m nd D hD bad
  unfold Prob.cnt
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

/-! ## A ledger under a written list of exponents -/

theorem zip_fst_sublist {α : Type} : ∀ (es : List Nat) (L : List α),
    ((es.zip L).map Prod.fst).Sublist es
  | [], _ => by simp
  | _ :: _, [] => by simp
  | e :: es, _ :: L => by
    simp only [List.zip_cons_cons, List.map_cons]
    exact (zip_fst_sublist es L).cons₂ e

theorem mem_zip_of_mem {α : Type} : ∀ (es : List Nat) (L : List α), L.length ≤ es.length →
    ∀ f ∈ L, ∃ e, (e, f) ∈ es.zip L
  | _, [], _, f, hf => by cases hf
  | [], _ :: _, h, _, _ => by simp at h
  | e :: es, g :: L, h, f, hf => by
    rcases List.mem_cons.1 hf with rfl | hf'
    · exact ⟨e, by simp⟩
    · obtain ⟨e', he'⟩ := mem_zip_of_mem es L (by simpa using h) f hf'
      exact ⟨e', by simp [he']⟩

/-- The count that a block which draws the batching element needs. The claims of a ledger L get the
exponents of a written list es, in order. If the exponents differ, none is above D, there are
enough of them, and some claim of L fails on m, then the one form holds at no more than D
elements. -/
theorem cnt_zip_le [Fintype E] (es : List Nat) (L : Ledger E J) (m : J → E) (nd : es.Nodup)
    (D : Nat) (hD : ∀ e ∈ es, e ≤ D) (hl : L.length ≤ es.length) (bad : ¬ L.Holds m) :
    Prob.cnt (fun x : E => (batchAt x (es.zip L)).Holds m) ≤ D := by
  apply cnt_batchAt_le
  · exact nd.sublist (zip_fst_sublist es L)
  · intro p hp
    exact hD p.1 ((zip_fst_sublist es L).subset (List.mem_map.2 ⟨p, hp, rfl⟩))
  · by_contra k
    apply bad
    intro f hf
    obtain ⟨e, he⟩ := mem_zip_of_mem es L hl f hf
    by_contra kf
    exact k ⟨(e, f), he, kf⟩

/-- What holds of m before the batching element holds behind it, at every element. -/
theorem zip_holds (es : List Nat) (L : Ledger E J) (m : J → E) (x : E) (h : L.Holds m) :
    (batchAt x (es.zip L)).Holds m := by
  show (batchAt x (es.zip L)).gap m = 0
  rw [batchAt_gap]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hv
  have : q.2.gap m = 0 := h q.2 (List.of_mem_zip hq).2
  rw [this, mul_zero]

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.cnt_batchAt_le
#print axioms OnBytes.Road.Rows.cnt_zip_le
#print axioms OnBytes.Road.Rows.zip_holds
