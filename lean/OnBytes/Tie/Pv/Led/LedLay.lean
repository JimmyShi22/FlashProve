-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedLay.lean: what the readings of a lay give at single entries.

LedJoint.lean reads the committed entries m : J → E by addresses: Lay.maskAt, Lay.cellAt and
Lay.entryAt are sums over all entries. This file says what these sums are.

Main theorems: Lay.cellAt_addr, Lay.maskAt_addr (at the address of an entry i the reading is m i);
Lay.cellAt_none, Lay.maskAt_none (at an address that no entry has it is 0); Lay.entryAt_unit (a
virtual row with the weight 1 on one row is that row); Lay.entryAt_sum (an entry of a virtual row is
the sum over the rows of weight times cell, if all rows of the array lie below R).


-/
import OnBytes.Tie.Pv.Led.LedJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open TWhole

variable {E J : Type} [Field E] [Fintype J] (Y : Lay J) (m : J → E)

theorem Lay.sum_at (a : Addr) (i : J) (h : Y.addr i = a) :
    (∑ k, if Y.addr k = a then m k else 0) = m i := by
  classical
  have e : ∀ k, (Y.addr k = a) ↔ k = i :=
    fun k => ⟨fun hk => Y.inj (hk.trans h.symm), fun hk => hk ▸ h⟩
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem Lay.sum_none (a : Addr) (h : ∀ k, Y.addr k ≠ a) :
    (∑ k, if Y.addr k = a then m k else 0) = 0 :=
  Finset.sum_eq_zero fun k _ => if_neg (h k)

/-- At the address of an entry, the reading of a cell is the entry. -/
theorem Lay.cellAt_addr (t r c : Nat) (i : J) (h : Y.addr i = .cell t r c) :
    Y.cellAt m t r c = m i := Y.sum_at m _ i h

/-- At the address of an entry, the reading of the mask row is the entry. -/
theorem Lay.maskAt_addr (j : Nat) (i : J) (h : Y.addr i = .mask j) : Y.maskAt m j = m i :=
  Y.sum_at m _ i h

theorem Lay.cellAt_none (t r c : Nat) (h : ∀ k, Y.addr k ≠ .cell t r c) : Y.cellAt m t r c = 0 :=
  Y.sum_none m _ h

theorem Lay.maskAt_none (j : Nat) (h : ∀ k, Y.addr k ≠ .mask j) : Y.maskAt m j = 0 :=
  Y.sum_none m _ h

omit [Fintype J] in
/-- One summand of an entry of a virtual row, as a sum over the rows below R. -/
theorem Lay.colW_mul (t : Nat) (wts : Nat → E) (col R : Nat)
    (hR : ∀ k r, Y.addr k = .cell t r col → r < R) (k : J) :
    Y.colW t wts col k * m k =
      ∑ r ∈ Finset.range R, wts r * (if Y.addr k = .cell t r col then m k else 0) := by
  unfold Lay.colW
  cases h : Y.addr k with
  | mask j => simp
  | cell a r' c =>
    by_cases hc : a = t ∧ c = col
    · obtain ⟨rfl, rfl⟩ := hc
      have hr : r' < R := hR k r' h
      have e : ∀ r, (Addr.cell a r' c = Addr.cell a r c) ↔ r = r' := fun r =>
        ⟨fun q => by
          simp only [Addr.cell.injEq, true_and, and_true] at q
          exact q.symm, fun q => by rw [q]⟩
      simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range, hr, if_true,
        and_self]
    · have e : ∀ r, Addr.cell a r' c ≠ Addr.cell t r col := fun r q => by
        simp only [Addr.cell.injEq] at q
        exact hc ⟨q.1, q.2.2⟩
      simp only [hc, if_false, zero_mul, e, mul_zero, Finset.sum_const_zero]

/-- An entry of a virtual row is the sum over the rows of weight times cell. -/
theorem Lay.entryAt_sum (t : Nat) (wts : Nat → E) (col R : Nat)
    (hR : ∀ k r, Y.addr k = .cell t r col → r < R) :
    Y.entryAt m t wts col = ∑ r ∈ Finset.range R, wts r * Y.cellAt m t r col := by
  unfold Lay.entryAt Lay.cellAt
  simp only [Y.colW_mul m t wts col R hR, Finset.mul_sum]
  exact Finset.sum_comm

/-- A virtual row with the weight 1 on row r0 and 0 on the others is row r0. -/
theorem Lay.entryAt_unit (t r0 col : Nat) :
    Y.entryAt m t (fun r => if r = r0 then 1 else 0) col = Y.cellAt m t r0 col := by
  unfold Lay.entryAt Lay.cellAt Lay.colW
  refine Finset.sum_congr rfl fun k _ => ?_
  cases h : Y.addr k with
  | mask j => simp
  | cell a r c =>
    by_cases hc : a = t ∧ r = r0 ∧ c = col
    · obtain ⟨rfl, rfl, rfl⟩ := hc
      simp
    · have e : Addr.cell a r c ≠ Addr.cell t r0 col := fun q => by
        simp only [Addr.cell.injEq] at q
        exact hc q
      rw [if_neg e]
      by_cases h1 : a = t ∧ c = col
      · have h2 : r ≠ r0 := fun q => hc ⟨h1.1, q, h1.2⟩
        simp [h1, h2]
      · simp [h1]

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.Lay.cellAt_addr
#print axioms OnBytes.Road.Rows.Lay.maskAt_addr
#print axioms OnBytes.Road.Rows.Lay.entryAt_sum
#print axioms OnBytes.Road.Rows.Lay.entryAt_unit
