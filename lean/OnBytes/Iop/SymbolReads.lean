-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/SymbolReads.lean: what the program's folded symbols read as.

After a fold the verifier reads the folded rows at listed positions: it puts the opened columns'
symbols into tables and folds each table at the fold's point (OnBytes/Iop/Fold.lean).
OnBytes/Iop/SymbolLaws.lean says which entry of the result is which folded table. This file says
what a folded table reads as in any commutative ring K under a reading of the program's field
elements (Model.Reading): the sum over the rows of a row's weight at the point times the row's
entry. It is stated once, for `foldLow`, and used for the main table, the mask table and the fresh
mask's column.

Main definition: `eqVal` (the weight of a row at a point).
Main theorems: `foldLowOnce_val`, `foldLow_val`, `foldLow_all`, `singleRowsSymbols_val`.

Not claimed. Nothing on a call that fails. Nothing on where the opened columns come from. Nothing
for s.masks > 2: the function can then succeed with fewer entries for a position than s.rows. The
equations are between readings, not between the program's words, but for the kept symbols. No
theorem of OnBytes/Slice/ or OnBytes/Tie/ rests on this file's main theorems:
OnBytes/Slice/BlkFoldVec.lean proves the laws on foldLow again for the one reading Model.Reading.gl.
-/
import OnBytes.Iop.RowLaws
import OnBytes.Iop.SymbolLaws

namespace OnBytes

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## The weight of a row at a point -/

/-- The weight of row number b at the point g: the product over the coordinates of g, where
coordinate number j (from 0) gives x if bit j of b is 1 and 1 - x if it is 0. This is the
multilinear equality polynomial of b's low bits at g. Bits of b from |g| on are not read. -/
def eqVal (g : List E) (b : Nat) : K := pairsVal ρ (g.map fun x => (subE oneE x, x)) b

/-- Without a coordinate every row has the weight 1. -/
theorem eqVal_nil (b : Nat) : eqVal ρ [] b = 1 := rfl

/-- One step of the weight: the first coordinate goes with the lowest bit of the row's number. -/
theorem eqVal_cons (x : E) (g : List E) (b : Nat) :
    eqVal ρ (x :: g) b = (if b % 2 = 1 then ρ.val x else 1 - ρ.val x) * eqVal ρ g (b / 2) := by
  show ρ.val (if b % 2 == 1 then x else subE oneE x) * eqVal ρ g (b / 2) = _
  by_cases h : b % 2 = 1
  · rw [if_pos (beq_iff_eq.2 h), if_pos h]
  · rw [if_neg (fun c => h (beq_iff_eq.1 c)), if_neg h, ρ.sub, ρ.one]

/-- A sum over the numbers below 2 m, in pairs. -/
theorem sum_range_pairs (F : Nat → K) : ∀ m : Nat,
    ((List.range (2 * m)).map F).sum = ((List.range m).map fun b => F (2 * b) + F (2 * b + 1)).sum
  | 0 => rfl
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 from rfl, List.range_succ, List.range_succ,
      List.range_succ (n := m)]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    rw [sum_range_pairs F m, add_assoc]

/-! ## The fold of a table -/

/-- One variable folded: half as many entries. -/
theorem size_foldLowOnce (v : Array E) (g : E) : (foldLowOnce v g).size = v.size / 2 :=
  Array.size_ofFn

/-- One variable folded: entry i reads as (1 - g) v[2 i] + g v[2 i + 1]. A last entry without a
partner is dropped. An entry from v.size / 2 on reads as 0. -/
theorem foldLowOnce_val (v : Array E) (g : E) (i : Nat) :
    ρ.val ((foldLowOnce v g).getD i zeroE) =
      if i < v.size / 2 then
        (1 - ρ.val g) * ρ.val (v.getD (2 * i) zeroE) + ρ.val g * ρ.val (v.getD (2 * i + 1) zeroE)
      else 0 := by
  unfold foldLowOnce
  rw [getD_ofFn]
  by_cases h : i < v.size / 2
  · rw [dif_pos h, if_pos h]
    show ρ.val (maddE (v.getD (2 * i) zeroE) g
      (subE (v.getD (2 * i + 1) zeroE) (v.getD (2 * i) zeroE))) = _
    rw [maddE_val, ρ.sub]
    ring
  · rw [dif_neg h, if_neg h, ρ.zero]

/-- A fold at no coordinate leaves the table as it was. -/
theorem foldLow_nil (v : Array E) : foldLow v [] = v := rfl

/-- One step of the fold. -/
theorem foldLow_cons (v : Array E) (x : E) (g : List E) :
    foldLow v (x :: g) = foldLow (foldLowOnce v x) g := rfl

/-- The fold of a table at a point: entry p reads as the sum over the rows b of the weight of b at
the point times entry b + 2^|g| p (row b, place p), for p below v.size / 2^|g|; a later entry reads
as 0. -/
theorem foldLow_val : ∀ (g : List E) (v : Array E) (p : Nat),
    ρ.val ((foldLow v g).getD p zeroE) =
      if p < v.size / 2 ^ g.length then
        ((List.range (2 ^ g.length)).map fun b =>
          eqVal ρ g b * ρ.val (v.getD (b + 2 ^ g.length * p) zeroE)).sum
      else 0
  | [], v, p => by
    rw [foldLow_nil]
    show _ = if p < v.size / 2 ^ 0 then
      ((List.range (2 ^ 0)).map fun b => eqVal ρ [] b * ρ.val (v.getD (b + 2 ^ 0 * p) zeroE)).sum
      else 0
    rw [Nat.pow_zero, Nat.div_one]
    by_cases h : p < v.size
    · rw [if_pos h]
      simp [eqVal_nil]
    · rw [if_neg h, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      exact ρ.zero
  | x :: g, v, p => by
    have hpow : 2 ^ (x :: g).length = 2 * 2 ^ g.length := by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_comm]
    rw [foldLow_cons, foldLow_val g (foldLowOnce v x) p, size_foldLowOnce, Nat.div_div_eq_div_mul,
      hpow]
    by_cases hp : p < v.size / (2 * 2 ^ g.length)
    · rw [if_pos hp, if_pos hp, sum_range_pairs]
      refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
      have hb' : b < 2 ^ g.length := List.mem_range.1 hb
      -- The entry of the once folded table is there.
      have hin : b + 2 ^ g.length * p < v.size / 2 := by
        have h1 : (p + 1) * 2 ^ g.length ≤ v.size / 2 := by
          rw [← Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.div_div_eq_div_mul]
          exact hp
        rw [Nat.succ_mul, Nat.mul_comm] at h1
        omega
      have e0 : 2 * (b + 2 ^ g.length * p) = 2 * b + 2 * 2 ^ g.length * p := by
        rw [Nat.mul_add, Nat.mul_assoc]
      have e1 : 2 * (b + 2 ^ g.length * p) + 1 = 2 * b + 1 + 2 * 2 ^ g.length * p := by omega
      rw [foldLowOnce_val, if_pos hin, e1, e0, eqVal_cons, eqVal_cons,
        if_neg (by omega : ¬ 2 * b % 2 = 1), if_pos (by omega : (2 * b + 1) % 2 = 1),
        show 2 * b / 2 = b by omega, show (2 * b + 1) / 2 = b by omega]
      ring
    · rw [if_neg hp, if_neg hp]

/-- A table of exactly 2^|g| entries, folded at g: its first entry reads as the sum over b of the
weight of b times entry b. -/
theorem foldLow_all (g : List E) (v : Array E) (h : v.size = 2 ^ g.length) :
    ρ.val ((foldLow v g).getD 0 zeroE) =
      ((List.range (2 ^ g.length)).map fun b => eqVal ρ g b * ρ.val (v.getD b zeroE)).sum := by
  rw [foldLow_val, h, Nat.div_self (Nat.two_pow_pos _), if_pos Nat.one_pos]
  simp only [Nat.mul_zero, Nat.add_zero]

/-! ## The symbols of the single rows -/

/-- For a call that succeeds, on a complex with at most two mask rows (s.masks ≤ 2, which the
function does not test): what the symbols of the single rows read as. For each listed position in
turn: the fold, at the whole point, of the group's main table as the layout places it; the kept
members' main symbols as they were opened; the fold of the group's mask table, and then of the fresh
mask's column, at the point's first coordinates. -/
theorem singleRowsSymbols_val (s : SingleRows) (opened : Array (Array Column)) (n : Nat)
    (y : Array E) (hm : s.masks ≤ 2) (h : singleRowsSymbols s opened n = some y) :
    y.size = n * s.rows ∧ ∀ i, i < n →
      ρ.val (y.getD (i * s.rows) zeroE) =
          ((List.range (2 ^ s.layout.k)).map fun b =>
            eqVal ρ s.gamma b * ρ.val (mainTable s.layout opened i b)).sum ∧
        (∀ j, j < s.keptRows →
          y.getD (i * s.rows + 1 + j) zeroE = (keptSymbols s.layout opened i).getD j zeroE) ∧
        (1 ≤ s.masks → ρ.val (y.getD (i * s.rows + s.maskRow 0) zeroE) =
          ((List.range (2 ^ s.layout.h)).map fun b =>
            eqVal ρ (s.gamma.take s.layout.h) b * ρ.val (maskTable s.layout opened i b)).sum) ∧
        (s.masks = 2 → ρ.val (y.getD (i * s.rows + s.maskRow 1) zeroE) =
          ((List.range (2 ^ s.layout.h)).map fun b =>
            eqVal ρ (s.gamma.take s.layout.h) b *
              ρ.val ((colB opened s.layout.members.size i).mask.getD b zeroE)).sum) := by
  obtain ⟨hg, hh, hsize, hall⟩ := singleRowsSymbols_inv s opened n y hm h
  have hlow : (s.gamma.take s.layout.h).length = s.layout.h := by
    rw [List.length_take, hg]
    omega
  refine ⟨hsize, fun i hi => ?_⟩
  obtain ⟨t, ht, _, e0, ek, e1, e2⟩ := hall i hi
  obtain ⟨s1, s2, s3, s4, s5⟩ := tablesAt_all s.layout opened i t ht
  refine ⟨?_, fun j hj => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · rw [e0, foldLow_all ρ s.gamma t.1 (by rw [s1, hg]), hg]
    simp only [s4]
  · rw [ek j hj, ← s3, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
      Array.getElem?_toList]
  · rw [e1 h1, foldLow_all ρ _ t.2.1 (by rw [s2, hlow]), hlow]
    simp only [s5]
  · rw [(e2 h2).2, foldLow_all ρ _ _ (by rw [(e2 h2).1, hlow]), hlow]

end OnBytes

#print axioms OnBytes.eqVal_nil
#print axioms OnBytes.eqVal_cons
#print axioms OnBytes.sum_range_pairs
#print axioms OnBytes.size_foldLowOnce
#print axioms OnBytes.foldLowOnce_val
#print axioms OnBytes.foldLow_nil
#print axioms OnBytes.foldLow_cons
#print axioms OnBytes.foldLow_val
#print axioms OnBytes.foldLow_all
#print axioms OnBytes.singleRowsSymbols_val
