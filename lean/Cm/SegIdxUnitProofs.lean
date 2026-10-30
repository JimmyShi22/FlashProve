-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegIdxUnitProofs.lean: the proofs of the statements of Cm/SegIdx.lean on the atoms of the units
of the layout: `Spec.unit_ok`, `Spec.unit_vtx`, `Spec.live_of_inUnit`, `Spec.of_fits`.

A unit is one weight tensor with its coordinates, as the layout puts it into the index matrix
(`UnitS`, Inst/Model/Layout.lean); the bits of a coordinate's index come in three runs A, B, C of
sources (`CSrc`, Cm/SegIdx.lean).

Main names, each for runs that fit (`CSrc.Fits`, `FitsAll`):
  `col_num`: the column of the unit is the number of its column sources.
  `rowDec_num`: the row is decoded from the number of its row bits.
`unit_vtx` and `unit_ok` then follow from `ofBits_vtx` and `ofBits_ok` (Cm/SegIdxProofs.lean).
-/
import Cm.SegIdxProofs
import Inst.Model.LayoutBridge

set_option autoImplicit false

namespace Cm
open Cb Blocks Finset Inst.Model Inst.Model.Layout

/-! ## 1. Numbers of lists of bits -/

theorem numL_lt : ∀ l : List Bool, numL l < 2 ^ l.length
  | [] => by simp [numL]
  | β :: l => by
      have h := numL_lt l
      show (if β then 2 ^ l.length else 0) + numL l < 2 ^ (l.length + 1)
      rw [pow_succ]
      cases β <;> simp <;> omega

theorem numL_append : ∀ l₁ l₂ : List Bool, numL (l₁ ++ l₂) = numL l₁ * 2 ^ l₂.length + numL l₂
  | [], l₂ => by simp [numL]
  | β :: l₁, l₂ => by
      show (if β then 2 ^ (l₁ ++ l₂).length else 0) + numL (l₁ ++ l₂) =
        ((if β then 2 ^ l₁.length else 0) + numL l₁) * 2 ^ l₂.length + numL l₂
      rw [numL_append l₁ l₂, List.length_append, pow_add]
      cases β
      · simp
      · simp; ring

theorem num_lt (l : List Src) (v b : ℕ) : Src.num l v b < 2 ^ l.length := by
  have h := numL_lt (l.map fun s => s.bitAt v b)
  rwa [List.length_map] at h

theorem num_append (l₁ l₂ : List Src) (v b : ℕ) :
    Src.num (l₁ ++ l₂) v b = Src.num l₁ v b * 2 ^ l₂.length + Src.num l₂ v b := by
  unfold Src.num
  rw [List.map_append, numL_append, List.length_map]

theorem num_nil (v b : ℕ) : Src.num [] v b = 0 := rfl

theorem num_zeros (m v b : ℕ) : Src.num (List.replicate m (.bit false)) v b = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show (if false = true then _ else 0) +
        numL ((List.replicate m (Src.bit false)).map fun s => s.bitAt v b) = 0
    rw [if_neg (by simp), Nat.zero_add]
    exact ih

theorem vars_zeros (m : ℕ) : Src.vars (List.replicate m (.bit false)) = [] := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih

/-! ## 2. One coordinate -/

theorem div_mod_of {a e M : ℕ} (he : e < M) : (a * M + e) / M = a ∧ (a * M + e) % M = e := by
  have hM : 0 < M := lt_of_le_of_lt (Nat.zero_le _) he
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div hM, Nat.div_eq_of_lt he, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt he]

/-- If the runs fit, the split of a coordinate of each of the three kinds (`split`,
Inst/Model/Layout.lean) cuts the number of A ++ B ++ C into the number of B and the number of
A ++ C. -/
theorem split_num (x : CSrc) (c : Coord) (t : ℕ) (h : x.Fits c t) (v b : ℕ) :
    split c t (Src.num x.all v b) = (Src.num x.B v b, Src.num x.rowBits v b) := by
  obtain ⟨A, B, C⟩ := x
  obtain ⟨R, kind⟩ := c
  obtain ⟨hB, hk⟩ := h
  have hB : B.length = t := hB
  have hb := num_lt B v b
  rw [hB] at hb
  cases kind with
  | low =>
    have hC : C = [] := hk
    subst hC
    show (Src.num (A ++ B ++ []) v b % 2 ^ t, Src.num (A ++ B ++ []) v b / 2 ^ t) =
      (Src.num B v b, Src.num (A ++ []) v b)
    rw [List.append_nil, List.append_nil, num_append, hB, (div_mod_of hb).1, (div_mod_of hb).2]
  | high =>
    obtain ⟨hts, hC⟩ : t ≤ sOf R ∧ C.length = sOf R - t := hk
    have he := num_lt C v b
    rw [hC] at he
    show ((Src.num (A ++ B ++ C) v b / 2 ^ (sOf R - t)) % 2 ^ t,
        (Src.num (A ++ B ++ C) v b / 2 ^ sOf R) * 2 ^ (sOf R - t) +
          Src.num (A ++ B ++ C) v b % 2 ^ (sOf R - t)) =
      (Src.num B v b, Src.num (A ++ C) v b)
    have hp : (2 : ℕ) ^ sOf R = 2 ^ (sOf R - t) * 2 ^ t := by rw [← pow_add, Nat.sub_add_cancel hts]
    rw [num_append (A ++ B) C, num_append A B, num_append A C, hB, hC, hp, ← Nat.div_div_eq_div_mul,
      (div_mod_of he).1, (div_mod_of he).2, (div_mod_of hb).1, (div_mod_of hb).2]
  | whole =>
    obtain ⟨hC, hA⟩ : C = [] ∧ (0 < t → A = []) := hk
    subst hC
    show (if 0 < t then (Src.num (A ++ B ++ []) v b, 0) else (0, Src.num (A ++ B ++ []) v b)) =
      (Src.num B v b, Src.num (A ++ []) v b)
    by_cases ht : 0 < t
    · rw [if_pos ht, hA ht, List.nil_append, List.append_nil, List.append_nil]
      rfl
    · have hB0 : B = [] := List.length_eq_zero_iff.1 (by omega)
      rw [if_neg ht, hB0]
      simp [num_nil]

/-! ## 3. A unit -/

theorem colSrc_length_le :
    ∀ (cs : List Coord) (left : ℕ) (xs : List CSrc), FitsAll cs left xs → (colSrc xs).length ≤ left
  | [], _, [], _ => Nat.zero_le _
  | c :: cs, left, x :: xs, h => by
      have h1 := colSrc_length_le cs (left - tOf c left) xs h.2
      have h2 : x.B.length = tOf c left := h.1.1
      have h3 := Bridge.tOf_le c left
      show (colSrc xs ++ x.B).length ≤ left
      rw [List.length_append, h2]
      omega
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

theorem col_num (v b : ℕ) : ∀ (cs : List Coord) (left : ℕ) (xs : List CSrc), FitsAll cs left xs →
    col cs (bits cs left) (idxAt xs v b) = Src.num (colSrc xs) v b
  | [], _, [], _ => rfl
  | c :: cs, left, x :: xs, h => by
      show (split c (tOf c left) (Src.num x.all v b)).1 +
          2 ^ tOf c left * col cs (bits cs (left - tOf c left)) (idxAt xs v b) =
        Src.num (colSrc xs ++ x.B) v b
      rw [split_num x c _ h.1, col_num v b cs _ xs h.2, num_append, h.1.1]
      ring
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

theorem rowDec_num (j v b : ℕ) :
    ∀ (cs : List Coord) (left : ℕ) (xs : List CSrc), FitsAll cs left xs →
      rowDec j cs left xs (Src.num (rowSrc xs) v b) = row j cs (bits cs left) (idxAt xs v b)
  | [], _, [], _ => rfl
  | c :: cs, left, x :: xs, h => by
      have hr := num_lt x.rowBits v b
      show Src.num (rowSrc xs ++ x.rowBits) v b % 2 ^ x.rowBits.length +
          lOf c (tOf c left) *
            rowDec j cs (left - tOf c left) xs
              (Src.num (rowSrc xs ++ x.rowBits) v b / 2 ^ x.rowBits.length) =
        (split c (tOf c left) (Src.num x.all v b)).2 +
          lOf c (tOf c left) * row j cs (bits cs (left - tOf c left)) (idxAt xs v b)
      rw [num_append, (div_mod_of hr).1, (div_mod_of hr).2,
        split_num x c _ h.1, rowDec_num j v b cs _ xs h.2]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

theorem rowLive_num (v b : ℕ) :
    ∀ (cs : List Coord) (left : ℕ) (xs : List CSrc), FitsAll cs left xs →
      (rowLive cs left xs (Src.num (rowSrc xs) v b) ↔ LiveAt cs left (idxAt xs v b))
  | [], _, [], _ => Iff.rfl
  | c :: cs, left, x :: xs, h => by
      have hr := num_lt x.rowBits v b
      show (Src.num (rowSrc xs ++ x.rowBits) v b % 2 ^ x.rowBits.length < lOf c (tOf c left) ∧
          rowLive cs (left - tOf c left) xs
            (Src.num (rowSrc xs ++ x.rowBits) v b / 2 ^ x.rowBits.length)) ↔
        ((split c (tOf c left) (Src.num x.all v b)).2 < lOf c (tOf c left) ∧
          LiveAt cs (left - tOf c left) (idxAt xs v b))
      rw [num_append, (div_mod_of hr).1, (div_mod_of hr).2,
        split_num x c _ h.1, rowLive_num v b cs _ xs h.2]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- if the runs fit and the digit j is below nU, rows of live row parts are inside the unit -/
theorem rowDec_lt {j nU : ℕ} (hj : j < nU) :
    ∀ (cs : List Coord) (left : ℕ) (xs : List CSrc) (r : ℕ),
      FitsAll cs left xs → rowLive cs left xs r → rowDec j cs left xs r < nU * Bridge.lprod cs left
  | [], _, [], _, _, _ => by simpa [rowDec, Bridge.lprod] using hj
  | c :: cs, left, x :: xs, r, h, hl => by
      have ih := rowDec_lt hj cs (left - tOf c left) xs (r / 2 ^ x.rowBits.length) h.2 hl.2
      have h1 : r % 2 ^ x.rowBits.length < lOf c (tOf c left) := hl.1
      show r % 2 ^ x.rowBits.length +
          lOf c (tOf c left) * rowDec j cs (left - tOf c left) xs (r / 2 ^ x.rowBits.length) <
        nU * (lOf c (tOf c left) * Bridge.lprod cs (left - tOf c left))
      calc
        r % 2 ^ x.rowBits.length +
              lOf c (tOf c left) * rowDec j cs (left - tOf c left) xs (r / 2 ^ x.rowBits.length) <
            lOf c (tOf c left) +
              lOf c (tOf c left) * rowDec j cs (left - tOf c left) xs (r / 2 ^ x.rowBits.length) :=
          Nat.add_lt_add_right h1 _
        _ = lOf c (tOf c left) *
              (rowDec j cs (left - tOf c left) xs (r / 2 ^ x.rowBits.length) + 1) := by ring
        _ ≤ lOf c (tOf c left) * (nU * Bridge.lprod cs (left - tOf c left)) :=
          Nat.mul_le_mul_left _ ih
        _ = nU * (lOf c (tOf c left) * Bridge.lprod cs (left - tOf c left)) := by ring
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem live_of_inUnit : Spec.live_of_inUnit
  | [], _, [], _ => trivial
  | c :: cs, left, i :: is, h => ⟨((Bridge.good_split c left).lt i h.1).2, live_of_inUnit cs _ is h.2⟩
  | [], _, _ :: _, _ => trivial
  | _ :: _, _, [], _ => trivial

/-! ## 4. The atom of a unit -/

theorem pad_length {k : ℕ} {l : List Src} (h : l.length ≤ k) :
    (List.replicate (k - l.length) (Src.bit false) ++ l).length = k := by
  rw [List.length_append, List.length_replicate]
  omega

theorem unit_ok : Spec.unit_ok := by
  intro F _ E _ _ Φ v P n U xs hf hOK
  refine ofBits_ok F E Φ v _ _ _ (pad_length (colSrc_length_le _ _ _ hf)) ?_
  unfold Src.OK at hOK ⊢
  rw [List.append_assoc, vars_append, vars_zeros, List.nil_append]
  exact hOK

theorem unit_vtx : Spec.unit_vtx := by
  classical
  intro F _ E _ _ Φ v P n U xs hf hfit W b
  have hlen := colSrc_length_le _ _ _ hf
  rw [unitAtom, ofBits_vtx F E Φ v _ _ _ (pad_length hlen) W b, num_append, num_zeros, Nat.zero_mul,
    Nat.zero_add, ← col_num v b _ _ _ hf]
  unfold unitTab
  by_cases hl : LiveAt U.coords (Φ.hi + Φ.lo) (idxAt xs v b)
  · have hl' := (rowLive_num v b _ _ _ hf).2 hl
    simp only [if_pos hl, if_pos hl']
    unfold entryW
    rw [map_sum]
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    have hrow : off (Φ.hi + Φ.lo) (units P) n +
          rowDec j U.coords (Φ.hi + Φ.lo) xs (Src.num (rowSrc xs) v b) < Φ.h := by
      have h1 := rowDec_lt (mem_range.mp hj) _ _ _ _ hf hl'
      rw [← Bridge.hU_eq] at h1
      exact lt_of_lt_of_le (Nat.add_lt_add_left h1 _) hfit
    rw [sum_eq_single
        (off (Φ.hi + Φ.lo) (units P) n +
          rowDec j U.coords (Φ.hi + Φ.lo) xs (Src.num (rowSrc xs) v b))]
    · rw [if_pos rfl, rowDec_num j v b _ _ _ hf, map_mul, map_pow, map_ofNat]
      rfl
    · intro y _ hy
      rw [if_neg hy, zero_mul]
    · intro hn
      exact absurd (mem_range.mpr hrow) hn
  · have hl' := fun h => hl ((rowLive_num v b _ _ _ hf).1 h)
    simp only [if_neg hl, if_neg hl', zero_mul, sum_const_zero]

theorem of_fits : Spec.of_fits := by
  intro c t σ h1 h2 h3
  obtain ⟨R, kind⟩ := c
  cases kind with
  | low =>
    have ht := h1 rfl
    refine ⟨⟨?_, rfl⟩, ?_⟩
    · show (σ.drop (σ.length - t)).length = t
      rw [List.length_drop]
      omega
    · show σ.take (σ.length - t) ++ σ.drop (σ.length - t) ++ [] = σ
      rw [List.append_nil, List.take_append_drop]
  | high =>
    obtain ⟨ht, hs⟩ := h2 rfl
    have ht : t ≤ sOf R := ht
    have hs : sOf R ≤ σ.length := hs
    refine ⟨⟨?_, ht, ?_⟩, ?_⟩
    · show ((σ.drop (σ.length - sOf R)).take t).length = t
      rw [List.length_take, List.length_drop]
      omega
    · show ((σ.drop (σ.length - sOf R)).drop t).length = sOf R - t
      rw [List.length_drop, List.length_drop]
      omega
    · show σ.take (σ.length - sOf R) ++ (σ.drop (σ.length - sOf R)).take t ++
          (σ.drop (σ.length - sOf R)).drop t = σ
      rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  | whole =>
    by_cases ht : 0 < t
    · have e : CSrc.of ⟨R, .whole⟩ t σ = ⟨[], σ, []⟩ := if_pos ht
      rw [e]
      exact ⟨⟨h3 rfl ht, rfl, fun _ => rfl⟩, by simp [CSrc.all]⟩
    · have e : CSrc.of ⟨R, .whole⟩ t σ = ⟨σ, [], []⟩ := if_neg ht
      rw [e]
      exact ⟨⟨by show 0 = t; omega, rfl, fun h => absurd h ht⟩, by simp [CSrc.all]⟩

end Cm
