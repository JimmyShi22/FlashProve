-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetReadBitsFFK3.lean: vertices (layer ℓ, index x, position i) (`dec3`, Cm/SegAlg.lean) split
for a matrix with 2^f features in a column (`featAt`, Inst/Model/FF/Index.lean): the low f bits of x
and the position on the row side, the layer and the high bits of x on the column side.

A source of a bit (`Src`, Cm/SegIdx.lean) is a variable of the cube, its negation or a constant bit;
a list of sources forms a number at each vertex b (`Src.num`). In the calculus of separable atoms
(Cm/TargetReadBits.lean) a piece's weights on rows depend on the number t of one list (the row
side), its weights on columns on the number u of another (the column side).

Definitions and small theorems. This file joins the families of keys of the feed-forward segments to
Cm/TargetReadBitsFldFF.lean. Generic in vx, f.

Main names:
  `cs3 vx f`, `rs3 vx f` (`cs3_ok`: `Src.OK`, for f ≤ vx): the row sources, the column sources, in
    the cube of 2 + vx + 10 variables.
  `num_cs3`, `num_rs3`: for f ≤ vx, their numbers at the vertex b: t = (x mod 2^f) · 2^10 + i; u = ℓ
    · 2^(vx − f) + x / 2^f (the second for b < 2^(2 + vx + 10)).
  `csA vx`, `rsA vx`, `csA_ok`, `num_csA`, `num_rsA`, `uA_l`, `uA_x`: the fall-back's split (`WA`,
    `termAny`, Cm/TargetReadBitsFFKT.lean): the position alone on the row side; (ℓ, x) on the column
    side (`num_rsA`, `uA_l`, `uA_x` for b < 2^(2 + vx + 10)).

Terms: lean/GLOSSARY.md.
-/
import Cm.TargetReadBitsFldProofs
import Cm.SegAlg

set_option autoImplicit false

namespace Cm.TR

open Cb Blocks Finset Cm.Seg

def cs3 (vx f : ℕ) : List Src := fldsS (2 + vx + 10) [(10, f), (0, 10)]
def rs3 (vx f : ℕ) : List Src := fldsS (2 + vx + 10) [(10 + vx, 2), (10 + f, vx - f)]
def csA (vx : ℕ) : List Src := fldsS (2 + vx + 10) [(0, 10)]
def rsA (vx : ℕ) : List Src := fldsS (2 + vx + 10) [(10 + vx, 2), (10, vx)]

theorem cs3_ok (vx f : ℕ) (h : f ≤ vx) : Src.OK (cs3 vx f ++ rs3 vx f) (2 + vx + 10) := by
  refine flds_ok _ _ _ (fun p hp => ?_) ?_
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp only <;> omega
  · unfold FldApart
    simp only [List.cons_append, List.nil_append, List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true,
      List.Pairwise.nil, and_true]
    omega

theorem csA_ok (vx : ℕ) : Src.OK (csA vx ++ rsA vx) (2 + vx + 10) := by
  refine flds_ok _ _ _ (fun p hp => ?_) ?_
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp only <;> omega
  · unfold FldApart
    simp only [List.cons_append, List.nil_append, List.pairwise_cons, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true,
      List.Pairwise.nil, and_true]
    omega

/-- The low bits of the index. -/
theorem fld_lo (vx f b : ℕ) (h : f ≤ vx) : fld 10 f b = (dec3 vx b).2.1 % 2 ^ f := by
  show b / 2 ^ 10 % 2 ^ f = b / 2 ^ 10 % 2 ^ vx % 2 ^ f
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 h)]

theorem fld_pos (vx b : ℕ) : fld 0 10 b = (dec3 vx b).2.2 := by
  show b / 2 ^ 0 % 2 ^ 10 = b % 2 ^ 10
  rw [pow_zero, Nat.div_one]

theorem fld_x (vx b : ℕ) : fld 10 vx b = (dec3 vx b).2.1 := rfl

theorem fld_hi (vx f b : ℕ) (h : f ≤ vx) : fld (10 + f) (vx - f) b = (dec3 vx b).2.1 / 2 ^ f := by
  show b / 2 ^ (10 + f) % 2 ^ (vx - f) = b / 2 ^ 10 % 2 ^ vx / 2 ^ f
  have e : 2 ^ vx = 2 ^ f * 2 ^ (vx - f) := by rw [← pow_add]; congr 1; omega
  rw [pow_add, ← Nat.div_div_eq_div_mul, e, Nat.mod_mul_right_div_self]

theorem fld_l (vx b : ℕ) (hb : b < 2 ^ (2 + vx + 10)) : fld (10 + vx) 2 b = (dec3 vx b).1 := by
  show b / 2 ^ (10 + vx) % 2 ^ 2 = b / 2 ^ 10 / 2 ^ vx
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  refine Nat.mod_eq_of_lt ?_
  rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
  calc b < 2 ^ (2 + vx + 10) := hb
    _ = 2 ^ 2 * (2 ^ 10 * 2 ^ vx) := by ring

theorem num_cs3 (vx f b : ℕ) (h : f ≤ vx) :
    Src.num (cs3 vx f) (2 + vx + 10) b = (dec3 vx b).2.1 % 2 ^ f * 2 ^ 10 + (dec3 vx b).2.2 := by
  unfold cs3
  rw [flds_num _ _ _ (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only <;> omega), (flds_two 10 f 0 10 b).1, fld_lo vx f b h, fld_pos vx b]

theorem num_rs3 (vx f b : ℕ) (h : f ≤ vx) (hb : b < 2 ^ (2 + vx + 10)) :
    Src.num (rs3 vx f) (2 + vx + 10) b =
      (dec3 vx b).1 * 2 ^ (vx - f) + (dec3 vx b).2.1 / 2 ^ f := by
  unfold rs3
  rw [flds_num _ _ _ (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only <;> omega), (flds_two (10 + vx) 2 (10 + f) (vx - f) b).1, fld_l vx b hb, fld_hi vx f b h]

theorem dec3_i_lt (vx b : ℕ) : (dec3 vx b).2.2 < 2 ^ 10 := Nat.mod_lt _ (by positivity)
theorem dec3_x_lt (vx b : ℕ) : (dec3 vx b).2.1 < 2 ^ vx := Nat.mod_lt _ (by positivity)
theorem dec3_l_lt (vx b : ℕ) (hb : b < 2 ^ (2 + vx + 10)) : (dec3 vx b).1 < 4 := by
  rw [← fld_l vx b hb]
  exact Nat.mod_lt _ (by norm_num)

theorem t3_lo (vx f b : ℕ) (h : f ≤ vx) :
    Src.num (cs3 vx f) (2 + vx + 10) b / 2 ^ 10 = (dec3 vx b).2.1 % 2 ^ f := by
  rw [num_cs3 vx f b h, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (dec3_i_lt vx b), Nat.zero_add]

theorem t3_pos (vx f b : ℕ) (h : f ≤ vx) :
    Src.num (cs3 vx f) (2 + vx + 10) b % 2 ^ 10 = (dec3 vx b).2.2 := by
  rw [num_cs3 vx f b h, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (dec3_i_lt vx b)]

theorem xh_lt (vx f b : ℕ) (h : f ≤ vx) : (dec3 vx b).2.1 / 2 ^ f < 2 ^ (vx - f) := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  have e : vx - f + f = vx := by omega
  rw [e]
  exact dec3_x_lt vx b

theorem u3_l (vx f b : ℕ) (h : f ≤ vx) (hb : b < 2 ^ (2 + vx + 10)) :
    Src.num (rs3 vx f) (2 + vx + 10) b / 2 ^ (vx - f) = (dec3 vx b).1 := by
  rw [num_rs3 vx f b h hb, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (xh_lt vx f b h), Nat.zero_add]

theorem u3_hi (vx f b : ℕ) (h : f ≤ vx) (hb : b < 2 ^ (2 + vx + 10)) :
    Src.num (rs3 vx f) (2 + vx + 10) b % 2 ^ (vx - f) = (dec3 vx b).2.1 / 2 ^ f := by
  rw [num_rs3 vx f b h hb, Nat.add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (xh_lt vx f b h)]

theorem num_csA (vx b : ℕ) : Src.num (csA vx) (2 + vx + 10) b = (dec3 vx b).2.2 := by
  unfold csA
  rw [flds_num _ _ _ (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    simp only
    omega)]
  show fld 0 10 b * 2 ^ 0 + 0 = _
  rw [pow_zero, Nat.mul_one, Nat.add_zero, fld_pos vx b]

theorem num_rsA (vx b : ℕ) (hb : b < 2 ^ (2 + vx + 10)) :
    Src.num (rsA vx) (2 + vx + 10) b = (dec3 vx b).1 * 2 ^ vx + (dec3 vx b).2.1 := by
  unfold rsA
  rw [flds_num _ _ _ (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp only <;> omega), (flds_two (10 + vx) 2 10 vx b).1, fld_l vx b hb, fld_x vx b]

theorem uA_l (vx b : ℕ) (hb : b < 2 ^ (2 + vx + 10)) :
    Src.num (rsA vx) (2 + vx + 10) b / 2 ^ vx = (dec3 vx b).1 := by
  rw [num_rsA vx b hb, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (dec3_x_lt vx b), Nat.zero_add]

theorem uA_x (vx b : ℕ) (hb : b < 2 ^ (2 + vx + 10)) :
    Src.num (rsA vx) (2 + vx + 10) b % 2 ^ vx = (dec3 vx b).2.1 := by
  rw [num_rsA vx b hb, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (dec3_x_lt vx b)]

end Cm.TR
