-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/Toy2.lean: the relation before the smallness test's round at a second closed toy: one
matrix with two rows of cells in one symbol, over the integers.

Why: a symbol has room for three cells. Where a column has two rows, the third place of its one
symbol stands for no row. The relation before the round must refuse a symbol with anything there.

The radix is 8, the shift 2: a cell counts as small if it lies strictly between -4 and 4. There is
no read.

Main names:
  `pack_two`: the packing of two cells a 0, a 1 is a 0 + 8 * a 1.
  `toy2_in`: at the symbol 17 there are cells: 1 and 2.
  `toy2_third`: at the symbol 17 + 64 there are none.

Terms: lean/GLOSSARY.md.

-/
import Cb.Pv.Tail.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail.Toy2
open Iop

/-- One matrix, two rows of cells, one column, no read, one combination. -/
abbrev sz : Size := ⟨1, fun _ => 2, fun _ => 1, fun _ => 0, 1, 8, 2, 2, 2⟩

/-- no implicit instance -/
def eNone : ExtSpec := ⟨Unit, Empty, Unit, fun _ e => e.elim⟩

/-- The letters: the committed message is the one symbol. -/
def lt : Letters ℤ sz where
  X := Unit
  M := ℤ
  E := eNone
  W := Dig ℤ sz
  w := fun _ _ r _ => r.elim0
  sym := fun m _ _ _ => m
  tab := fun _ _ r _ => r.elim0
  dig := fun Z => Z
  ride := fun _ _ _ => True

/-- the column that is 1 in row i and 0 elsewhere -/
def e2 (i : Fin 2) : Fin 2 → ℤ := fun i₂ => if i₂ = i then 1 else 0

theorem pack_two (a : Fin 2 → ℤ) (i' : Fin (Alg.symRows 2)) :
    Alg.pack ((8 : ℕ) : ℤ) a i' = a 0 + 8 * a 1 := by
  have h : (i' : ℕ) = 0 := by
    have := i'.2
    unfold Alg.symRows at this
    omega
  rw [h]
  have e : a = fun i₂ => ∑ i, a i * e2 i i₂ := by
    funext i₂
    simp [e2, Finset.sum_ite_eq]
  conv_lhs => rw [e]
  rw [Alg.pack_sum, Fin.sum_univ_two, Alg.pack_mul_left, Alg.pack_mul_left,
    show Alg.pack ((8 : ℕ) : ℤ) (e2 0) 0 = 1 from by decide,
    show Alg.pack ((8 : ℕ) : ℤ) (e2 1) 0 = 8 from by decide]
  ring

theorem toy2_in : relIn lt () (17 : ℤ) := fun _ _ =>
  ⟨fun i : Fin 2 => if i = 0 then 1 else 2, fun i => by
      show |(if i = (0 : Fin 2) then (1 : ℤ) else 2)| < 2 * ((2 : ℕ) : ℤ)
      split_ifs <;> norm_num,
    fun i' => by
      show (17 : ℤ) = Alg.pack ((8 : ℕ) : ℤ) (fun i : Fin 2 => if i = 0 then (1 : ℤ) else 2) i'
      rw [pack_two]
      simp,
    fun r => r.elim0⟩

/-- A symbol with something in the place that stands for no row is refused. -/
theorem toy2_third : ¬ relIn lt () (17 + 64 : ℤ) := fun h => by
  obtain ⟨a, hs, hp, -⟩ := h (⟨0, Nat.one_pos⟩ : Fin 1) (⟨0, Nat.one_pos⟩ : Fin 1)
  have h0 : |(show Fin 2 → ℤ from a) 0| < 2 * ((2 : ℕ) : ℤ) := hs (0 : Fin 2)
  have h1 : |(show Fin 2 → ℤ from a) 1| < 2 * ((2 : ℕ) : ℤ) := hs (1 : Fin 2)
  have e : (17 + 64 : ℤ) = Alg.pack ((8 : ℕ) : ℤ) (show Fin 2 → ℤ from a)
      ((⟨0, by decide⟩ : Fin (Alg.symRows 2)) : ℕ) := hp (⟨0, by decide⟩ : Fin (Alg.symRows 2))
  rw [pack_two] at e
  rw [abs_lt] at h0 h1
  norm_num at h0 h1
  omega

end Cb.Pv.Tail.Toy2

#print axioms Cb.Pv.Tail.Toy2.toy2_in
#print axioms Cb.Pv.Tail.Toy2.toy2_third
