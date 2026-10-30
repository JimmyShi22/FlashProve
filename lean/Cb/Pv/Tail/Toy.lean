-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/Toy.lean: the smallness test's own round at a closed toy: one matrix with one cell, one
read, one combination, over the integers.

Why: a statement on knowledge soundness is worth nothing if its input relation always holds, if its
output relation never holds, or if its error is so large that it says nothing. At the toy each of
the three is excluded by a theorem.

The committed messages of the toy are a pair: the one symbol and the one read. The cell's weight in
the read is 1. The radix is 4, the digits' tables have two entries each, the shift is 2: a cell
counts as small if it lies strictly between -4 and 4.

Main names:
  `toy_hole`: the statement of Cb/Pv/Tail/Block.lean holds at the toy.
  `toy_in`: at the messages (1, 1) there is a cell.
  `toy_tooth`: after the read is turned to 2 there is none, while what rides still holds.
  `toy_big`: at the messages (4, 4) there is none: the cell behind them is not small.
  `toy_out`: at the messages (1, 1) and a drawn entry 1 there are digits that meet all clauses.
  `toy_slips`: at the turned messages and a drawn entry 0 there are such digits too: the error of
    the round cannot be 0.
  `toy_eps`: the error at the toy is 2 of the 4 values that can be drawn.

Terms: lean/GLOSSARY.md.

-/
import Cb.Pv.Tail.Know

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail.Toy
open Iop

/-- One matrix, one cell, one column, one read, one combination. -/
abbrev sz : Size := ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, 1, 4, 2, 2, 2⟩

/-- no implicit instance -/
def eNone : ExtSpec := ⟨Unit, Empty, Unit, fun _ e => e.elim⟩

/-- The letters of the toy. What rides: the symbol is 1 or 4. -/
def lt : Letters ℤ sz where
  X := Unit
  M := ℤ × ℤ
  E := eNone
  W := Dig ℤ sz
  w := fun _ _ _ _ => 1
  sym := fun m _ _ _ => m.1
  tab := fun m _ _ _ => m.2
  dig := fun Z => Z
  ride := fun _ m _ => m.1 = 1 ∨ m.1 = 4

theorem sz_ok : sz.OK := Nat.le_refl 4

theorem toy_hole : HoleAt lt := know lt sz_ok

/-- the packing of one cell -/
theorem pack_one (a : Fin 1 → ℤ) (i' : Fin (Alg.symRows 1)) :
    Alg.pack ((4 : ℕ) : ℤ) a i' = a 0 := by
  have h : (i' : ℕ) = 0 := by
    have := i'.2
    unfold Alg.symRows at this
    omega
  rw [h]
  calc Alg.pack ((4 : ℕ) : ℤ) a 0
      = Alg.pack ((4 : ℕ) : ℤ) (fun i => a 0 * (fun _ : Fin 1 => (1 : ℤ)) i) 0 := by
        congr 1
        funext i
        rw [Subsingleton.elim i 0, mul_one]
    _ = a 0 * Alg.pack ((4 : ℕ) : ℤ) (fun _ : Fin 1 => (1 : ℤ)) 0 := Alg.pack_mul_left _ _ _ _
    _ = a 0 := by
        rw [show Alg.pack ((4 : ℕ) : ℤ) (fun _ : Fin 1 => (1 : ℤ)) 0 = 1 from by decide, mul_one]

theorem toy_in : relIn lt () ((1, 1) : ℤ × ℤ) := fun _ _ =>
  ⟨fun _ => 1, fun _ => by norm_num, fun i' => by
      show (1 : ℤ) = Alg.pack ((4 : ℕ) : ℤ) (fun _ : Fin 1 => (1 : ℤ)) i'
      exact (pack_one (fun _ : Fin 1 => (1 : ℤ)) i').symm,
    fun _ => by
      show (1 : ℤ) = ∑ _i : Fin 1, (1 : ℤ) * (1 : ℤ)
      simp⟩

/-- what a cell behind the messages must be -/
theorem cell_of {m : ℤ × ℤ} (h : relIn lt () m) : ∃ a : ℤ, |a| < 4 ∧ m.1 = a ∧ m.2 = a := by
  obtain ⟨a, hs, hp, hr⟩ := h (⟨0, Nat.one_pos⟩ : Fin 1) (⟨0, Nat.one_pos⟩ : Fin 1)
  refine ⟨(show Fin 1 → ℤ from a) 0, ?_, ?_, ?_⟩
  · have h4 : |(show Fin 1 → ℤ from a) 0| < 2 * ((2 : ℕ) : ℤ) := hs (0 : Fin 1)
    norm_num at h4
    exact h4
  · have e : m.1 = Alg.pack ((4 : ℕ) : ℤ) (show Fin 1 → ℤ from a)
        ((⟨0, by decide⟩ : Fin (Alg.symRows 1)) : ℕ) := hp (⟨0, by decide⟩ : Fin (Alg.symRows 1))
    rw [e]
    exact pack_one _ _
  · have e : m.2 = ∑ i : Fin 1, (1 : ℤ) * (show Fin 1 → ℤ from a) i :=
      hr (⟨0, Nat.one_pos⟩ : Fin 1)
    rw [e]
    simp

/-- The tooth: one entry of the messages is turned: no cell, while what rides holds. -/
theorem toy_tooth (Z : Dig ℤ sz) :
    lt.ride ((), ()) ((1, 2) : ℤ × ℤ) Z ∧ ¬ relIn lt () ((1, 2) : ℤ × ℤ) :=
  ⟨Or.inl rfl, fun h => by
    obtain ⟨a, -, h1, h2⟩ := cell_of h
    have e1 : (1 : ℤ) = a := h1
    have e2 : (2 : ℤ) = a := h2
    omega⟩

/-- A cell that is not small is refused. -/
theorem toy_big (Z : Dig ℤ sz) :
    lt.ride ((), ()) ((4, 4) : ℤ × ℤ) Z ∧ ¬ relIn lt () ((4, 4) : ℤ × ℤ) :=
  ⟨Or.inr rfl, fun h => by
    obtain ⟨a, hs, h1, -⟩ := cell_of h
    have e1 : (4 : ℤ) = a := h1
    rw [← e1] at hs
    norm_num at hs⟩

/-- the digits l, h everywhere -/
def dg (l h : ℤ) : Dig ℤ sz := ⟨fun _ _ _ => l, fun _ _ _ => h⟩

/-- the drawn matrix with the one entry e -/
def dr (e : Prob.Coef) : Dr sz := fun _ _ _ => e

theorem out_of (m : ℤ × ℤ) (e : Prob.Coef) (l h : ℕ) (hl : l < 2) (hh : h < 2)
    (h1 : e.val * m.1 = (l : ℤ) + 2 * (h : ℤ) - 2) (h2 : e.val * m.2 = (l : ℤ) + 2 * (h : ℤ) - 2) :
    relOut lt () (dr e) m (dg l h) :=
  ⟨fun _ _ _ => ⟨⟨l, hl, rfl⟩, ⟨h, hh, rfl⟩⟩,
    fun μ u i' => by
      show ∑ _c : Fin 1, ((e.val : ℤ) : ℤ) * m.1 =
        Alg.pack ((4 : ℕ) : ℤ) (comb (dg l h) μ u) i'
      rw [pack_one]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [h1]
      simp [comb, dg],
    fun μ u _ => by
      show ∑ _c : Fin 1, ((e.val : ℤ) : ℤ) * m.2 = ∑ i : Fin 1, (1 : ℤ) * comb (dg l h) μ u i
      simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
      rw [h2]
      simp [comb, dg]⟩

/-- The output relation can hold: true messages, the drawn entry 1. -/
theorem toy_out : relOut lt () (dr (true, false)) ((1, 1) : ℤ × ℤ) (dg 1 1) :=
  out_of (1, 1) (true, false) 1 1 (by norm_num) (by norm_num) (by simp [Prob.Coef.val])
    (by simp [Prob.Coef.val])

/-- The error cannot be 0: turned messages, the drawn entry 0. -/
theorem toy_slips (b : Bool) : relOut lt () (dr (false, b)) ((1, 2) : ℤ × ℤ) (dg 0 1) :=
  out_of (1, 2) (false, b) 0 1 (by norm_num) (by norm_num) (by simp [Prob.Coef.val])
    (by simp [Prob.Coef.val])

/-- The error at the toy: 2 of 4. -/
theorem toy_eps : TWhole.errList (eps lt) = [2] ∧ Fintype.card (Dr sz) = 4 := by
  have h : Fintype.card (Dr sz) = 4 := by
    rw [card_dr]
    simp [Size.columns]
  refine ⟨?_, h⟩
  show [Fintype.card (Dr sz) / 2 ^ 1] = [2]
  rw [h]
  norm_num

end Cb.Pv.Tail.Toy

#print axioms Cb.Pv.Tail.Toy.toy_hole
#print axioms Cb.Pv.Tail.Toy.toy_in
#print axioms Cb.Pv.Tail.Toy.toy_tooth
#print axioms Cb.Pv.Tail.Toy.toy_big
#print axioms Cb.Pv.Tail.Toy.toy_out
#print axioms Cb.Pv.Tail.Toy.toy_slips
#print axioms Cb.Pv.Tail.Toy.toy_eps
