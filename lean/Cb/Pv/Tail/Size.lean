-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/Size.lean: the sizes and the data of the smallness test of a sub-proof. Definitions, and
the number of values that can be drawn.

A sub-proof commits to integer matrices. Three cells of one column are packed into one symbol. It
also commits to reads: each is meant to be a weighted sum of the cells of one column. The smallness
test draws a matrix with entries -1, 0, 1: tau entries for each column. The prover then sends, for
each row of cells and each of the tau combinations, the combination of that row's cells, shifted by
beta and cut into a low and a high digit. The mathematics of the test, without any protocol, is in
Alg/Range.lean; the types here are the ones that its statements take.

Main names:
  `Size`: the public numbers: for each matrix its rows of cells, its columns and its reads; tau; the
    radix of the packing; the sizes of the two digits' tables; the shift.
  `Size.OK`: the two digits together do not reach beyond twice the shift.
  `Dr s`: what is drawn: for each matrix, each combination and each column two bits
    (`Prob.Coef`, Prob/Window.lean: 0 with two of the four values, 1 and -1 with one each).
  `card_dr`, `flat`: it has 4 ^ (columns * tau) values: as many as lists of columns * tau pairs of
    bits.
  `Dig`: the digits. `comb`: a combination, as the digits give it.

Limits: all values lie in one commutative ring K: nothing here says that a symbol
or a digit is of a smaller field.

Terms: lean/GLOSSARY.md.

-/
import Alg.Range

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail

/-- The public numbers of the smallness test of one sub-proof. -/
structure Size where
  /-- the number of matrices -/
  NM : ℕ
  /-- rows of cells, columns and reads of a matrix -/
  m : ℕ → ℕ
  k : ℕ → ℕ
  nr : ℕ → ℕ
  /-- the number of random combinations -/
  tau : ℕ
  /-- the radix of the packing -/
  rad : ℕ
  /-- the sizes of the tables of the low and of the high digit -/
  lo : ℕ
  hi : ℕ
  /-- the shift of a combination -/
  beta : ℕ

/-- The two digits together do not reach beyond twice the shift. -/
def Size.OK (s : Size) : Prop := s.lo * s.hi ≤ 2 * s.beta

/-- the columns of all matrices together -/
def Size.columns (s : Size) : ℕ := ∑ μ : Fin s.NM, s.k μ

/-- What is drawn: two bits for each matrix, combination and column. -/
abbrev Dr (s : Size) : Type := ∀ μ : Fin s.NM, Fin s.tau → Fin (s.k μ) → Prob.Coef

/-- The number of values that can be drawn. -/
theorem card_dr (s : Size) : Fintype.card (Dr s) = 4 ^ (s.columns * s.tau) := by
  have h : ∀ μ : Fin s.NM,
      Fintype.card (Fin s.tau → Fin (s.k μ) → Prob.Coef) = 4 ^ (s.k μ * s.tau) := by
    intro μ
    simp [pow_mul]
  rw [Fintype.card_pi, Finset.prod_congr rfl fun μ _ => h μ, Finset.prod_pow_eq_pow_sum,
    Size.columns, Finset.sum_mul]

/-- What is drawn, as one list of pairs of bits. -/
theorem flat (s : Size) : Nonempty (Dr s ≃ (Fin (s.columns * s.tau) → Bool × Bool)) :=
  ⟨Fintype.equivOfCardEq (by rw [card_dr]; simp)⟩

/-- The digits: matrix, combination, row of cells. -/
structure Dig (K : Type) (s : Size) where
  zl : ∀ μ : Fin s.NM, Fin s.tau → Fin (s.m μ) → K
  zh : ∀ μ : Fin s.NM, Fin s.tau → Fin (s.m μ) → K

/-- A combination, as the digits give it. -/
def comb {K : Type} [CommRing K] {s : Size} (Z : Dig K s) (μ : Fin s.NM) (u : Fin s.tau) :
    Fin (s.m μ) → K :=
  fun i => Z.zl μ u i + (s.lo : K) * Z.zh μ u i - (s.beta : K)

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.card_dr
#print axioms Cb.Pv.Tail.flat
