-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/Base.lean: the lift: behind committed symbols there is an integer matrix for each matrix.

A sub-proof commits to symbols: three integer cells of a column packed into one element of the
field. What a link's joints say of "the cells" they say through one map, `cellValS`
(Cb/Pv/Tail/InLink.lean), which reads the cells off the symbols. This file has the statement that
such cells are there, with the integers as a letter and under "there are".

Main names:
  `BaseAt y Mz`: the integers Mz are small; the symbols y are their packing; the cells read off y
    are their images in the field.
  `Base y`: there are such integers.
  `baseAt_of_packs`: under the three inequalities `Size.Uniq` the third clause follows from the
    first two.
  `baseAt_unique`: under the same, `BaseAt y Mz` names Mz: it is `cellsOf (symL K s) y`.
  `baseAt_of_relIn`, `base_of_relIn`: the input relation of the smallness test's round
    (Cb/Pv/Tail/Block.lean) gives both, of the committed symbols.
  `weak_base`: without the clause on the packing the statement holds of all symbols whatever, if the
    shift is not 0: `cellValS` is the image of a small integer by its definition. So the clause on
    the packing is what `Base` says.

Limits: nothing here says that symbols have cells: that is the smallness test's claim.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.InLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail

variable {K : Type} [Field K] {s : Size}

/-- The integers Mz are small, the symbols y are their packing, and the cells read off y are their
images. -/
def BaseAt (y : Syms K s) (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) : Prop :=
  (∀ μ c i, |Mz μ c i| < 2 * (s.beta : ℤ)) ∧
    (∀ μ c i', y μ i' c = ((Alg.pack (s.rad : ℤ) (Mz μ c) i' : ℤ) : K)) ∧
    ∀ j : JCell s, cellValS y j = ((Mz j.1 j.2.1 j.2.2 : ℤ) : K)

/-- Behind the symbols y there are such integers. -/
def Base (y : Syms K s) : Prop := ∃ Mz, BaseAt y Mz

/-- Small integers with the packing y are `cellsOf`. -/
theorem cellsOf_of_packs (p : ℕ) [CharP K p] (hu : s.Uniq p) {y : Syms K s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ}
    (h1 : ∀ μ c i, |Mz μ c i| < 2 * (s.beta : ℤ))
    (h2 : ∀ μ c i', y μ i' c = ((Alg.pack (s.rad : ℤ) (Mz μ c) i' : ℤ) : K)) :
    Mz = cellsOf (symL K s) y := by
  funext μ c
  have ha : Packs (symL K s) y μ c (Mz μ c) := ⟨h1 μ c, h2 μ c⟩
  exact packs_unique (symL K s) p hu (fun _ => rfl) ha (packs_cellsOf (symL K s) ⟨_, ha⟩)

theorem baseAt_of_packs (p : ℕ) [CharP K p] (hu : s.Uniq p) {y : Syms K s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ}
    (h1 : ∀ μ c i, |Mz μ c i| < 2 * (s.beta : ℤ))
    (h2 : ∀ μ c i', y μ i' c = ((Alg.pack (s.rad : ℤ) (Mz μ c) i' : ℤ) : K)) : BaseAt y Mz :=
  ⟨h1, h2, fun j => by rw [cellsOf_of_packs p hu h1 h2]; rfl⟩

theorem baseAt_unique (p : ℕ) [CharP K p] (hu : s.Uniq p) {y : Syms K s}
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (h : BaseAt y Mz) :
    Mz = cellsOf (symL K s) y := cellsOf_of_packs p hu h.1 h.2.1

theorem baseAt_of_relIn (Λ : Letters K s) (p : ℕ) [CharP K p] (hu : s.Uniq p) {x : Λ.X}
    {msg : Λ.M} (h : relIn Λ x msg) : BaseAt (Λ.sym msg) (cellsOf Λ msg) :=
  have g := cellsOK_cellsOf Λ p hu h
  ⟨g.1, g.2.1, fun _ => rfl⟩

theorem base_of_relIn (Λ : Letters K s) (p : ℕ) [CharP K p] (hu : s.Uniq p) {x : Λ.X} {msg : Λ.M}
    (h : relIn Λ x msg) : Base (Λ.sym msg) := ⟨_, baseAt_of_relIn Λ p hu h⟩

/-- Without the clause on the packing the statement holds of all symbols. -/
theorem weak_base (hb : 0 < s.beta) (y : Syms K s) :
    ∃ Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ,
      (∀ μ c i, |Mz μ c i| < 2 * (s.beta : ℤ)) ∧
      ∀ j : JCell s, cellValS y j = ((Mz j.1 j.2.1 j.2.2 : ℤ) : K) := by
  refine ⟨cellsOf (symL K s) y, fun μ c i => ?_, fun _ => rfl⟩
  by_cases h : ∃ a, Packs (symL K s) y μ c a
  · exact (packs_cellsOf (symL K s) h).1 i
  · unfold cellsOf
    rw [dif_neg h, abs_zero]
    have : (0 : ℤ) < (s.beta : ℤ) := by exact_mod_cast hb
    omega

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.baseAt_of_packs
#print axioms Cb.Pv.Tail.baseAt_unique
#print axioms Cb.Pv.Tail.baseAt_of_relIn
#print axioms Cb.Pv.Tail.base_of_relIn
#print axioms Cb.Pv.Tail.weak_base
