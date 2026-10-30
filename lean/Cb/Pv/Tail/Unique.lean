-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/Unique.lean: the cells behind committed symbols are a function of the committed messages.

The relation before the smallness test's round (`relIn`, Cb/Pv/Tail/Block.lean) says that there are
small cells. Under three inequalities on the shift, the radix and the characteristic of the ring, a
column of symbols has at most one column of small cells (`Alg.small_unique`, Alg/Range.lean). So
the cells can be named: `cellsOf` reads the committed symbols alone: neither the weights of the
reads nor the reads.

Main names:
  `Size.Uniq s p`: the three inequalities: 0 < beta; 4 beta - 1 ≤ rad;
    (4 beta - 2) (1 + rad + rad ^ 2) < p.
  `Packs`: a column of integers is small and has the committed packing. `packs_unique`.
  `cellsOf`: the cells behind the committed symbols (0 where there are none).
  `cells_eq`: any cells behind the committed messages are `cellsOf`.
  `cellsOK_cellsOf`: before the round, `cellsOf` are cells behind the committed messages.
  `cellsOf_congr`: two tuples of messages with the same symbols in a column have the same cells
    there.
  `uniq_gl`: the three inequalities hold at the shift 2 ^ 17, the radix 2 ^ 20 and the
    characteristic 2 ^ 64 - 2 ^ 32 + 1. `cellsOK_gl`: so at these numbers over `Cb.Gl.E`.

Limits: `cellsOf` is found by choice: no program is given. Two sub-proofs that read one array have
two sizes and two tuples of letters: `packs_unique` speaks of one column of symbols, whoever reads
it; that the two read the same symbols is not said here.

Terms: lean/GLOSSARY.md.

-/
import Cb.Gl.GlField
import Cb.Pv.Tail.Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail

/-- The three inequalities under which small cells are unique. -/
def Size.Uniq (s : Size) (p : ℕ) : Prop :=
  (0 : ℤ) < (s.beta : ℤ) ∧ 4 * (s.beta : ℤ) - 1 ≤ (s.rad : ℤ) ∧
    (4 * (s.beta : ℤ) - 2) * (1 + (s.rad : ℤ) + (s.rad : ℤ) ^ 2) < (p : ℤ)

variable {K : Type} [CommRing K] {s : Size} (Λ : Letters K s)

/-- The column a of integers is small and has the committed packing of column c of matrix μ. -/
def Packs (msg : Λ.M) (μ : Fin s.NM) (c : Fin (s.k μ)) (a : Fin (s.m μ) → ℤ) : Prop :=
  Alg.Small (s.beta : ℤ) a ∧ ∀ i', Λ.sym msg μ i' c = ((Alg.pack (s.rad : ℤ) a i' : ℤ) : K)

theorem packs_unique (p : ℕ) [CharP K p] (hu : s.Uniq p) {msg msg' : Λ.M} {μ : Fin s.NM}
    {c : Fin (s.k μ)} {a b : Fin (s.m μ) → ℤ} (hm : ∀ i', Λ.sym msg μ i' c = Λ.sym msg' μ i' c)
    (ha : Packs Λ msg μ c a) (hb : Packs Λ msg' μ c b) : a = b :=
  Alg.small_unique p hu.1 hu.2.1 hu.2.2 (le_refl _) ha.1 hb.1 fun i' => by
    rw [← ha.2 i', ← hb.2 i', hm i']

open Classical in
/-- The cells behind the committed symbols; 0 where there are none. -/
noncomputable def cellsOf (msg : Λ.M) (μ : Fin s.NM) (c : Fin (s.k μ)) : Fin (s.m μ) → ℤ :=
  if h : ∃ a, Packs Λ msg μ c a then h.choose else fun _ => 0

theorem packs_cellsOf {msg : Λ.M} {μ : Fin s.NM} {c : Fin (s.k μ)}
    (h : ∃ a, Packs Λ msg μ c a) : Packs Λ msg μ c (cellsOf Λ msg μ c) := by
  unfold cellsOf
  rw [dif_pos h]
  exact h.choose_spec

/-- Any cells behind the committed messages are `cellsOf`. -/
theorem cells_eq (p : ℕ) [CharP K p] (hu : s.Uniq p) {x : Λ.X} {msg : Λ.M}
    {a : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (h : CellsOK Λ x msg a) :
    a = cellsOf Λ msg := by
  funext μ c
  have ha : Packs Λ msg μ c (a μ c) := ⟨h.1 μ c, h.2.1 μ c⟩
  exact packs_unique Λ p hu (fun _ => rfl) ha (packs_cellsOf Λ ⟨_, ha⟩)

/-- Before the round, `cellsOf` are cells behind the committed messages. -/
theorem cellsOK_cellsOf (p : ℕ) [CharP K p] (hu : s.Uniq p) {x : Λ.X} {msg : Λ.M}
    (h : relIn Λ x msg) : CellsOK Λ x msg (cellsOf Λ msg) := by
  obtain ⟨a, ha⟩ := cells_of_relIn Λ h
  rw [← cells_eq Λ p hu ha]
  exact ha

/-- The same symbols in a column: the same cells there. -/
theorem cellsOf_congr {msg msg' : Λ.M} {μ : Fin s.NM} {c : Fin (s.k μ)}
    (hm : ∀ i', Λ.sym msg μ i' c = Λ.sym msg' μ i' c) :
    cellsOf Λ msg μ c = cellsOf Λ msg' μ c := by
  have e : ∀ a, Packs Λ msg μ c a ↔ Packs Λ msg' μ c a := fun a =>
    and_congr_right fun _ => forall_congr' fun i' => by rw [hm i']
  have e2 : Packs Λ msg μ c = Packs Λ msg' μ c := funext fun a => propext (e a)
  unfold cellsOf
  rw [e2]

/-- The three inequalities at the shift 2 ^ 17, the radix 2 ^ 20, the prime 2 ^ 64 - 2 ^ 32 + 1. -/
theorem uniq_gl {s : Size} (hb : s.beta = 2 ^ 17) (hr : s.rad = 2 ^ 20) : s.Uniq Cb.Gl.p := by
  unfold Size.Uniq
  rw [hb, hr]
  have hp : ((Cb.Gl.p : ℕ) : ℤ) = 2 ^ 64 - 2 ^ 32 + 1 := by
    show (((2 ^ 64 - 2 ^ 32 + 1 : ℕ) : ℕ) : ℤ) = 2 ^ 64 - 2 ^ 32 + 1
    norm_num
  rw [hp]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- At these numbers, over the cubic extension of the field with 2 ^ 64 - 2 ^ 32 + 1 elements. -/
theorem cellsOK_gl {s : Size} (Λ : Letters Cb.Gl.E s) (hb : s.beta = 2 ^ 17) (hr : s.rad = 2 ^ 20)
    {x : Λ.X} {msg : Λ.M} (h : relIn Λ x msg) : CellsOK Λ x msg (cellsOf Λ msg) :=
  cellsOK_cellsOf Λ Cb.Gl.p (uniq_gl hb hr) h

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.packs_unique
#print axioms Cb.Pv.Tail.cells_eq
#print axioms Cb.Pv.Tail.cellsOK_cellsOf
#print axioms Cb.Pv.Tail.cellsOf_congr
#print axioms Cb.Pv.Tail.uniq_gl
#print axioms Cb.Pv.Tail.cellsOK_gl
