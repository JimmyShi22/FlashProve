-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Tail/HostVal.lean: a value of the frame's letters at which the three laws of
Cb/Pv/Tail/InLink.lean hold.

The seam in front of the smallness test's round (`host_seam`) asks three laws of a frame's letters.
An entry of a committed symbol array is a packed symbol: no committed entry is a cell. So at early
entries that are the committed entries alone the first law fails. Here the early entries are the
committed ones and, beside them, the cells: the value at a cell's place is the cell behind the
committed symbols (`cellValS`). The late entries are the reads at their columns.

Main names:
  `msgV raw sym`: the early entries: the committed ones, and the cells behind the symbols.
  `affV`: the form of a read at a column, on the cells' places; 0 on the committed entries.
  `entV tab`: the late entries.
  `hcell_val`, `haff_val`, `htab_val`: the three laws, at `ic := Sum.inr` and `it := id`.

Limits: whoever takes this value reads "the cells" through `cellValS` everywhere: a frame's other
premises must be paid at the same early entries. The late entries are numbered by matrix, read and
column, not by their places in a committed vector.

Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.InLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open TWhole

variable {K : Type} [Field K] {s : Size} {J₀ M₁ U₁ : Type}

/-- The early entries: the committed ones, and the cells behind the committed symbols. -/
noncomputable def msgV (raw : M₁ → J₀ → K) (sym : M₁ → Syms K s) (m : M₁) : J₀ ⊕ JCell s → K :=
  Sum.elim (raw m) (cellValS (sym m))

/-- The late entries: the reads at their columns. -/
def entV (tab : U₁ → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → K) (u : U₁) : JTab s → K :=
  fun j => tab u j.1 j.2.1 j.2.2

/-- The form of a read at a column: its weights on the cells' places, 0 on the committed entries. -/
def affV (Λ : Letters K s) (x : Λ.X) (j : JTab s) : Aff K (J₀ ⊕ JCell s) :=
  ⟨Sum.elim (fun _ => 0) (affRead Λ x j).co, 0⟩

theorem hcell_val (raw : M₁ → J₀ → K) (sym : M₁ → Syms K s) (m : M₁) (j : JCell s) :
    msgV raw sym m (Sum.inr j) = cellValS (sym m) j := rfl

theorem haff_val [Fintype J₀] (Λ : Letters K s) (x : Λ.X) (j : JTab s) (v : J₀ ⊕ JCell s → K) :
    (affV (J₀ := J₀) Λ x j).val v = (affRead Λ x j).val fun i => v (Sum.inr i) := by
  have h0 : (affRead Λ x j).c0 = 0 := by
    obtain ⟨μ, r, c⟩ := j
    rfl
  unfold affV Aff.val
  rw [Fintype.sum_sum_type, h0]
  simp

omit [Field K] in
theorem htab_val (tab : U₁ → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → K) (u : U₁)
    (j : JTab s) : entV tab u j = tab u j.1 j.2.1 j.2.2 := rfl

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.hcell_val
#print axioms Cb.Pv.Tail.haff_val
#print axioms Cb.Pv.Tail.htab_val
