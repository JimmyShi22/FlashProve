-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EntryCells.lean: the entries entryTrue (Johnson/Road/K4/EntryTrue.lean) read of the
matrices M THE CELLS INSIDE THE APPROXIMATE RANGE PROOF's OWN RANGES ALONE: matrix a below the
structure's number of matrices, row r below that matrix's rows, column c below its columns. So two
readers of the first sending's matrices that agree inside the ranges, and may part outside, give one
entryTrue.

Why. One reader of a witness cuts each table to its range and another reads it uncut: as functions
on all natural numbers the two part, at a witness that holds something beyond a range. An equation M
= M' between them is then false, and a law that asks it can be called by nobody.

  `InRange tl M M'`: M and M' agree at every cell inside tl's ranges.
  `saysOf_cells`: a table's sum at a place that tabAt names reads cells inside the ranges alone.
  `entryOf_cells`, `entryTrue_cells`: so the entries are the same, as functions.
  `entryTrue_range`: with two structures of one list of rows and columns (entryTrue_tl,
    Johnson/Road/K4/EntrySame.lean).
No new argument: tabAt_some (OnBytes/Tie/Pv/Tail/LettersAt.lean).
Limits. InRange is a PREMISE: that two given readers agree inside the ranges is shown by nobody
here. Nothing on soundness.


-/
import Johnson.Road.K4.EntrySame
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading HFun HTailF2)
open OnBytes.Model.Layer (Own)

variable {K : Type} [Field K]

/-- M and M' agree at every cell inside the ranges of tl. -/
def InRange (tl : HTailF2) (M M' : Mats K) : Prop :=
  ∀ a r c, a < tl.NM → r < (tl.mats.getD a {}).m → c < (tl.mats.getD a {}).k → M a r c = M' a r c

/-- A table's sum at a place that tabAt names reads cells inside the ranges alone. -/
theorem saysOf_cells (ρ : Reading K) {tl : HTailF2} {M M' : Mats K} (h : InRange tl M M')
    {Fn : HFun} {c sg pos : ℕ} (hp : tl.tabAt Fn c sg = some pos) :
    saysOf ρ M Fn c sg = saysOf ρ M' Fn c sg := by
  obtain ⟨h1, h2, h3, _⟩ := OnBytes.Tie.Pv.Tail.tabAt_some tl hp
  unfold saysOf
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < Fn.len := mem_range.mp hj
  have hr : sg * Fn.len + j < (tl.mats.getD Fn.mat {}).m := by
    have a1 : (sg + 1) * Fn.len ≤ (tl.mats.getD Fn.mat {}).m / Fn.len * Fn.len :=
      Nat.mul_le_mul_right _ h3
    have a2 := Nat.div_mul_le_self (tl.mats.getD Fn.mat {}).m Fn.len
    have a3 : (sg + 1) * Fn.len = sg * Fn.len + Fn.len := by ring
    omega
  rw [h Fn.mat _ c h1 hr h2]

/-- The entries are the same, as functions. -/
theorem entryOf_cells (ρ : Reading K) {tl : HTailF2} {M M' : Mats K} (h : InRange tl M M')
    (funs : Array HFun) (iU3 K3 : ℕ) :
    entryOf ρ tl funs iU3 K3 M = entryOf ρ tl funs iU3 K3 M' := by
  classical
  funext a r i
  unfold entryOf
  by_cases ha : a = iU3
  · rw [if_pos ha, if_pos ha]
    by_cases hx : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧ tl.tabAt x.1 x.2.1 x.2.2 = some (r * K3 + i)
    · rw [dif_pos hx, dif_pos hx]
      exact saysOf_cells ρ h hx.choose_spec.2
    · rw [dif_neg hx, dif_neg hx]
  · rw [if_neg ha, if_neg ha]

theorem entryTrue_cells {tl : HTailF2} {M M' : Mats Cb.Gl.E} (h : InRange tl M M') (o : Own) :
    entryTrue tl o M = entryTrue tl o M' :=
  entryOf_cells _ h _ _ _

/-- With two structures of one list of rows and columns. -/
theorem entryTrue_range {tl tl' : HTailF2}
    (hm : (tl.mats.map fun M => (M.m, M.k)) = tl'.mats.map fun M => (M.m, M.k))
    (hN : tl.NM = tl.mats.size) (hN' : tl'.NM = tl'.mats.size) {M M' : Mats Cb.Gl.E}
    (h : InRange tl M M') (o : Own) : entryTrue tl o M = entryTrue tl' o M' :=
  (entryTrue_cells h o).trans (entryTrue_tl hm hN hN' o M')

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.saysOf_cells
#print axioms OnBytes.Road.K4.entryOf_cells
#print axioms OnBytes.Road.K4.entryTrue_cells
#print axioms OnBytes.Road.K4.entryTrue_range
