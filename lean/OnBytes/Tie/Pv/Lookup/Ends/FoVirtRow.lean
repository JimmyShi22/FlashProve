-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoVirtRow.lean: the law of a virtual row: its entries are a combination
of the rows of its array.

A claim of the byte-level verifier may name entries of a virtual row of an array. In a world
(OnBytes.Model.World) such an entry is any value. That virtual row e of array t is the combination,
under given weights, of the array's own rows is a proposition on the world.

 - VirtRow entry t e wt cellAt rows n: for each index i below n, entry i of virtual row e of array t
   is the sum over the array's rows r of wt r times the array's entry in row r at index i. General
   in the array, the row, the weights and the entries.
 - virtRow_some: some world meets it; virtRow_pins: it fixes the row's n entries.
 - runSum_range: the sum in which the value of a run is written (OnBytes/Model/TreesLaws.lean), as a
   sum over a range.
 - run_virt: under VirtRow, the sum of a run's weights times the row's entries is the double sum
   over the array's columns and rows.

VirtRow is a hypothesis wherever it stands.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that VirtRow holds of any committed array.

-/
import OnBytes.Model.TreesLaws
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace Fo
open Finset OnBytes.Model

section
variable {K : Type} [CommRing K]

/-- Virtual row e of array t is the combination of the array's rows under the weights wt. -/
def VirtRow (entry : ℕ → ℕ → ℕ → K) (t e : ℕ) (wt : ℕ → K) (cellAt : ℕ → ℕ → K) (rows n : ℕ) :
    Prop :=
  ∀ i < n, entry t e i = ∑ r ∈ range rows, wt r * cellAt r i

theorem virtRow_some (t e : ℕ) (wt : ℕ → K) (cellAt : ℕ → ℕ → K) (rows n : ℕ) :
    ∃ entry, VirtRow entry t e wt cellAt rows n :=
  ⟨fun _ _ i => ∑ r ∈ range rows, wt r * cellAt r i, fun _ _ => rfl⟩

theorem virtRow_pins {e₁ e₂ : ℕ → ℕ → ℕ → K} {t e : ℕ} {wt : ℕ → K} {cellAt : ℕ → ℕ → K}
    {rows n : ℕ} (h₁ : VirtRow e₁ t e wt cellAt rows n) (h₂ : VirtRow e₂ t e wt cellAt rows n)
    (i : ℕ) (hi : i < n) : e₁ t e i = e₂ t e i := (h₁ i hi).trans (h₂ i hi).symm

theorem runSum_from (f : ℕ → K) : ∀ n i, runSum f n i = ∑ j ∈ range n, f (i + j)
  | 0, _ => rfl
  | n + 1, i => by
    rw [Finset.sum_range_succ']
    show f i + runSum f n (i + 1) = _
    rw [runSum_from f n (i + 1), Nat.add_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_assoc, Nat.add_comm 1 j]

theorem runSum_range (f : ℕ → K) (n : ℕ) : runSum f n 0 = ∑ j ∈ range n, f j := by
  rw [runSum_from]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.zero_add]

/-- A run on a virtual row, on the array's own entries. -/
theorem run_virt {entry : ℕ → ℕ → ℕ → K} {t e : ℕ} {wt : ℕ → K} {cellAt : ℕ → ℕ → K}
    {rows n : ℕ} (h : VirtRow entry t e wt cellAt rows n) (w : ℕ → K) :
    runSum (fun i => w i * entry t e i) n 0 =
      ∑ i ∈ range n, w i * ∑ r ∈ range rows, wt r * cellAt r i := by
  rw [runSum_range]
  exact Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]

end
end Fo
