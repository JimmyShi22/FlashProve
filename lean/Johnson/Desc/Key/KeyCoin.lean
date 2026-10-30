-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyCoin.lean: THE TABLE OF JOINTS' SENTENCES (KeyWords.lean: sums of the program's machine elements, compared by the letter same) AGAINST THE COIN OF THE KINDS' FILES (values in the field GE, read by readE), BY LEMMA: at same := «the two read as one element» (sameGl).
(The four definitions stay as they are; the coin is reached by lemma. RowHolds ⇔ Means.Says is proved in Johnson/Desc/Key/RowHoldsSays.lean: rowHolds_iff_says, under its premise OffTables.)
  sameGl                a b := readE a = readE b
  eqW_two               the library's two spellings of the equality vector's weight are one (Leaves.eqW on a list | Slice.eqW on a function)
  read_weightAt · read_formAt
  tensorRowHolds_iff    **PROVED**: TensorRowHolds sameGl m mat mk x ⇔ (Leaves.readTRow x).Holds ⟨readE ∘ mk⟩ (the matrix read) m.rows m.kCol: NO PREMISE
  holds_cut             the row's sums end at the matrix's size: so it holds of a matrix just if it holds of that matrix cut at its size (cutM, Johnson/Desc/First/Look/KeyLaw/Closed.lean)
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyWords
import Johnson.Desc.Key.KeySumRead
import OnBytes.Slice.BlkLeavesTop
import OnBytes.Slice.BlkTens

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Slice

/-- Two machine elements read as one element of the field. -/
def sameGl (a b : E) : Prop := readE a = readE b

/-- It is the filling of same in RowHoldsSays.lean (fun a b => ρ.val a = ρ.val b) at the library's reading Reading.gl. -/
theorem sameGl_eq : sameGl = fun a b => OnBytes.Model.Reading.gl.val a = OnBytes.Model.Reading.gl.val b := rfl

theorem eqW_two : ∀ (z : List E) (j : ℕ), Leaves.eqW (z.map readE) j = OnBytes.Slice.eqW z.length (readL z) j
  | [], j => (eqW_zero _ j).symm
  | x :: z, j => by
    rw [List.map_cons, List.length_cons, eqW_succ', Leaves.eqW_cons, eqW_two z (j / 2)]
    have e : (fun t => readL (x :: z) (t + 1)) = readL z := rfl
    rw [e]
    refine congrArg₂ (· * ·) ?_ rfl
    have h0 : readL (x :: z) 0 = readE x := rfl
    rw [h0, Nat.testBit_zero]
    by_cases hj : j % 2 = 1
    · simp [hj]
    · simp [hj]

theorem read_fold {α : Type} (f : α → E) : ∀ (l : List α) (s : E), readE (l.foldl (fun s t => addE s (f t)) s) = readE s + (l.map fun t => readE (f t)).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, read_fold f l, readE_add, List.map_cons, List.sum_cons, add_assoc]

theorem read_weightAt (g : List Tensor) (y : Nat) : readE (weightAt g y) = (g.map fun v => readE (v.entry y)).sum := by
  unfold weightAt
  rw [read_fold (fun t : Tensor => t.entry y), readE_zero, zero_add]

theorem read_formAt (mk : Slot → E) (f : MaskForm) : readE (formAt mk f) = (PscF.World.mk fun s => readE (mk s)).form (readForm f) := by
  unfold formAt PscF.World.form readForm
  rw [read_fold (fun x : Slot × E => mulE x.2 (mk x.1)), readE_zero, zero_add, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  exact readE_mul _ _

/-- **A row on the matrix holds, in the two coins.** -/
theorem tensorRowHolds_iff (m : Wf.Matrix) (mat : Nat → Nat → F) (mk : Slot → E) (x : TensorRow) :
    TensorRowHolds sameGl m mat mk x ↔ (Leaves.readTRow x).Holds ⟨fun s => readE (mk s)⟩ (fun y c => readE (ofF (mat y c))) m.rows m.kCol := by
  unfold TensorRowHolds sameGl Leaves.TRowF.Holds Leaves.readTRow
  rw [readE_add, read_formAt, sumE_read readE readE_zero readE_add]
  have e : ∀ y, readE (sumE (2 ^ m.kCol) fun c => mulE (mulE (weightAt x.g y) ((Tensor.eq x.psi).entry c)) (ofF (mat y c))) =
      ∑ c ∈ Finset.range (2 ^ m.kCol), (x.g.map fun v => readE (v.entry y)).sum * Leaves.eqW (x.psi.map readE) c * readE (ofF (mat y c)) := fun y => by
    rw [sumE_read readE readE_zero readE_add]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [readE_mul, readE_mul, read_weightAt, readE_eq, readE_one, one_mul, eqW_two]
  simp only [e]

/-- The row's sums end at the matrix's size. -/
theorem holds_cut (W : PscF.World) (M : ℕ → ℕ → GE) (nRows kCol : ℕ) (t : Leaves.TRowF) :
    t.Holds W (fun r c => if r < nRows ∧ c < 2 ^ kCol then M r c else 0) nRows kCol ↔ t.Holds W M nRows kCol := by
  unfold Leaves.TRowF.Holds
  have e : (∑ r ∈ Finset.range nRows, ∑ c ∈ Finset.range (2 ^ kCol), t.g r * Leaves.eqW t.psi c * (if r < nRows ∧ c < 2 ^ kCol then M r c else 0)) =
      ∑ r ∈ Finset.range nRows, ∑ c ∈ Finset.range (2 ^ kCol), t.g r * Leaves.eqW t.psi c * M r c :=
    Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun c hc => by
      rw [if_pos ⟨Finset.mem_range.1 hr, Finset.mem_range.1 hc⟩]
  rw [e]

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.tensorRowHolds_iff
#print axioms VerifiableInference.Desc.Key.holds_cut
