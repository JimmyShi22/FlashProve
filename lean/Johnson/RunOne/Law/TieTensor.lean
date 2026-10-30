-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieTensor.lean: THE TABLE'S
"A ROW ON THE MATRIX HOLDS", IN MACHINE ELEMENTS, IS THE LIBRARY'S, IN THE FIELD:
TensorRowHolds (Johnson/Desc/Key/KeyWords.lean) at "two elements are the same where they read alike"
holds of a row exactly if the row, read (Leaves.readTRow, OnBytes/Slice/BlkLeavesTop.lean), holds
(TRowF.Holds, KeyLeaves.lean) of the matrix read, in the world of the mask entries read.

Main names:
  eqK_eqW: two texts of the equality weights are one. read_eqEntry: an entry of the program's
    equality vector, read.
  read_weightAt, read_formAt: the weight of a row of the matrix, and a form in mask entries, read.
  tensorRow_iff: THE IFF. holds_cut: the library's sentence reads the matrix inside its size.
  tensorRow_iff_cut: the iff at the matrix cut at its size, as the links' rows have it.

Object: definitions of two groups of files and of the library; no block's text.
User: none yet (meant: the items kclaims and pile against the links' Pend).
Letters: m, a matrix's size · mat, a matrix of machine words · mk, the mask entries · x, a row.

Limits. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieKeys
import Johnson.Desc.Key.KeySumRead
import Johnson.Desc.K14.Law.Tensors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieTensor
open OnBytes OnBytes.Slice
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Key (sumE sumE_read weightAt formAt TensorRowHolds)
open VerifiableInference.Desc.K3.KeyLaw (cutM)
open Johnson.RunOne.Law.TieKeys

/-- Two texts of the equality weights are one. -/
theorem eqK_eqW : ∀ (z : List GE) (j : ℕ), _root_.Desc.K14.Law.eqK z j = Leaves.eqW z j
  | [], _ => rfl
  | x :: z, j => by
    unfold _root_.Desc.K14.Law.eqK Leaves.eqW
    rw [eqK_eqW z]

/-- An entry of the program's equality vector, read. -/
theorem read_eqEntry (z : List E) (j : ℕ) :
    readE ((Tensor.eq z).entry j) = Leaves.eqW (z.map readE) j := by
  have h := _root_.Desc.K14.Law.entry_eq Reading.gl z oneE j
  have h' : readE ((Tensor.eq z).entry j) =
      readE oneE * _root_.Desc.K14.Law.eqK (z.map readE) j := h
  rw [h', readE_one, one_mul, eqK_eqW]

theorem read_weightFold (y : ℕ) : ∀ (g : List Tensor) (a : E),
    readE (g.foldl (fun s t => addE s (t.entry y)) a) =
      readE a + (g.map fun v => readE (v.entry y)).sum
  | [], a => by simp
  | t :: g, a => by
    rw [List.foldl_cons, read_weightFold y g, readE_add, List.map_cons, List.sum_cons]
    ring

/-- The weight of a row of the matrix, read. -/
theorem read_weightAt (g : List Tensor) (y : ℕ) :
    readE (weightAt g y) = (g.map fun v => readE (v.entry y)).sum := by
  unfold weightAt
  rw [read_weightFold, readE_zero, zero_add]

theorem read_formFold (mk : Slot → E) : ∀ (f : MaskForm) (a : E),
    readE (f.foldl (fun s x => addE s (mulE x.2 (mk x.1))) a) =
      readE a + (f.map fun x => readE x.2 * readE (mk x.1)).sum
  | [], a => by simp
  | x :: f, a => by
    rw [List.foldl_cons, read_formFold mk f, readE_add, readE_mul, List.map_cons, List.sum_cons]
    ring

/-- A form in mask entries, read. -/
theorem read_formAt (mk : Slot → E) (f : MaskForm) :
    readE (formAt mk f) = (⟨fun s => readE (mk s)⟩ : PscF.World).form (readForm f) := by
  unfold formAt PscF.World.form readForm
  rw [read_formFold, readE_zero, zero_add, List.map_map]
  rfl

/-- **THE TABLE'S "A ROW ON THE MATRIX HOLDS" IS THE LIBRARY'S.** -/
theorem tensorRow_iff (m : Wf.Matrix) (mat : ℕ → ℕ → F) (mk : Slot → E) (x : TensorRow) :
    TensorRowHolds (fun a b => readE a = readE b) m mat mk x ↔
      (Leaves.readTRow x).Holds ⟨fun s => readE (mk s)⟩ (matR mat) m.rows m.kCol := by
  unfold TensorRowHolds Leaves.TRowF.Holds Leaves.readTRow
  show readE _ = readE _ ↔ _
  rw [readE_add, read_formAt, sumE_read readE readE_zero readE_add]
  have e : ∀ y ∈ Finset.range m.rows,
      readE (sumE (2 ^ m.kCol) fun c => mulE (mulE (weightAt x.g y) ((Tensor.eq x.psi).entry c))
        (OnBytes.ofF (mat y c))) =
      ∑ c ∈ Finset.range (2 ^ m.kCol), (x.g.map fun v => readE (v.entry y)).sum *
        Leaves.eqW (x.psi.map readE) c * matR mat y c := fun y _ => by
    rw [sumE_read readE readE_zero readE_add]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [readE_mul, readE_mul, read_weightAt, read_eqEntry]
    rfl
  rw [Finset.sum_congr rfl e]

/-- The library's sentence reads the matrix inside its size. -/
theorem holds_cut (m : Wf.Matrix) (W : PscF.World) (M : ℕ → ℕ → GE) (t : Leaves.TRowF) :
    t.Holds W (cutM m M) m.rows m.kCol ↔ t.Holds W M m.rows m.kCol := by
  unfold Leaves.TRowF.Holds
  have e : ∑ r ∈ Finset.range m.rows, ∑ c ∈ Finset.range (2 ^ m.kCol),
      t.g r * Leaves.eqW t.psi c * cutM m M r c =
      ∑ r ∈ Finset.range m.rows, ∑ c ∈ Finset.range (2 ^ m.kCol),
        t.g r * Leaves.eqW t.psi c * M r c :=
    Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun c hc => by
      unfold cutM
      rw [if_pos ⟨Finset.mem_range.1 hr, Finset.mem_range.1 hc⟩]
  rw [e]

/-- The iff at the matrix cut at its size. -/
theorem tensorRow_iff_cut (m : Wf.Matrix) (mat : ℕ → ℕ → F) (mk : Slot → E) (x : TensorRow) :
    TensorRowHolds (fun a b => readE a = readE b) m mat mk x ↔
      (Leaves.readTRow x).Holds ⟨fun s => readE (mk s)⟩ (cutM m (matR mat)) m.rows m.kCol :=
  (tensorRow_iff m mat mk x).trans (holds_cut m _ _ _).symm

end Johnson.RunOne.Law.TieTensor

#print axioms Johnson.RunOne.Law.TieTensor.read_eqEntry
#print axioms Johnson.RunOne.Law.TieTensor.tensorRow_iff
#print axioms Johnson.RunOne.Law.TieTensor.tensorRow_iff_cut
