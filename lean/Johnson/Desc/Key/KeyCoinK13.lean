-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyCoinK13.lean: THE BRIDGE «At», SECOND HALF: A ROW ON THE MATRIX IN THE KIND K13's LAW's COIN (Johnson/Desc/K13/Law/Means.lean: Holds: the multilinear extension of gᵀM at the point psi, plus the mask form, is the target) AGAINST THE
LIBRARY's (OnBytes/Slice/KeyLeaves.lean: TRowF.Holds: the double sum over rows and columns BY NUMBERS), which tensorRowHolds_iff (Johnson/Desc/Key/KeyCoin.lean) ties to the table's own TensorRowHolds. In the field GE alone; no machine sum.
  matN w            K13's typed matrix (rows Fin nR; a column by the bits of its number, THE LOWEST FIRST) as a function of two numbers; 0 beyond the rows
  k13Holds_iff      PROVED: K13.Law.Holds Reading.gl w x ⇔ (Leaves.readTRow x).Holds ⟨w.mask⟩ (matN w) nR k, WHERE THE ROW's POINT HAS JUST k COORDINATES
  witOf m mat mk    THE KIND K13's TYPED WITNESS OUT OF THE TABLE's READERS: the matrix read in the field, typed by Fin m.rows and the column's bits; the mask entries read
  tensorRowHolds_iff_k13   PROVED: **THE BRIDGE «At», WHOLE**: TensorRowHolds sameGl m mat mk x ⇔ K13.Law.Holds Reading.gl (witOf m mat mk) x, under x.psi.length = m.kCol
THE PREMISE x.psi.length = k IS NEEDED: K13's rd reads k coordinates (one that lacks counts as 0; one beyond does not count); the library's eqW reads the whole list.
Nothing on soundness.
-/
import Johnson.Desc.K13.Law.Means
import Johnson.Desc.Key.KeyCoin
import OnBytes.Slice.SimBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Slice OnBytes.Model
open VerifiableInference.Desc.K13.Law (Holds lhs colOf weights formVal)
open Johnson.L5.Layers (rd)

variable {nR k : ℕ}

/-- K13's typed matrix, by numbers. -/
def matN (w : K13.Law.Wit Cb.Gl.E nR k) (r c : ℕ) : Cb.Gl.E :=
  if h : r < nR then w.mat ⟨r, h⟩ (fun t => c.testBit t.val) else 0

theorem matN_rowNo (w : K13.Law.Wit Cb.Gl.E nR k) (i : Fin nR) (β : Fin k → Bool) : matN w i.val (Sz.rowNo β) = w.mat i β := by
  unfold matN
  rw [dif_pos i.isLt]
  exact congrArg (w.mat i) (funext fun t => testBit_rowNo β t)

theorem form_read (mask : Slot → Cb.Gl.E) (m : MaskForm) : (⟨mask⟩ : PscF.World).form (readForm m) = formVal Reading.gl mask m := by
  unfold PscF.World.form readForm formVal
  rw [List.map_map]
  rfl

/-- **The two coins of a row on the matrix are one.** -/
theorem k13Holds_iff (w : K13.Law.Wit Cb.Gl.E nR k) (x : TensorRow) (hk : x.psi.length = k) :
    Holds Reading.gl w x ↔ (Leaves.readTRow x).Holds ⟨w.mask⟩ (matN w) nR k := by
  have key : Alg.mle (colOf w (weights Reading.gl nR x.g)) (rd Reading.gl k x.psi) =
      ∑ r ∈ Finset.range nR, ∑ c ∈ Finset.range (2 ^ k), (Leaves.readTRow x).g r * Leaves.eqW (Leaves.readTRow x).psi c * matN w r c := by
    rw [Finset.sum_range]
    have e1 : ∀ i : Fin nR, ∑ c ∈ Finset.range (2 ^ k), (Leaves.readTRow x).g i.val * Leaves.eqW (Leaves.readTRow x).psi c * matN w i.val c =
        ∑ β : Fin k → Bool, weights Reading.gl nR x.g i * Alg.eqk (rd Reading.gl k x.psi) β * w.mat i β := by
      intro i
      rw [sum_range_cube]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [matN_rowNo]
      have e2 : Leaves.eqW (Leaves.readTRow x).psi (Sz.rowNo β) = Alg.eqk (rd Reading.gl k x.psi) β := by
        show Leaves.eqW (x.psi.map readE) (Sz.rowNo β) = _
        rw [eqW_two, hk, eqW_rowNo]
        rfl
      rw [e2]
      rfl
    rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_comm]
    unfold Alg.mle colOf
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold Holds lhs Leaves.TRowF.Holds
  rw [key]
  show _ + formVal Reading.gl w.mask x.masks = _ ↔ _ + (⟨w.mask⟩ : PscF.World).form (readForm x.masks) = readE x.target
  rw [form_read]
  exact Iff.rfl

/-- The kind K13's typed witness out of the table's readers. -/
def witOf (m : Wf.Matrix) (mat : Nat → Nat → F) (mk : Slot → E) : K13.Law.Wit Cb.Gl.E m.rows m.kCol :=
  ⟨fun i β => readE (ofF (mat i.val (Sz.rowNo β))), fun s => readE (mk s)⟩

theorem holds_congr (W : PscF.World) (M M' : ℕ → ℕ → Cb.Gl.E) (nRows kCol : ℕ) (t : Leaves.TRowF)
    (h : ∀ r c, r < nRows → c < 2 ^ kCol → M r c = M' r c) : t.Holds W M nRows kCol ↔ t.Holds W M' nRows kCol := by
  unfold Leaves.TRowF.Holds
  have e : (∑ r ∈ Finset.range nRows, ∑ c ∈ Finset.range (2 ^ kCol), t.g r * Leaves.eqW t.psi c * M r c) =
      ∑ r ∈ Finset.range nRows, ∑ c ∈ Finset.range (2 ^ kCol), t.g r * Leaves.eqW t.psi c * M' r c :=
    Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun c hc => by
      rw [h r c (Finset.mem_range.1 hr) (Finset.mem_range.1 hc)]
  rw [e]

/-- **The bridge «At», whole: the table's own sentence on a row on the matrix against the kind K13's law's.** -/
theorem tensorRowHolds_iff_k13 (m : Wf.Matrix) (mat : Nat → Nat → F) (mk : Slot → E) (x : TensorRow) (hk : x.psi.length = m.kCol) :
    TensorRowHolds sameGl m mat mk x ↔ Holds Reading.gl (witOf m mat mk) x := by
  rw [tensorRowHolds_iff, k13Holds_iff (witOf m mat mk) x hk]
  refine holds_congr _ _ _ _ _ _ fun r c hr hc => ?_
  unfold matN witOf
  rw [dif_pos hr]
  show _ = readE (ofF (mat r (Sz.rowNo fun t : Fin m.kCol => c.testBit t.val)))
  rw [rowNo_testBit, Nat.mod_eq_of_lt hc]

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.tensorRowHolds_iff_k13
#print axioms VerifiableInference.Desc.Key.k13Holds_iff
