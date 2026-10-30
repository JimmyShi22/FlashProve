-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRowOnW.lean: the library's sentence "a row on the matrix holds" (`TensorRowHolds`,
Johnson/Desc/Key/KeyWords.lean), read in the field, is a sentence on W = gᵀM alone. Statements and
proofs.

Why. The batching of the rows on the matrix hands on one row: weights g of the matrix's rows, a
column point, a mask form, a target. The prover then sends W = gᵀM, and what is tested further is
tested of W. This file has the identity of sums beneath that step, for the honest W; the step
itself, in the verifier's text, is not treated.

What is shown, with "the same" read as "the same reading" (`readE`):
  **`row_iff_w`**: the row x holds of the matrix exactly if the sum over the columns c of
    eq(x.psi; c) · W[c], plus the mask form at the masks' values, is the target: W the vector of
    E2E/KeyArrays.lean (`wAt`) at the row's own weights.
  `row_iff_wVal`: the same with W's entries as the machine elements `wVal`, of which the library's
    sentence `VIs` holds (`w_is`, E2E/KeyArrays.lean).

Limits. One step of mathematics on finite sums. That the verifier's row on W's oracle message says
the right side is not shown here. No mask, no coin, no round. Nothing on hiding follows from this
file.


-/
import E2E.KeyArrays

set_option autoImplicit false

namespace AtPublicFiles.Key
open Finset
open OnBytes.Slice (GF GE toF readE)
open VerifiableInference.Desc.Key (TensorRowHolds weightAt formAt sumE sumE_read)

/-- **A row on the matrix holds exactly if its column weights read the target off W.** -/
theorem row_iff_w (m : OnBytes.Wf.Matrix) (mat : ℕ → ℕ → OnBytes.F) (mk : OnBytes.Slot → OnBytes.E)
    (x : OnBytes.TensorRow) :
    TensorRowHolds (fun a b => readE a = readE b) m mat mk x ↔
      (∑ c ∈ range (2 ^ m.kCol), readE ((OnBytes.Tensor.eq x.psi).entry c) *
          wAt (fun y => readE (weightAt x.g y)) (fun y c => toF (mat y c)) m.rows c) +
        readE (formAt mk x.masks) = readE x.target := by
  have h : ∀ y, readE (sumE (2 ^ m.kCol) fun c => OnBytes.mulE
        (OnBytes.mulE (weightAt x.g y) ((OnBytes.Tensor.eq x.psi).entry c))
        (OnBytes.ofF (mat y c))) =
      ∑ c ∈ range (2 ^ m.kCol), readE (weightAt x.g y) *
        readE ((OnBytes.Tensor.eq x.psi).entry c) * algebraMap GF GE (toF (mat y c)) := fun y => by
    rw [sumE_read readE OnBytes.Slice.readE_zero OnBytes.Slice.readE_add]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [OnBytes.Slice.readE_mul, OnBytes.Slice.readE_mul, OnBytes.Slice.readE_ofF]
  unfold TensorRowHolds
  dsimp only
  rw [OnBytes.Slice.readE_add, sumE_read readE OnBytes.Slice.readE_zero OnBytes.Slice.readE_add,
    w_claim, Finset.sum_congr rfl fun y _ => h y]

/-- The same with W's entries as machine elements. -/
theorem row_iff_wVal (m : OnBytes.Wf.Matrix) (mat : ℕ → ℕ → OnBytes.F)
    (mk : OnBytes.Slot → OnBytes.E) (x : OnBytes.TensorRow) :
    TensorRowHolds (fun a b => readE a = readE b) m mat mk x ↔
      (∑ c ∈ range (2 ^ m.kCol), readE ((OnBytes.Tensor.eq x.psi).entry c) *
          readE (wVal x.g mat m.rows c)) + readE (formAt mk x.masks) = readE x.target := by
  rw [row_iff_w]
  have h : ∀ c, readE (wVal x.g mat m.rows c) =
      wAt (fun y => readE (weightAt x.g y)) (fun y c => toF (mat y c)) m.rows c := fun c => by
    unfold wVal
    rw [OnBytes.Slice.readE_ofTriple, OnBytes.Slice.toE_ofE]
  simp only [h]

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.row_iff_w
#print axioms AtPublicFiles.Key.row_iff_wVal
