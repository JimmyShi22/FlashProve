-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Means.lean: what a row on the committed matrix says, read in a field.

A row (`TensorRow`, OnBytes/Iop/Batt.lean) is data of the verifier: weights on the rows of the
matrix, a column point, a linear form in mask entries, a target. This file says when such a row is
true of a matrix and of mask entries. Definitions alone.

The form is the library's: < g (x) eq(psi, .), M > is `Alg.mle` of the vector g^T M on the columns,
at the point psi, as in `Cb.BattPar.ten` (Cb/Ld/LdBatt.lean). That the two agree is a theorem of
Johnson/Desc/K13/Law/Fit.lean (`inHolds_iff`).
Main names:
  `Wit K nR k`: the entries of a matrix of nR rows and 2^k columns; a value for every mask entry.
  `weights`, `formVal`, `colOf`: the weights of a row as a vector; the value of a mask form; g^T M.
  `lhs`, `Holds`: the row's left side; the row is true.
  `claimRow`, `HoldsClaim`: the same of the claim of the test on the table (`LinClaim`).
Used of `verify-on-bytes`, as data or as pure functions: `TensorRow`, `LinClaim`, `Slot`,
`MaskForm`, `Single`, `Tensor.entry`; `Reading` (OnBytes/Model/HideLaws.lean); `rd`
(OnBytes/Tie/Pv/Psc/PscRead.lean).

What is not claimed. That the kinds in front lay rows with this meaning, or that the test on the
table shows a claim with this meaning. A weight's entries from row nR on do not count. A coordinate
of the column point beyond the k-th does not count; one that lacks counts as 0.

-/
import OnBytes.Iop.Lin
import OnBytes.Tie.Pv.Psc.PscRead
import Alg.Mle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model
open Johnson.L5.Layers (rd)

/-- What the prover is bound to before the batching: the matrix, and every mask entry. -/
structure Wit (K : Type) (nR k : ℕ) where
  /-- the matrix: row, column; a column is named by the bits of its number, the lowest first -/
  mat : Fin nR → (Fin k → Bool) → K
  /-- the mask entries -/
  mask : Slot → K

variable {K : Type} [Field K] (ρ : Reading K) {nR k : ℕ}

/-- The weights on the rows of the matrix: the sum of the tensors, entry by entry. -/
def weights (nR : ℕ) (g : List Tensor) : Fin nR → K := fun i =>
  (g.map fun t => ρ.val (t.entry i)).sum

/-- The value of a mask form. -/
def formVal (mask : Slot → K) (m : MaskForm) : K := (m.map fun t => ρ.val t.2 * mask t.1).sum

/-- v^T M, a vector on the columns. -/
def colOf (w : Wit K nR k) (v : Fin nR → K) : (Fin k → Bool) → K := fun c => ∑ i, v i * w.mat i c

/-- The left side of a row: < g (x) eq(psi, .), M > + the mask form. -/
def lhs (w : Wit K nR k) (r : TensorRow) : K :=
  Alg.mle (colOf w (weights ρ nR r.g)) (rd ρ k r.psi) + formVal ρ w.mask r.masks

/-- The row is true. -/
def Holds (w : Wit K nR k) (r : TensorRow) : Prop := lhs ρ w r = ρ.val r.target

/-- The claim of the test on the table, as a row. An entry of another part than the mask rows is
read as the mask entry of that number. -/
def claimRow (c : LinClaim) : TensorRow where
  g := c.g
  psi := c.psi
  masks := c.masks.toList.map fun s => (⟨s.oracle, s.index⟩, s.coeff)
  target := c.target

/-- The claim is true. -/
def HoldsClaim (w : Wit K nR k) (c : LinClaim) : Prop := Holds ρ w (claimRow c)

end VerifiableInference.Desc.K13.Law
