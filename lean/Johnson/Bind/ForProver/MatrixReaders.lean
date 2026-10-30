-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/MatrixReaders.lean: THE INDEX'S READER IS THE PLAIN READER OF THE LIBRARY'S
MATRIX OF THAT INDEX. Two statements and their proofs; the full size.

Why. An honest prover's parts read the relation's index by row and column in the base field
(`OnBytes.HonestTrace.entryOf`, Johnson/HonestTrace/IndexReaders.lean). The library's typed encoder
takes a matrix of cells over the extension field; at an index that matrix is
`VerifiableInference.OnPublicFiles.Flat.matrixOf`, and its plain reader is `AtPublicFiles.Key.cellsReader` (the
library's E2E/KeyReaders.lean). A sentence that is stated at the relation's index is carried to the
typed input through `matrixOf`: here the two readers are shown to be one.

Main names (namespace `Bind.ForProver`).
  `entry_matrixOf`: at the typed addresses `entryOf i` is the first coordinate of `matrixOf i`.
  **`cellsReader_matrixOf`**: as whole functions of two numbers: `cellsReader (matrixOf i)` is
    `entryOf i`.

Limits. Off one law of this folder (the library's matrix of an index is the cast of the index's
integers: `cellsOfF_matrixOf`, Johnson/Bind/ForProver/JoinsSizes.lean), the two readers' texts, and
that outside the matrix's shape the index's reader is 0 (`OnBytes.HonestTrace.entryOf_out`). That
the shape of `matrixOf` (hRef rows, 2^kRef columns) is the reference matrix's numbers at the full
size is used up to unfolding. No coin, no table, no encoder is named. Of a cell the first coordinate
alone is read; of the others nothing is said here. This file writes no honest prover. No
completeness, no index privacy, no soundness; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.JoinsSizes
import Johnson.HonestTrace.IndexReaders
import E2E.KeyReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (frS frZ)
open VerifiableInference.OnPublicFiles (numsRef)
open VerifiableInference.OnPublicFiles.Flat (matrixOf)
open AtPublicFiles.Key (cellsReader)

/-- **At the typed addresses the index's reader is the first coordinate of the library's matrix of
that index.** Off the law that this matrix is the cast of the index's integers, and the reader's
text. -/
theorem entry_matrixOf (i : Cm.Idx) (y : Fin numsRef.rows)
    (c : Fin (2 ^ (numsRef.kLo + frS.P.v))) :
    OnBytes.HonestTrace.entryOf i y.val c.val = (matrixOf i y c).c0 :=
  congrArg (fun M : OnBytes.Flat.Cells (frS.toDecR frZ 402653181) numsRef => (M y c).c0)
    (cellsOfF_matrixOf i)

/-- **As whole functions: the plain reader of the library's matrix of an index is the index's
reader.** Outside the matrix's shape both are 0. -/
theorem cellsReader_matrixOf (i : Cm.Idx) :
    cellsReader (matrixOf i) = OnBytes.HonestTrace.entryOf i := by
  funext y c
  unfold cellsReader
  by_cases h : y < Inst.Model.Layout.hRef ∧ c < 2 ^ Inst.Model.Layout.kRef
  · rw [dif_pos h]
    exact (entry_matrixOf i ⟨y, h.1⟩ ⟨c, h.2⟩).symm
  · rw [dif_neg h]
    exact (OnBytes.HonestTrace.entryOf_out i h).symm

end Bind.ForProver

end

#print axioms Bind.ForProver.entry_matrixOf
#print axioms Bind.ForProver.cellsReader_matrixOf
