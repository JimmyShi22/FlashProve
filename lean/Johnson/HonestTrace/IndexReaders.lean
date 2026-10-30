-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/IndexReaders.lean

Two readers of an index at the full (reference) size: the committed matrix of the weights' digits by
row and column, and the model's weight tensors; and what ties the two.

The pieces of an honest prover, which are written elsewhere, read what all requests share, the
index, in two ways. Those on the committed weights read a matrix of digits by row and column. The
trace of the model's run is made of the weight tensors. In this library an index at the reference
sizes is "Cm.Idx": a well-formed matrix of digits. The tensors are what the layout reads from that
matrix. This file names the two readers and quotes the theorems that tie them, so that a caller of
the trace (Johnson/HonestTrace/Full.lean) can say through which reader each term reads the index.

Main definitions and theorems:
* "entryZ", "entryOf": the entry of the matrix of digits at a row and a column, as an integer and in
  the field; 0 outside the matrix's shape ("entryZ_out", "entryOf_out"). "entryZ_byte": inside the
  shape it is a signed byte.
* "tensorsOf": the weight tensors that the layout reads from the matrix.
* "tensorsOf_eq", "index_val_eq": the tensors are "Layout.weightsOf" of the matrix, and they are the
  weights of "i.index". Both hold by definition.
* "tensorsOf_ofIndex", "entryZ_ofIndex": the way back. For well-formed tensors j the index
  "Cm.Idx.ofIndex j" has the tensors j, and its matrix is "Layout.matrixRef j".
* "idx_ext": two indices with the same integer entries are one index.
* "servesAt_iff_tensors": "ServesAt" reads of the index the tensors alone.
* "honAt_eq_entries": the honest cells read of the index the integer entries alone.

Limits. All is at the reference model's sizes. Nothing here says that "Cm.Idx.ofIndex i.index" is i:
whether two well-formed matrices can hold the same tensors is not settled in this file. So the
honest cells, which are written over the matrix, are not shown here to be a function of the tensors.
"entryOf" is the image of a signed byte in the field; that the image determines the byte is not
stated here.

Not claimed: anything on a commitment, a key file or a proof.

-/
import Johnson.HonestTrace.Full
import Cm.RelTrue

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)
open OnBytes.Road
open VerifiableInference.OnPublicFiles.Flat (scalesAt)

/-- The entry of the index's matrix of the weights' digits at row r and column c, as an integer. -/
def entryZ (i : Cm.Idx) (r c : ℕ) : ℤ := i.mat r c

/-- **The first reader: the committed matrix of the weights' digits, by row and column, in the
field.** -/
def entryOf (i : Cm.Idx) (r c : ℕ) : Cb.Gl.F := ((entryZ i r c : ℤ) : Cb.Gl.F)

/-- **The second reader: the model's weight tensors**, as the layout reads them from the matrix. -/
def tensorsOf (i : Cm.Idx) : Weights := i.weights

/-- Outside the matrix's shape (hRef rows, 2^kRef columns) the integer entry is 0. -/
theorem entryZ_out (i : Cm.Idx) {r c : ℕ} (h : ¬ (r < hRef ∧ c < 2 ^ kRef)) : entryZ i r c = 0 := by
  show Cm.ext i.val r c = 0
  unfold Cm.ext
  rw [dif_neg h]

/-- Outside the matrix's shape the entry in the field is 0. -/
theorem entryOf_out (i : Cm.Idx) {r c : ℕ} (h : ¬ (r < hRef ∧ c < 2 ^ kRef)) :
    entryOf i r c = 0 := by
  unfold entryOf
  rw [entryZ_out i h, Int.cast_zero]

/-- Inside the shape the integer entry is a signed byte. -/
theorem entryZ_byte (i : Cm.Idx) {r c : ℕ} (hr : r < hRef) (hc : c < 2 ^ kRef) :
    -2 ^ 7 ≤ entryZ i r c ∧ entryZ i r c < 2 ^ 7 :=
  i.wf.1 r hr c hc

/-- The tensors are what the library's layout reads from the matrix. It holds by definition. -/
theorem tensorsOf_eq (i : Cm.Idx) : tensorsOf i = Layout.weightsOf ppref kRef (entryZ i) := rfl

/-- The tensors are the weights of the index in the form "Index ppref". It holds by definition. -/
theorem index_val_eq (i : Cm.Idx) : i.index.val = tensorsOf i := rfl

/-- For well-formed tensors j the index "Cm.Idx.ofIndex j" has the tensors j
("Cm.weights_ofIndex"). -/
theorem tensorsOf_ofIndex (j : Index ppref) : tensorsOf (Cm.Idx.ofIndex j) = j.val :=
  Cm.weights_ofIndex j

/-- The matrix of "Cm.Idx.ofIndex j" is the library's matrix of the tensors j, "Layout.matrixRef j"
("Cm.mat_ofIndex"). -/
theorem entryZ_ofIndex (j : Index ppref) : entryZ (Cm.Idx.ofIndex j) = Layout.matrixRef j :=
  Cm.mat_ofIndex j

/-- Two indices with the same integer entries are one index. -/
theorem idx_ext {i j : Cm.Idx} (h : entryZ i = entryZ j) : i = j := by
  apply Subtype.ext
  funext r c
  have e := congrFun (congrFun h r.val) c.val
  have ei : entryZ i r.val c.val = i.val r c := by
    show Cm.ext i.val r.val c.val = _
    unfold Cm.ext
    rw [dif_pos ⟨r.isLt, c.isLt⟩]
  have ej : entryZ j r.val c.val = j.val r c := by
    show Cm.ext j.val r.val c.val = _
    unfold Cm.ext
    rw [dif_pos ⟨r.isLt, c.isLt⟩]
  rw [← ei, ← ej]
  exact e

/-- **"ServesAt" reads of the index the tensors alone**: it is "Serves" at the tensors. It holds by
definition. -/
theorem servesAt_iff_tensors (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) :
    ServesAt X i x ↔
      Serves ppref (scalesAt X).kap (scalesAt X).nf (fun _ => tbRef) (Hd.polOf X.hS)
        (tensorsOf i) x :=
  Iff.rfl

/-- **The honest cells read of the index the integer entries alone**: they are "honTK" at the matrix
of these entries. It holds by definition. -/
theorem honAt_eq_entries (X : Model.Verify.Public) (i : Cm.Idx) (x : Instance ppref) :
    honAt X i x =
      honTK (scalesAt X).kap (scalesAt X).nf (fun _ => tbRef) (entryZ i) x.prompt
        (Head.Req.of (Hd.polOf X.hS) x) :=
  rfl

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.entryZ
#print axioms OnBytes.HonestTrace.entryOf
#print axioms OnBytes.HonestTrace.tensorsOf
#print axioms OnBytes.HonestTrace.entryZ_out
#print axioms OnBytes.HonestTrace.entryOf_out
#print axioms OnBytes.HonestTrace.entryZ_byte
#print axioms OnBytes.HonestTrace.tensorsOf_eq
#print axioms OnBytes.HonestTrace.index_val_eq
#print axioms OnBytes.HonestTrace.tensorsOf_ofIndex
#print axioms OnBytes.HonestTrace.entryZ_ofIndex
#print axioms OnBytes.HonestTrace.idx_ext
#print axioms OnBytes.HonestTrace.servesAt_iff_tensors
#print axioms OnBytes.HonestTrace.honAt_eq_entries
