-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/All/Trace.lean: the trace of the whole model: one object for all 25 segments, and how
each segment reads it. Definitions (words of this library: lean/GLOSSARY.md).

* There are 12 groups of four layers. Group g has a feed-forward segment and an attention segment;
  the head comes last. Groups are counted from 0 here (g < 12; the first layer of group g is 4 g).
* `Trace` holds, for every segment, the cells that it owns: no cell that a segment reads is stored
  twice. (The type has names that nothing reads: the cells of x0 in ff g for g > 0; qry, key, val,
  out in att g; ff g and att g for g ≥ 12; all names that are not valid. So different terms of the
  type represent one trace.) A borrowed cell is read from the segment that owns it:
    `vFF`    x0 of the feed-forward segment of group g + 1 is x8 of that of group g, cell by cell;
    `vAtt`   qry, key, val, out of the attention segment of group g are q, kx, v, o of the
             feed-forward segment of the group: qry_b[g, i, n] is q of layer λ of the segment at
             position i and index 128 h + n, and so on (λ = `lamOf b`, h = `head g b`,
             Inst/Model/Att/Index.lean; here g is the key/value head);
    `vHead`  x of the head is x8 of the last feed-forward segment; feature 5,120 l + j is cell l
             of channel j.
-/
import Inst.Model.FF.Trace
import Inst.Model.Att.Trace
import Inst.Model.Head.Trace
import Inst.Model.MatrixOf

set_option autoImplicit false

namespace Inst.Model.All

open Layout (kRef hRef)

/-- groups of four layers -/
def nGr : ℕ := 12

/-- The trace: the cells owned by the 12 feed-forward segments, by the 12 attention segments and by
the head. (Of ff g the cells of x0 are read for g = 0 only; of att g only the names with
`Raw.Own`.) -/
structure Trace where
  ff : ℕ → FFSeg.Cell → ℤ
  att : ℕ → AttSeg.Raw → ℤ
  hf : ℕ → ℕ → ℤ
  hd : ℕ → ℕ → ℤ
  hr : ℕ → ℕ → ℤ

namespace Trace
variable (T : Trace)

/-- the cells that the feed-forward segment of group g reads -/
def vFF (g : ℕ) : FFSeg.Cell → ℤ := fun c =>
  if c.X = .x0 ∧ 0 < g then T.ff (g - 1) { c with X := .x8 } else T.ff g c

/-- the cells of the matrix qa of a feed-forward segment, under the names of the attention
segment -/
def bor (f : FFSeg.Cell → ℤ) : AttSeg.Raw → ℤ
  | .qry k b g i n => f ⟨.q, k, AttSeg.Dim.ref.lamOf b, AttSeg.Dim.ref.ch * AttSeg.Dim.ref.head g b + n, i⟩
  | .out k b g i n => f ⟨.o, k, AttSeg.Dim.ref.lamOf b, AttSeg.Dim.ref.ch * AttSeg.Dim.ref.head g b + n, i⟩
  | .key k lam g j n => f ⟨.kx, k, lam, AttSeg.Dim.ref.ch * g + n, j⟩
  | .val k lam g j n => f ⟨.v, k, lam, AttSeg.Dim.ref.ch * g + n, j⟩
  | _ => 0

/-- the cells that the attention segment of group g reads -/
def vAtt (g : ℕ) : AttSeg.Raw → ℤ := AttSeg.join (T.att g) (bor (T.ff g))

/-- the cells that the head reads -/
def vHead : Head.Cells ℤ :=
  ⟨T.hf, T.hd, T.hr, fun φ i => T.ff (nGr - 1) ⟨.x8, φ / 5120, 0, φ % 5120, i⟩⟩

end Trace

/-- the tokens of a prompt, as a function on all numbers -/
def tokOf (prompt : Fin ppref.T → Fin ppref.V) : ℕ → ℕ := fun i =>
  if h : i < ppref.T then (prompt ⟨i, h⟩).val else 0

/-- all cells that some segment reads are at most 128 in absolute value -/
structure Small128 (T : Trace) : Prop where
  ff : ∀ g < nGr, ∀ c : FFSeg.Cell, c.Valid FFSeg.Dim.ref → |T.vFF g c| ≤ 128
  att : ∀ g < nGr, ∀ c : AttSeg.Raw, c.Valid AttSeg.Dim.ref → |T.vAtt g c| ≤ 128
  hf : ∀ i < Head.nT, ∀ φ < Head.nFeat .hf, |T.hf φ i| ≤ 128
  hd : ∀ i < Head.nT, ∀ φ < Head.nFeat .hd, |T.hd φ i| ≤ 128
  hr : ∀ i < Head.nT, ∀ φ < Head.nFeat .hr, |T.hr φ i| ≤ 128

end Inst.Model.All
