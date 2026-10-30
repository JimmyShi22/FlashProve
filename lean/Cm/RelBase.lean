-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/RelBase.lean: what the model's two heads share: the index, the bound on the cells of the 24
segments of the layers, and what a true request is.

In standard terms: parts of an indexed relation for the model. An index is the matrix of digits off
which the weights are read; a witness is a table of integers, the cells (`Trace`,
Inst/Model/All/Trace.lean). In this file "head" is the model's last part, not the top of a file,
and the "words" of a layer are its quantization scales (`LayerScale`, Inst/Model/Program.lean).

Definitions, and a few short lemmas on them.

Cm/Rel.lean has the head of Inst/Model/Head/, written after the programs (a cost ledger, a policy).
Cm/Rel2.lean has the plain head of the technical report (lean/CREDITS.md).

Main names:
  `Shape`, `ext`, `Idx`: an index is a well-formed digit matrix: 3,076,096 rows and 2^18 columns of
    integers, every entry in [-128, 128), and low + 256 high in [-2^12, 2^12) in every column of
    every pair of rows that holds two-byte weights (Inst/Model/Layout.lean: `WFW`). The type holds
    matrices of exactly this shape, so two indices are equal if and only if all their entries are.
  `Idx.weights`, `Idx.index`: `Idx.index` is onto (Cm/RelTrue.lean: `index_onto`). By reading of
    the layout, and no theorem, not one to one: entries at which no byte of a weight lies are free
    within the two ranges.
  `BelowL B T`: the bound.
  `TrueAt κ nf i x`: a true request, written out, at the words κ of the layers and the final
    normalisation nf: the sentence in which the language of the pair of Cm/TargetPRel.lean ends, at
    a lawful table and a prime p with 2^61 - 1 ≤ p. It reads an index through its weights alone.

The conditions of the layers (`Cm.TP.CondL`, Cm/TargetPRel.lean) are those of
Inst/Model/FF/Trace.lean and Inst/Model/Att/Trace.lean. They are the print's conditions up to
bookkeeping: offsets and numbers of cells, one joint key for two digits.
The notions (cells as witness, honest and relaxed bounds on cells; the pair and its conditions:
Cm/TargetPRel.lean) follow the worked example named in lean/CREDITS.md; the text is this library's.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md); "the print": a print of
it. Neither is in this repository.

-/
import Inst.Model.All.TraceK
import Code.Field

set_option autoImplicit false

/- no default table of scales is in sight in this file: what reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

/-! ## The index -/

/-- an integer matrix of the index's shape -/
abbrev Shape : Type := Fin hRef → Fin (2 ^ kRef) → ℤ

/-- the same as a function on all pairs of numbers: 0 outside the shape -/
def ext (M : Shape) : Mat := fun r c =>
  if h : r < hRef ∧ c < 2 ^ kRef then M ⟨r, h.1⟩ ⟨c, h.2⟩ else 0

/-- a function on all pairs of numbers, cut to the shape -/
def cut (W : Mat) : Shape := fun r c => W r.val c.val

theorem ext_cut {W : Mat} (h : ∀ y c, ¬ (y < hRef ∧ c < 2 ^ kRef) → W y c = 0) :
    ext (cut W) = W := by
  funext y c
  unfold ext cut
  split
  · rfl
  · rename_i hn
    exact (h y c hn).symm

/-- An index: a well-formed digit matrix. -/
def Idx : Type := {M : Shape // Layout.WFW ppref kRef (ext M) hRef}

namespace Idx
variable (i : Idx)
/-- the matrix, as Inst/Model/ reads it (`Mat`, Inst/Model/Program.lean) -/
def mat : Mat := ext i.val
theorem wf : Layout.WFW ppref kRef i.mat hRef := i.property
/-- the weight tensors that the layout reads from the matrix -/
def weights : Weights := Layout.weightsOf ppref kRef i.mat
/-- the same as an `Index ppref` of Inst/Model/Program.lean -/
def index : Index ppref := Layout.Bridge.indexOf i.mat i.wf
end Idx

/-! ## The bound of the layers -/

/-- every cell that a segment of the layers reads is below B in absolute value -/
structure BelowL (B : ℤ) (T : Trace) : Prop where
  ff : ∀ g < nGr, ∀ c : FFSeg.Cell, c.Valid FFSeg.Dim.ref → |T.vFF g c| < B
  att : ∀ g < nGr, ∀ c : AttSeg.Raw, c.Valid AttSeg.Dim.ref → |T.vAtt g c| < B

/-! ## The true request -/

/-- the logits of the integer program: position, then token -/
abbrev logitsAt (κ : ℕ → LayerScale) (nf : NormPar) (i : Idx) (x : Instance ppref) : ℕ → ℕ → ℤ :=
  lgK ppref κ nf (fun _ => tbRef) i.weights x.prompt

/-- A true request, written out: r < e ≤ 1,024, and y = 0 if e < 1,024; the integer program runs on
the 1,024 tokens (no range test fails at any position, covered or not); at every covered position t
the checked token has a greatest logit, and every smaller token a smaller logit: it is the model's
first choice. -/
def TrueAt (κ : ℕ → LayerScale) (nf : NormPar) (i : Idx) (x : Instance ppref) : Prop :=
  (x.r < x.e ∧ x.e ≤ ppref.T ∧ (x.e < ppref.T → x.y.val = 0)) ∧
  RunsK ppref κ nf (fun _ => tbRef) i.weights x.prompt ∧
  ∀ t, x.r ≤ t → t < x.e →
    (∀ v < ppref.V, logitsAt κ nf i x t v ≤ logitsAt κ nf i x t (x.w t)) ∧
    ∀ v < x.w t, logitsAt κ nf i x t v < logitsAt κ nf i x t (x.w t)

/-- the same in the words of Inst/Model/ProgramR.lean: the form (`Head3`), and exact match on the
stretch (`ModelS`) -/
theorem trueAt_iff (κ : ℕ → LayerScale) (nf : NormPar) (i : Idx) (x : Instance ppref) :
    TrueAt κ nf i x ↔ Head3 x ∧ ModelS ppref κ nf (fun _ => tbRef) i.weights x :=
  ⟨fun h => ⟨h.1, h.2.1, fun t h1 h2 => (gapOf_eq_zero_iff _ _ (x.w_lt t)).2 (h.2.2 t h1 h2)⟩,
    fun h => ⟨h.1, h.2.1, fun t h1 h2 => (gapOf_eq_zero_iff _ _ (x.w_lt t)).1 (h.2.2 t h1 h2)⟩⟩

/-! ## Small things -/

/-- a fixed value of cells: all 0 -/
def cells0 : Trace := ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- the cells that a head borrows are cells of the last feed-forward segment -/
theorem headX_valid {φ i : ℕ} (hφ : φ < Head.nFeat .x) (hi : i < Head.nT) :
    (⟨.x8, φ / 5120, 0, φ % 5120, i⟩ : FFSeg.Cell).Valid FFSeg.Dim.ref := by
  have h1 : φ < 25600 := hφ
  have h2 : i < 1024 := hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · show φ / 5120 < 5
    omega
  · show 0 < 1
    omega
  · show φ % 5120 < 5120
    omega
  · exact h2

/-- so a bound on the cells of the layers bounds the cells that a head borrows -/
theorem BelowL.headX {B : ℤ} {T : Trace} (b : BelowL B T) {φ i : ℕ}
    (hφ : φ < Head.nFeat .x) (hi : i < Head.nT) : |T.vHead.x φ i| < B := by
  have := b.ff (nGr - 1) (by decide) _ (headX_valid hφ hi)
  unfold Trace.vFF at this
  rw [if_neg (fun h => by cases h.1)] at this
  exact this

theorem BelowL.mono {B B' : ℤ} (h : B ≤ B') {T : Trace} (b : BelowL B T) : BelowL B' T :=
  ⟨fun g hg c hc => lt_of_lt_of_le (b.ff g hg c hc) h,
    fun g hg c hc => lt_of_lt_of_le (b.att g hg c hc) h⟩

end Cm
