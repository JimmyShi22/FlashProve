-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysAll.lean: the forms of all 34 segments of a layer sub-proof's lookup against
the library's keys: one theorem.

Johnson/Road/FormsKeysKit.lean says what is compared and in what sense, and has the record Fits of
all hypotheses. The files Johnson/Road/FormsKeysA.lean to FormsKeysD.lean have one theorem for each
family. This file gathers them.

Main theorems.
 - Fits.line_lin: for every family s, at every layer on which the family is present: if the
   verifier's line returns a form at the segment's name, then in a world with true reads that form
   is worth the sum, over the segment's entries x, of the weight of x times the multilinear
   extension, over the positions, of the affine part of the library's keys at x.
 - Fits.line_key: for the 22 families whose keys are affine in the cells, the same with the keys
   themselves.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. For the twelve other families the products
in the keys are not in the form; nothing here is on them. The program does not import this file.
-/
import Johnson.Road.FormsKeysA
import Johnson.Road.FormsKeysB
import Johnson.Road.FormsKeysC
import Johnson.Road.FormsKeysD

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW key lin len present isExp)

/-- A family that exists only on layers with experts is present on the odd layers alone. -/
theorem odd_of_present {s : Fam} {lam : ℕ} (he : isExp s = true) (hp : present s lam = true) :
    lam % 2 = 1 := by
  unfold present at hp
  rw [he] at hp
  simpa [Inst.Model.FFSeg.isExpL] using hp

/-- True for a family whose keys are affine in the cells. -/
def affine : Fam → Bool
  | .G | .U | .QK | .N1 | .N2 | .O | .D | .V | .LR | .XR | .DD | .MR => false
  | _ => true

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low u : ℕ → K}

/-- All 34 families. Under the record Fits, at a layer lam of the group (lam < D.nl) on which the
family s is present, with one weight for each entry of the segment and, if the segment is read by
blocks, block weights that are one set with them: the form that the verifier builds for the segment
is worth the weighted sum of the extensions of the affine part of the library's keys. The tables tb,
the number L0 of the group's first layer and the weights w are arguments of the library's lin, which
reads none of them. That the family is present is used for LH and LR alone. -/
theorem Fits.line_lin (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (s : Fam)
    (lam : ℕ) (hlam : lam < D.nl) (hp : present s lam = true) {ew wh : Array E}
    (hsz : ew.size = len D s) (hbl : byBlocks s = true → Wts ρ ew wh v.y.ls low (len D s)) {f : Aff}
    (h : v.line (segName s) lam ew wh = some f) :
    f.value ρ W = ∑ x ∈ range (len D s), ρ.val (ew.getD x zeroE) *
      Blocks.ext D.lT (fun i => lin D t tb L0 w s lam x i) u := by
  cases s
  case G => exact F.line_G tb L0 w lam hlam (hbl rfl) h
  case U => exact F.line_U tb L0 w lam hlam (hbl rfl) h
  case UT => exact F.line_UT tb L0 w lam (hbl rfl) h
  case QK => exact F.line_QK tb L0 w lam hlam (hbl rfl) h
  case N1 => exact F.line_N1 tb L0 w lam hlam (hbl rfl) h
  case N2 => exact F.line_N2 tb L0 w lam hlam (hbl rfl) h
  case O => exact F.line_O tb L0 w lam hlam (hbl rfl) h
  case D => exact F.line_D tb L0 w lam hlam (hbl rfl) h
  case V => exact F.line_V tb L0 w lam hlam (hbl rfl) h
  case LR => exact F.line_LR tb L0 w lam hlam hsz (odd_of_present rfl hp) h
  case XR => exact F.line_XR tb L0 w lam hsz h
  case LT => exact F.line_LT tb L0 w lam h
  case DD => exact F.line_DD tb L0 w lam h
  case GH => exact F.line_GH tb L0 w lam hlam (hbl rfl) h
  case UH => exact F.line_UH tb L0 w lam hlam (hbl rfl) h
  case OH => exact F.line_OH tb L0 w lam hlam (hbl rfl) h
  case DH => exact F.line_DH tb L0 w lam hlam (hbl rfl) h
  case VH => exact F.line_VH tb L0 w lam hlam (hbl rfl) h
  case LH => exact F.line_LH tb L0 w lam hlam hsz (odd_of_present rfl hp) h
  case QKH => exact F.line_QKH tb L0 w lam hlam (hbl rfl) h
  case N1H => exact F.line_N1H tb L0 w lam hlam (hbl rfl) h
  case N2H => exact F.line_N2H tb L0 w lam hlam (hbl rfl) h
  case ROW => exact F.line_ROW tb L0 w lam hsz h
  case SEL => exact F.line_SEL tb L0 w lam h
  case L3 => exact F.line_L3 tb L0 w lam h
  case G0 => exact F.line_G0 tb L0 w lam (hbl rfl) h
  case CN1 => exact F.line_CN1 tb L0 w lam (hbl rfl) h
  case CN2 => exact F.line_CN2 tb L0 w lam (hbl rfl) h
  case CQK => exact F.line_CQK tb L0 w lam (hbl rfl) h
  case CV => exact F.line_CV tb L0 w lam (hbl rfl) h
  case CLR => exact F.line_CLR tb L0 w lam hsz h
  case F => exact F.line_F tb L0 w lam (hbl rfl) h
  case MR => exact F.line_MR tb L0 w lam h
  case CG => exact F.line_CG tb L0 w lam (hbl rfl) h

omit scl in
/-- For a family whose keys are affine in the cells the affine part is the key. -/
theorem lin_eq_key [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (s : Fam) (hs : affine s = true) (l x i : ℕ) :
    lin D t tb L0 w s l x i = key D t tb L0 w s l x i := by
  cases s <;> first | rfl | exact absurd hs (by decide)

/-- The 22 families whose keys are affine in the cells: the form is worth the weighted sum of the
extensions of the library's keys themselves. -/
theorem Fits.line_key (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (s : Fam)
    (hs : affine s = true) (lam : ℕ) (hlam : lam < D.nl) (hp : present s lam = true)
    {ew wh : Array E} (hsz : ew.size = len D s)
    (hbl : byBlocks s = true → Wts ρ ew wh v.y.ls low (len D s)) {f : Aff}
    (h : v.line (segName s) lam ew wh = some f) :
    f.value ρ W = ∑ x ∈ range (len D s), ρ.val (ew.getD x zeroE) *
      Blocks.ext D.lT (fun i => key D t tb L0 w s lam x i) u := by
  rw [F.line_lin tb L0 w s lam hlam hp hsz hbl h]
  simp only [lin_eq_key D t tb L0 w s hs]

#print axioms Fits.line_lin
#print axioms Fits.line_key

end OnBytes.Road
