-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysFree.lean: the library's quantities of a lookup call, at a free point.

The library writes the weights of a call's layers and columns, the weight of its padding and the
parts of the extension of its key vector at the call's point zc D z c, which it cuts out of the
point z of the whole lookup (Inst/Model/FF/Objects.lean: el, ewc, ew, PADW, LINE, TERM, ACC, TS, KF;
the token's point is zpos D z). This file has these definitions with a free point ζ in the place of
zc D z c, and the coordinates of ζ behind those of the layer and the column (uP) in the place of
zpos D z. So a statement on one call need not speak of the trees of the lookup. KEYP, the like of
LINEP with the whole key, and uP have no counterpart in the library.

Only definitions. That each is the library's own at ζ := zc D z c is shown in
Johnson/Road/FormsKeysVec.lean. The program does not import this file.
-/
import Inst.Model.FF.Objects

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW key lin term mat len call pos lJ isPad famsIn lut)

variable {K : Type} [Field K] (D : Dim)

/-- The weight of layer l: the equality weight of the first lL coordinates of ζ. -/
def elP (ζ : ℕ → K) (l : ℕ) : K := Blocks.eqN D.lL 0 ζ l

/-- The weight of column jj of call c: the equality weight of the next lJ coordinates. -/
def ewcP (c : Fin 8) (ζ : ℕ → K) (jj : ℕ) : K := Blocks.eqN (lJ D c) D.lL ζ jj

/-- The weight of entry x of family s: that of its column. -/
def ewP (ζ : ℕ → K) (s : Fam) (x : ℕ) : K := ewcP D (call s) ζ (pos D s x)

/-- The token's point: the coordinates of ζ behind those of the layer and the column. -/
def uP (c : Fin 8) (ζ : ℕ → K) : ℕ → K := fun j => ζ (D.lL + lJ D c + j)

/-- The weight of the padding: for each layer its weight times the sum of the weights of the columns
that are padding in that layer. -/
def PADWP (c : Fin 8) (ζ : ℕ → K) : K :=
  ∑ l ∈ range D.nl, elP D ζ l *
    ∑ jj ∈ range (2 ^ lJ D c), if isPad D c l jj then ewcP D c ζ jj else 0

section Cells

variable [scl : Scl] (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)

/-- The weighted sum of the extensions of the affine parts of the keys of family s at layer l. -/
def LINEP (ζ : ℕ → K) (s : Fam) (l : ℕ) : K :=
  ∑ x ∈ range (len D s), ewP D ζ s x *
    Blocks.ext D.lT (fun i => lin D t tb L0 w s l x i) (uP D (call s) ζ)

/-- The weighted sum of the extensions of the whole keys of family s at layer l. -/
def KEYP (ζ : ℕ → K) (s : Fam) (l : ℕ) : K :=
  ∑ x ∈ range (len D s), ewP D ζ s x *
    Blocks.ext D.lT (fun i => key D t tb L0 w s l x i) (uP D (call s) ζ)

/-- The weighted sum, at one position, of the parts of the keys that are left to the sumcheck over
the positions. -/
def TERMP (ζ : ℕ → K) (s : Fam) (l i : ℕ) : K :=
  ∑ x ∈ range (len D s), ewP D ζ s x * term D t tb L0 w s l x i

/-- The weighted sum of the extensions of the matrix products in the keys. -/
def ACCP (ζ : ℕ → K) (s : Fam) (l : ℕ) : K :=
  ∑ x ∈ range (len D s), ewP D ζ s x *
    Blocks.ext D.lT (fun i => mat D t w s l x i) (uP D (call s) ζ)

/-- What the sumcheck over the positions is to show for call c. -/
def TSP (c : Fin 8) (ζ : ℕ → K) : K :=
  Blocks.ext D.lT (fun i =>
      ∑ l ∈ range D.nl, elP D ζ l * ((famsIn c l).map fun s => TERMP D t tb L0 w ζ s l i).sum)
    (uP D c ζ)

/-- The library's KF of call c, at the free point. -/
def KFP (c : Fin 8) (ζ : ℕ → K) : K :=
  (((lut tb c).pad : ℤ) : K) * PADWP D c ζ + TSP D t tb L0 w c ζ +
    ∑ l ∈ range D.nl,
      elP D ζ l * ((famsIn c l).map fun s => LINEP D t tb L0 w ζ s l + ACCP D t w ζ s l).sum

end Cells

end OnBytes.Road
