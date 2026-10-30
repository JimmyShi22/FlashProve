-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttRead.lean: the setting in which a claim of the attention sub-proof is read on
cells.

The claims of the attention sub-proof (OnBytes/Model/AttentionClaimsA.lean, AttentionClaimsB.lean)
read the committed matrices only through entries of tables, and all tables lie in one committed
vector. This file names what has to be known before the value of such a claim can be said on the
cells of the matrices. Definitions alone.

 - mAt, cellsK: the cells of the attention segment, by the library's names
   (Inst/Model/Att/Trace.lean), read in matrices over a field K at the addresses of
   Johnson/Road/Lane5AttDef.lean.
 - MatsFit: the smallness test's list holds the matrices of the attention sub-proof, with the rows
   that the shape gives them. Public.
 - AttAt: the setting. The shape is what the verifier's own function returns; the list of matrices
   fits; and in the world W every table of the list is true of the matrices M, entry by entry.
 - Cols: what a form reads of the state in which it is made. PiecesAll: piece b is pair b. Public.
 - TabAt, AsAt: a table with given weights begins at a given entry of the vector. Public.
 - lowOf: the weights of a table on blocks of features, on the features of a block.

The maps, the summands and the contractions that the claims are compared with are the library's
(Inst/Model/Att/Sums.lean: Acube, Bcube, Aext, Bext, rd2, rd3): none is defined here.

What this file does not claim. It holds no theorem. Nothing is said about probabilities or about
hiding. That every table is true (AttAt.tabs) is a hypothesis of whoever uses it: the smallness test
is there to show it. That the verifier's list of tables meets TabAt and AsAt is not shown here. The
program does not import this file.


-/
import OnBytes.Model.Attention
import OnBytes.Model.HideLaws
import OnBytes.Iop.GroundLaws
import Johnson.Road.FormsKeysEq
import Johnson.Road.FormsKeysMat
import Johnson.Road.Lane5AttDef
import Inst.Model.Att.KeyForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Model (Reading World Fork HFun HTailF2 eqTab)
open OnBytes.Attention (Shape Heard)
open Inst.Model.AttSeg (Raw)

variable {K : Type} [Field K]

/-- The entry of the matrices at an address: number in the list, row, column. -/
def mAt (M : Mats K) (a : ℕ × ℕ × ℕ) : K := M a.1 a.2.1 a.2.2

/-- The cells of the attention segment, read in the matrices of the sub-proof's list. -/
def cellsK (S : Shape) (M : Mats K) : Raw → K := fun c => mAt M (L5.addrA S c)

/-- The smallness test's list has the parts of as, then ah, ao, bA and qa, with the rows that the
shape gives them; a part of as also has its columns. -/
structure MatsFit (S : Shape) (tl : HTailF2) : Prop where
  /-- the number of matrices -/
  nm : tl.NM = S.cf.NAs + 4
  /-- a part of as -/
  asM : ∀ q < S.cf.NAs, (tl.mats.getD q {}).m = 2 ^ S.cf.lmS ∧
    (tl.mats.getD q {}).k = S.kAs / S.cf.NAs
  /-- the rows of ah -/
  ahM : (tl.mats.getD S.cf.NAs {}).m = S.cf.wcH * S.T
  /-- the rows of ao -/
  aoM : (tl.mats.getD (S.cf.NAs + 1) {}).m = S.cf.wcO * S.T
  /-- the rows of qa -/
  qaM : (tl.mats.getD (S.cf.NAs + 3) {}).m = S.cf.wcQ * S.T

/-- The setting of a claim. ρ reads the verifier's elements in K. W gives every slot and every entry
of the vector of tables a value. M holds the matrices. h is what the claims read. K3 is the number
of columns of the array that holds the vector of tables. -/
structure AttAt (ρ : Reading K) (W : World K) (tl : HTailF2) (K3 : ℕ) (M : Mats K) (h : Heard)
    (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape) : Prop where
  /-- the reading takes numerals to numbers -/
  num : Numerals ρ
  /-- the shape is what the verifier's function returns -/
  shape : Attention.shapeHid lid cf = .ok (h.S, fs)
  /-- the list of matrices -/
  mats : MatsFit h.S tl
  /-- every table of the list is true of the matrices (Johnson/Road/FormsKeysMat.lean) -/
  tabs : ∀ Fn ∈ h.t.funs.toList, Holds ρ W tl h.iU3 K3 M Fn

/-- In the state F the vector of tables, array number iU3, has K3 columns. A form is made in a
state, and of the state it reads this number alone. -/
def Cols (F : Fork) (h : Heard) (K3 : ℕ) : Prop := ((F.trees[h.iU3]?).map (·.K)).getD 0 = K3

/-- Piece number b of a list of pieces is pair number b, and there is a piece for each pair. It
holds of a unit whose call holds all pairs, so where all layers of the group have one shift.
Public. -/
def PiecesAll (S : Shape) (pw : Array Attention.PW) : Prop :=
  pw.size = S.NP ∧ ∀ b < S.NP, ∀ w, pw[b]? = some w → w.lam = b / S.HA ∧ w.a = b % S.HA

/-- A table on blocks of len rows of matrix number mat, under the weights phi, begins at entry t of
the vector, and the length that is stored for t is the table's. -/
structure TabAt (tl : HTailF2) (h : Heard) (t mat len : ℕ) (phi : Array E) : Prop where
  /-- the table is in the list -/
  laid : ∃ Fn ∈ h.t.funs.toList, Fn.start = t ∧ Fn.mat = mat ∧ Fn.len = len ∧ Fn.phi = phi
  /-- the stored length -/
  size : (h.t.tabLen.lookup t).getD 0 =
    (tl.mats.getD mat {}).k * ((tl.mats.getD mat {}).m / len)

/-- A table on the matrix as, under the weights phi, begins at entry t: the tables of the parts
side by side, each on whole columns. The length that is stored for t is that of all parts. -/
structure AsAt (h : Heard) (t : ℕ) (phi : Array E) : Prop where
  /-- the parts' tables are in the list -/
  laid : ∀ q < h.S.cf.NAs, ∃ Fn ∈ h.t.funs.toList,
    Fn.start = t + q * (h.S.kAs / h.S.cf.NAs) ∧ Fn.mat = q ∧ Fn.len = 2 ^ h.S.cf.lmS ∧ Fn.phi = phi
  /-- the stored length -/
  size : (h.t.tabLen.lookup t).getD 0 = h.S.cf.NAs * (h.S.kAs / h.S.cf.NAs)

/-- The weights of a table on blocks of features, on the 2^ls features of a block: the equality
weights of the last ls coordinates of the point zc on the features of a head (lng in
OnBytes/Model/AttentionTables.lean). -/
def lowOf (S : Shape) (zc : Array E) : Array E := eqTab (zc.extract (zc.size - S.ls) zc.size)

end OnBytes.Road.Rows
