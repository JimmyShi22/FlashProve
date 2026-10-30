-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPort.lean: the definitions on which the comparison of the verifier's panels
with the library's stands.

The batched sumcheck of a layer sub-proof sums a product of two long vectors, made of panels
(OnBytes/Model/LayerPanels.lean). Johnson/Road/FormsKeysEnd.lean shows that this sum is the sum over
the verifier's panels of the claim's weight times a share. The library has its own panels, each with
a share (Pan.share in Inst/Model/FF/Objects.lean). The files that compare the two, kind of panel by
kind, read the definitions of this file.

Only definitions, and one equation that holds by definition.
 - shareP: the share of one of the verifier's panels, without the weight of its claim.
 - shareL, share_wc: the library's share of a panel without the call's weight wc.
 - sentAt, rPort: the record of reads at which the two shares are compared.
 - Returns: the forms of a panel's two sides are there.
 - WvRows, WvTri: the vectors of a panel's weight claims are the library's B side.
 - HasShort2, PortFits: one record for what all comparisons ask.
 - ElTie, EwTie, WtsTie: the ties of one call's and one family's weights to the library's.

Sent and hidden. rPort is the library's record of true reads (rdTrue) in all fields but five. Three,
R2, sc2 and sel2, hold what the prover SENT for the end values of the second token sumcheck: by the
text of panelT and hearStack these sent values stand in the verifier's panels as constants. They are
hidden values plus a factor times a mask entry, so rPort is not rdTrue; sig1_affine
(Johnson/Road/FormsKeysSigL.lean) says how the library's sum hangs on these three fields. The two
others, hh1 and hh2, hold the never-sent vectors hv, which stay free here.

What is not claimed. No statement is made on any panel. That the record PortFits can be met, and
that it follows from the verifier's layout and from tables that are true, is not shown here. The
program does not import this file.
-/
import Johnson.Road.FormsKeysEnd
import Johnson.Road.FormsKeysTrue2
import Johnson.Road.FormsKeysSigL

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab tenCell)
open OnBytes.Model.Layer (Env Lay SBlk Ten)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Arr LW Pan Rd rdTrue zpos call len wc)

variable {K : Type} [Field K]

/-! ## The two shares -/

/-- The share of one of the verifier's panels in the sum of the batched sumcheck, without the weight
of its claim: the call's weight times the sum over the rows of the row's weight times the inner
product of what is left of the two sides. It is the summand of the third clause of stack_slots
(Johnson/Road/FormsKeysEnd.lean) without omK. hv: the never-sent vectors; wv: the vectors of the
weight claims. -/
def shareP (ρ : Reading K) (W : World K) (y : Lay) (hv wv : ℕ → ℕ → K) (b : SBlk) : K :=
  ρ.val b.ec * ∑ i ∈ range (nRows y b), rowW ρ b i *
    ∑ yv ∈ range (2 ^ b.wy), aRaw ρ W hv b i yv * bRaw ρ W wv b i yv

section Library

variable [scl : Scl] (D : Dim) (r : Rd K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K)

/-- The library's share of a panel without the call's weight. -/
def shareL (p : Pan) : K :=
  ∑ ρ' ∈ range (p.nr D), p.wt D z ρ' *
    ∑ ι ∈ range (p.nc D), p.A D r ρ' ι * p.B D r tb L0 w z zh ρ' ι

/-- The library's share is the call's weight times shareL. -/
theorem share_wc (p : Pan) :
    p.share D r tb L0 w z zh = wc D z (call p.fam) * shareL D r tb L0 w z zh p := rfl

end Library

/-! ## The record of reads -/

/-- What was sent for end value number i of the second token sumcheck, read in K; 0 past the
array's end. -/
def sentAt (ρ : Reading K) (shownT : Array E) (i : ℕ) : K := ρ.val (shownT.getD i zeroE)

/-- The record of reads at which the verifier's shares are the library's. The true contractions of
the cells t at the lookup's token point and at zh, the end point of the second token sumcheck; but
for the reciprocal of norm number ν the sent value number ν, for the score of layer 2 l' + 1 number
NN Lam + l', for entry e of its selector number NN Lam + LamM + l' NE + e; for Hh1 at (l, j) entry
l 2^(the bits of f) + j of the never-sent vector number 0, and for Hh2 at (l', j) entry j of the
never-sent vector number 1 + l'. -/
def rPort (ρ : Reading K) (y : Lay) (shownT : Array E) (hv : ℕ → ℕ → K) (D : Dim) (t : Cell → K)
    (z zh : ℕ → K) : Rd K :=
  withEnds
    (rdTrue D t z zh (fun l j => hv 0 (l * 2 ^ ceilLog2 y.h.f + j)) fun l' j => hv (1 + l') j)
    (fun ν => sentAt ρ shownT ν) (fun l' => sentAt ρ shownT (y.NN * y.Lam + l'))
    fun l' e => sentAt ρ shownT (y.NN * y.Lam + y.LamM + l' * y.h.NE + e)

/-! ## What is asked of one panel -/

/-- The forms of a panel's sides are there: a side that is given as forms returns a form at every
row and column of the panel. Where a form is absent, aRaw and bRaw read 0. -/
def Returns (b : SBlk) : Prop :=
  (∀ A, b.A = some A → ∀ i, i < b.ni → ∀ yv, yv < b.ny → ∃ a, A i yv = some a) ∧
    ∀ B, b.B = some B → ∀ i, i < b.ni → ∀ yv, yv < b.ny → ∃ a, B i yv = some a

/-- The vectors of the weight claims number v0 to v0 + ni - 1, one for each row of a panel with 2^wy
places in a row, are the rows of B on the first nc columns, and 0 on the others. -/
def WvRows (wv : ℕ → ℕ → K) (v0 ni wy nc : ℕ) (B : ℕ → ℕ → K) : Prop :=
  ∀ i, i < ni → ∀ yv, yv < 2 ^ wy → wv (v0 + i) yv = if yv < nc then B i yv else 0

/-- The vector of the one weight claim of a panel with the selector holds B, row after row. -/
def WvTri (wv : ℕ → ℕ → K) (v0 ni wy nc : ℕ) (B : ℕ → ℕ → K) : Prop :=
  ∀ e, e < ni → ∀ yv, yv < 2 ^ wy → wv v0 (e * 2 ^ wy + yv) = if yv < nc then B e yv else 0

/-! ## One record for the hypotheses -/

section Record

variable [scl : Scl] (ρ : Reading K) (W : World K) (v : Env) (D : Dim) (c : Cells K) (t : Cell → K)

/-- The array X is read entry by entry at the end point of the second token sumcheck: the verifier
finds its tensor and the short tables of its matrix at the point rt, the library's cell names are
tied to the tensor's places, and the tables are true at u'. -/
def HasShort2 (u' : ℕ → K) (X : Arr) : Prop :=
  ∃ (ten : Ten) (b : ℕ), v.tensorAt (arrName X) "rt" = some (ten, b) ∧
    Tied c t X ten.mat ten.place ∧ ShortTrue ρ W v b ten.mat D.lT c u'

/-- What all comparisons of the panels ask, beside what is asked of one panel, call or family. low:
the coordinates of a feature's low bits in the lookup's point; z: the library's point; zh: the end
point of the second token sumcheck. -/
structure PortFits (low z zh : ℕ → K) : Prop where
  /-- what the theorems on the forms at the lookup's point ask, at the library's token point -/
  fits : Fits ρ W v D c t low (zpos D z)
  /-- the arrays that are read entry by entry, at the end point of the second token sumcheck -/
  short2 : ∀ X : Arr, readShort X = true → HasShort2 ρ W v D c t zh X
  /-- the residual stream at that end point: the two families of long tables under the names that
  the verifier writes out. The stream that goes out has no table there -/
  stream2 : ∃ (bI bF : ℕ) (txs : Ten),
    v.tabAt ("xbI" ++ "@" ++ "Y") = some bI ∧ v.tabAt ("af" ++ "@" ++ "Y") = some bF ∧
    v.y.T_ "xs" = some txs ∧ txs.mat = 0 ∧
    Tied c t .x0 4 v.y.xb ∧ Tied c t .xs txs.mat txs.place ∧
    LongTrue ρ W v bI 4 v.y.ls D.lT c low zh ∧ LongTrue ρ W v bF txs.mat v.y.ls D.lT c low zh ∧
    (∀ l, v.y.S2 ∣ tenCell v.y.xb l 0 0) ∧ ∀ i l, v.y.S2 ∣ tenCell txs.place l i 0

end Record

/-! ## The ties of one call and of one family

They are no fields of the record: the library's point of a call has as many coordinates as the
library's call has bits, and where the verifier's least number of columns makes a call longer than
the library's, the ties of that call fail. So each comparison asks the ties of its own call and
family alone. -/

/-- The layers' weights in the point of the verifier's call number q are the library's for its call
cc, on the group's layers. -/
def ElTie (ρ : Reading K) (v : Env) (D : Dim) (z : ℕ → K) (q : ℕ) (cc : Fin 8) : Prop :=
  ∀ lam, lam < D.nl → ρ.val ((eqTab (v.zl q)).getD lam zeroE) = Inst.Model.FFSeg.el D z cc lam

/-- The weights of the entries of the segment of the family s are the library's, one for each entry
of the family. -/
def EwTie (ρ : Reading K) (v : Env) (D : Dim) (z : ℕ → K) (s : Fam) : Prop :=
  ∀ a : Array E, v.ewOf (segName s) = some a →
    a.size = len D s ∧ ∀ x, x < len D s → ρ.val (a.getD x zeroE) = Inst.Model.FFSeg.ew D z s x

/-- The weights of the blocks of that segment and the weights of its entries are one set of
weights. -/
def WtsTie (ρ : Reading K) (v : Env) (D : Dim) (low : ℕ → K) (s : Fam) : Prop :=
  ∀ a wh : Array E, v.ewOf (segName s) = some a → v.ewh (segName s) = some wh →
    Wts ρ a wh v.y.ls low (len D s)

end OnBytes.Road
