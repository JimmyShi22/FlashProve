-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/H.lean: the key vector, the table and the planes of counts of the lookup
of the calls of the output head's sub-proof, written as terms over a reading of named cells.

Definitions, and three statements by rfl. "H", in the names and the docstrings, is this lookup. "The
port" is the Lean verifier under OnBytes/ (the head: OnBytes/Model/Head.lean); the records in PubH
are its own. cell : NameH → R is a reading of the names, an argument; R is any field.
Main names:
  `NameH`: a name: the cell (row, column) of matrix number mat of the head's list (hf's parts, hd,
    hr, bH, the stream), or the cell (row, column) of the committed matrix of weights.
  `PubH`: what is public: the head's shape and layout, the record of the stream's matrix, the
    covered positions, the checked tokens, the layout of the committed weights.
  `cellAt M0 m k T F t`: feature F at position t of a family of matrices with m rows and k columns
    each, the first of them number M0. With u := m / T features a column: matrix M0 + F / (k u), row
    (F % u) T + t, column (F / u) % k.
  `aw`, `ra`, `d1`, `d2`, `ex`, `nrm`, `xs`, `dig`, `recip`, `costC`, `costB`: the head's numbers
    at an index and a position, spelled from cells at radix 256.
  `wcell`, `wH`: a cell of the weights' last unit, and the weight H[k][v] from its digits.
  `lg`: a logit: the sum over the channels k of nrm k t * H[k][v].
  `affH`: the part of a segment's key that is affine in the cells. `gamH`: the products: at NF the
    reciprocal times the stream; at HD0, where the position is covered and x is an entry of the
    vocabulary (`real`), the checked token's logit less x's, over 2^(sh + 15), sh := P.h.digSh;
    else 0.
  `segH`: their sum: the key of entry x of a segment at position t.
  `colH`: which entry of which segment stands in column j of call q. `kvH`: call q's key number i,
    i = j T + t; in a column that no segment lists: the value that the call's padding row holds.
  `placeH`: where bit j of the count of row u = t 2^cK + c of the joint table lies: matrix bH, row
    (t % 2^(lm - 5)) 32 + j, column c 2^(kT + 5 - lm) + t / 2^(lm - 5), for c < NC, j < 32 and
    u < 2^d; else none. Here lm := h.lmbH. `bitsH`: the planes as one vector; 0 where there is no
    place.
  `keyH_eq`, `tabH_eq`: the key vector keyH and the table tabH are jointKey (at kvH) and jointTab of
    OnBytes/Tie/Pv/Lookup/Ends/Joint.lean at the shape P.L.fs, by rfl. `segH_eq`: a key is its
    affine part plus its products, by rfl.
Limits: nothing is assumed. No definition is marked noncomputable. A row in a name is a row of
cells: in the programs, one of three lanes of a committed symbol (a remark; nothing here states it).
Does not say: that an accepted proof's keys are these; that the port computes these terms; that the
two slots of the port's key forms hold gamH's sums; anything on a claim, a round or a message.

-/
import OnBytes.Model.Head
import OnBytes.Tie.Pv.Lookup.Ends.Joint
import Mathlib.Algebra.Field.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends.H

open OnBytes.Model OnBytes.Ends

/-- A name at H. -/
inductive NameH where
  /-- the cell (row, column) of matrix number mat of the head's list -/
  | cell (mat r c : ℕ)
  /-- the cell (row, column) of the committed matrix of weights -/
  | w (r c : ℕ)
  deriving DecidableEq, Repr

/-- What is public at H. -/
structure PubH where
  /-- the head's shape -/
  h : Head.Shape
  /-- its layout -/
  L : Head.HL
  /-- the record of the stream's matrix -/
  b : Head.Border
  /-- the covered positions -/
  cov : Head.Covered
  /-- the token that is checked at each covered position -/
  win : Array ℕ
  /-- the layout of the committed weights -/
  lay : WsLay

/-- Feature F at position t of a family of matrices. -/
def cellAt (M0 m k T F t : ℕ) : NameH :=
  .cell (M0 + F / (k * (m / T))) (F % (m / T) * T + t) (F / (m / T) % k)

/-! ## A cell of the weights -/

/-- The part of an index that a group gives to the columns. -/
def colPart (g : WsGrp) (i : ℕ) : ℕ :=
  if g.cls == 'E' then
    (List.range g.t).foldl (fun s b => s + (i % 2 ^ g.z / 2 ^ g.takenAt b % 2) * 2 ^ b) 0
  else if g.aTaken then i else 0

/-- The part of an index that a group leaves to the rows. -/
def rowPart (g : WsGrp) (i : ℕ) : ℕ :=
  if g.cls == 'E' then
    i / 2 ^ g.z * 2 ^ (g.z - g.t) +
      (if g.high then i % 2 ^ g.z % 2 ^ (g.z - g.t) else i % 2 ^ g.z / 2 ^ g.t)
  else if g.aTaken then 0 else i

/-- Digit δ of the weight of unit u with the indices idx, one for each group: (row, column). -/
def wcell (u : WsUnit) (δ : ℕ) (idx : List ℕ) : ℕ × ℕ :=
  let gi := u.g.zip idx
  (u.off + gi.reverse.foldl (fun s x => s * x.1.left + rowPart x.1 x.2) δ,
    gi.foldl (fun s x => s + colPart x.1 x.2 * 2 ^ x.1.cb0) 0)

section Terms

variable {R : Type} [Field R] (P : PubH) (cell : NameH → R)

/-- A cell of hf, of hd, of hr, of the stream: by feature and position. -/
def hfC (F t : ℕ) : R := cell (cellAt 0 P.L.m P.L.k P.h.T F t)
/-- See hfC. -/
def hdC (F t : ℕ) : R := cell (cellAt P.h.NHf P.L.mD P.L.kD P.h.T F t)
/-- See hfC. -/
def hrC (F t : ℕ) : R := cell (cellAt (P.h.NHf + 1) P.L.mR P.L.kR P.h.T F t)
/-- See hfC. -/
def xbC (F t : ℕ) : R := cell (cellAt (P.h.NHf + 3) P.b.mxb P.b.kxb P.h.T F t)

/-- n limbs of J features each from feature off on, at radix 256. -/
def limbs (n off J x t : ℕ) : R :=
  (List.range n).foldl (fun s l => s + (256 : R) ^ l * hfC P cell (off + l * J + x) t) 0

/-- The final norm's rounded product, its remainder's high digit; a margin's middle and low digit;
a table value. -/
def aw (x t : ℕ) : R := limbs P cell 2 P.L.oAw P.h.d x t
/-- See aw. -/
def ra (x t : ℕ) : R := limbs P cell 2 P.L.oRa P.h.d x t
/-- See aw. -/
def d1 (v t : ℕ) : R := limbs P cell 2 P.L.oD1 P.L.JV v t
/-- See aw. -/
def d2 (v t : ℕ) : R := limbs P cell 1 P.L.oD2 P.L.JV v t
/-- See aw. -/
def ex (v t : ℕ) : R := limbs P cell exc P.L.oE P.L.JV v t

/-- The normalized activation of channel k. -/
def nrm (k t : ℕ) : R := hdC P cell k t + 256 * hdC P cell (P.h.d + k) t

/-- The stream's value at channel k. -/
def xs (k t : ℕ) : R :=
  (List.range P.b.nl).foldl (fun s l => s + (256 : R) ^ l * xbC P cell (P.b.cell l k) t) 0

/-- Digit idx of the head's row: a cell holds its digit minus 128. -/
def dig (idx t : ℕ) : R := hrC P cell idx t + 128

/-- n digits of the row from digit first on, low digit first. -/
def digs (first n t : ℕ) : R :=
  (List.range n).foldl (fun s j => s + (256 : R) ^ j * dig P cell (first + j) t) 0

/-- The final norm's reciprocal: six digits. -/
def recip (t : ℕ) : R := digs P cell (if P.h.XL == 5 then 80 else 57) 6 t

/-- The numbers c and b of a position with a cost, from digits of the head's row. -/
def costC (t : ℕ) : R := digs P cell (ledNR P.h.XL) 5 t
/-- See costC. -/
def costB (t : ℕ) : R := dig P cell (ledNR P.h.XL + 5) t

/-- The weight H[k][v] of the head's unit, the last of the layout: groups (vocabulary, channel). -/
def wH (k v : ℕ) : R :=
  let u := P.lay.U.getD (P.lay.U.size - 1) default
  (List.range u.nlw).foldl
    (fun s δ => s + (256 : R) ^ δ * cell (.w (wcell u δ [v, k]).1 (wcell u δ [v, k]).2)) 0

/-- The logit of entry v at position t. -/
def lg (v t : ℕ) : R :=
  (List.range P.h.d).foldl (fun s k => s + nrm P cell k t * wH P cell k v) 0

/-- 1 at a covered position, at a position with a cost, at a true condition; else 0. -/
def ind (b : Bool) : R := if b then 1 else 0

/-- 1 if position t is covered and v is an entry of the vocabulary. -/
def real (v t : ℕ) : R := ind (P.cov.hOn.getD t false && decide (v < P.h.V))

/-- The middle and the low digit of a margin, with their offsets at the real places. -/
def midK (v t : ℕ) : R := d1 P cell v t + 32896 * real P v t
/-- See midK. -/
def lowK (v t : ℕ) : R := d2 P cell v t + 128 * real P v t

/-- The inverse of 2^(sh + 15). -/
def iw : R := ((2 : R) ^ (P.h.digSh + 15))⁻¹

/-- **The part of a segment's key that is affine in the cells.** -/
def affH (sn : String) (x t : ℕ) : R :=
  if sn == "NF" then
    2 ^ (P.h.KF - 1) - 2 ^ P.h.KF * aw P cell x t - 2 ^ 16 * (32896 + ra P cell x t)
  else if sn == "NFH" then 2 ^ (32 - P.h.KF) * (32896 + ra P cell x t)
  else if sn == "HD0" then
    iw P * (ind (decide (x < P.h.V) && P.cov.hOnC.getD t false) *
          (costC P cell t + 2 ^ 37 * costB P cell t) -
        real P x t * ind (decide (x < P.win.getD t 0)) -
        2 ^ P.h.digSh * midK P cell x t - lowK P cell x t)
  else if sn == "HD1" then midK P cell x t
  else if sn == "HD2" then lowK P cell x t
  else if sn == "HE0" || sn == "HE1" then
    let v := Head.firstEntry P.L sn + x
    midK P cell v t + 2 ^ 16 * ((Head.offE : ℕ) + ex P cell v t)
  else if sn == "ROW" then
    ((if x < ledNR P.h.XL then ledMu P.h.XL x else 1 : ℕ) : R) * dig P cell x t
  else if sn == "CNF" then aw P cell x t + 2 ^ 28 * nrm P cell x t + 2 ^ 15 + 2 ^ 39
  else 0

/-- **The products in a segment's key.** -/
def gamH (sn : String) (x t : ℕ) : R :=
  if sn == "NF" then recip P cell t * xs P cell x t
  else if sn == "HD0" then
    iw P * (real P x t * (lg P cell (P.win.getD t 0) t - lg P cell x t))
  else 0

/-- **The key of entry x of a segment at position t.** -/
def segH (sn : String) (x t : ℕ) : R := affH P cell sn x t + gamH P cell sn x t

/-- Which entry of which segment stands in column j of call q. -/
def colH (L : Head.HL) (q j : ℕ) : Option (String × ℕ) :=
  (L.calls.getD q default).segs.findSome? fun g =>
    (g.pos.findIdx? (· == j)).map fun x => (g.name, x)

/-- A call's key vector from a function on segments, entries and positions. -/
def kvOf (f : String → ℕ → ℕ → R) (q i : ℕ) : R :=
  match colH P.L q (i / P.h.T) with
  | some (sn, x) => f sn x (i % P.h.T)
  | none => (tauN P.L.fs q (t0N P.L.fs q) : R)

/-- **Call q's key number i at H.** -/
def kvH (q i : ℕ) : R := kvOf P (segH P cell) q i

/-- The joint key vector at H. -/
def keyH (θ : R) (X : ℕ) : R := jointKey P.L.fs (kvH P cell) θ X

/-- The joint table at H. -/
def tabH (θ : R) (u : ℕ) : R := jointTab P.L.fs θ u

theorem keyH_eq : keyH P cell = jointKey P.L.fs (kvH P cell) := rfl

theorem tabH_eq : (tabH P : R → ℕ → R) = jointTab P.L.fs := rfl

theorem segH_eq (sn : String) (x t : ℕ) :
    segH P cell sn x t = affH P cell sn x t + gamH P cell sn x t := rfl

end Terms

/-- **Where bit j of the count of row u of the joint table lies at H.** -/
def placeH (h : Head.Shape) (fs : Forest.Shape) (u j : ℕ) : Option NameH :=
  let c := u % 2 ^ fs.cK
  let t := u / 2 ^ fs.cK
  if c < fs.NC ∧ j < 32 ∧ u < 2 ^ fs.d then
    some (.cell (h.NHf + 2) (t % 2 ^ (h.lmbH - 5) * 32 + j)
      (c * 2 ^ (fs.kT + 5 - h.lmbH) + t / 2 ^ (h.lmbH - 5)))
  else none

/-- The planes at H as one vector: entry X = u * 32 + j is the bit at placeH u j; 0 where there is
no place. -/
def bitsH {R : Type} [Zero R] (h : Head.Shape) (fs : Forest.Shape) (cell : NameH → R) (X : ℕ) :
    R :=
  match placeH h fs (X / 32) (X % 32) with
  | some x => cell x
  | none => 0

end OnBytes.Ends.H

#print axioms OnBytes.Ends.H.wcell
#print axioms OnBytes.Ends.H.affH
#print axioms OnBytes.Ends.H.gamH
#print axioms OnBytes.Ends.H.kvH
#print axioms OnBytes.Ends.H.keyH
#print axioms OnBytes.Ends.H.tabH
#print axioms OnBytes.Ends.H.placeH
#print axioms OnBytes.Ends.H.bitsH
#print axioms OnBytes.Ends.H.keyH_eq
