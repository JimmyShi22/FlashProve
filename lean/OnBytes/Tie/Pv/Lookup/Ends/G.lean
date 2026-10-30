-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/G.lean: the key vector, the table and the planes of bits of the lookup of
a layers' sub-proof, written out term by term over the verifier's own records.

G is the lookup of the calls of a layers' sub-proof (OnBytes/Model/Layer.lean): one group of layers.
All definitions are over the verifier's own records (Layer.Pub: the layout y with its tensors, calls
and lookup shape, the scales sc, the rotary table, the layout of the committed weights), the group's
number g, and a reading cell : NameG → R of the cells, R any commutative ring.

Main names:
  `NameG`: a name: the cell (row, column) of matrix number mat of the group's list (af's parts, ad's
    parts, ar, b, qa, the stream that goes out, the stream that comes in), or the cell (row, column)
    of the committed matrix of weights.
  `cellAt`: feature F at token t of a family of matrices with m rows and k columns each, the first
    of them number M0: with u := m / T features a column: matrix M0 + F / (k u), row (F % u) T + t,
    column (F / u) % k.
  `ten`: entry (instance, x) of a tensor at token i, spelled from cells at radix 256: limb l is
    feature OFF + (l cnt + instance) J + x of the tensor's matrix; 0 for a tensor that the layout
    has not.
  `xs`: the residual stream after write number s of the group. `dig`, `recip`: a digit of a norm's
    row, and the norm's reciprocal from six of them. `wt`: a weight of a unit from its digits, at
    the cells that wcell names (OnBytes/Tie/Pv/Lookup/Ends/H.lean: one text for both sites).
  `site`, `high`: the low and the high key of a rounding site.
  `affG`: the part of a segment's key that is affine in the cells. `gamG`: the products. `segG`:
    their sum: the key of entry x of a segment on layer lam of the group at token i.
  `colG`: which entry of which segment stands in column j of call q. `kvOf`: a call's key vector
    from any function on segments, layers, entries and tokens. `kvG`: call q's key number X, X =
    (lam 2^lJ + j) T + i; in a column that no segment lists, and in a column of a segment of the
    layers with routed experts on an even layer: the call's padding row.
  `placeG`: where bit j of the count of row u = t 2^cK + c of the joint table lies: matrix b, row
    (t % 2^(lmb - 5)) 32 + j, column c 2^(kT + 5 - lmb) + t / 2^(lmb - 5), for c < NC, j < 32,
    u < 2^d; else none. `bitsG`: the planes as one vector; 0 where there is no place.
  `keyG_eq`, `tabG_eq`: the key vector and the table at G are jointKey and jointTab
    (OnBytes/Tie/Pv/Lookup/Ends/Joint.lean) at the verifier's own shape P.y.fo: by rfl.
  `segG_eq`: a key is its affine part and its products. `site_split`: a rounding site's key is
    affine in its accumulator.

What is read of the verifier's records: fields and constants: of a tensor OFF, nl, cnt, J, mat; of
a call its segments and lJ; of a segment name, pos, moe; of the layout T, Lam, dq, mrow, kcol,
parts, mxb, kxb, its calls, its shape and the lookup's shape; of the shape xl, d, f, fe, NE, dh,
lmb, the flags p3, p4, gcl, rcl and the digit forms hgD, huD, hq, ho, hdD, hv, hr; of the lookup's
shape cK, NC, d, kT; the scales' words at nine places of a layer's record (Layer.Lkq, Lkk, Lkv,
Lko, Lkg, Lku, Lkd, LK1, LK2) and three of a layer with routed experts; of the weights' layout its
units; of a unit nlw and its groups. The index arithmetic is written out here and calls no routine
of the verifier but Lay.T_, WsLay.unitOf, Scales.kl, Scales.klM, ledNR, ledMu and the two public
tables ropeC and stubO.

The next two paragraphs are readings of the verifier's text: no theorem of this file or of this
library bears them.

Two factors of the products are the verifier's only under the tests on the scales. (i) At N1 and N2
the factor here is 2^(16 - K), the verifier's panel has 1: they are equal only because K ≥ 17 is
tested on the scales (KL-norm); K ≥ 16 would do for the equality. (ii) At QK the factor here goes
by entry (kq or kk), the verifier's panel has kq's for both: they are equal only because kq ≠ kk is
admitted with both ≥ 16 alone (KL-kq-kk). A comparison at scales that pass both tests sees neither.

The written tables (FC, FL, FS): their rows are natural numbers below 2^42, no residues of negative
numbers (OnBytes/Model/LayerLayout.lean: rowFC, rowFS, the row of FL): so tauN of
OnBytes/Tie/Pv/Lookup/Ends/Joint.lean, which casts a row's number into R, gives the row in every
ring.

Limits: no premise; all definitions are computable; no classical term. It is not said here that an
accepted proof's keys are these; nor that the batched sumcheck and the second token sumcheck prove
gamG's sums; nothing is said on a claim, a round or a message. That the terms are the verifier's is
no theorem of this file. A word on files outside this library, which cannot be checked from here
and on which nothing here rests: two theorems there (alg_line, alg_call) prove it of the affine
parts, under their premises Fits and TiesG; of the products gamG those files prove only that they
are the library's. The definitions are total: natural subtraction and division cut off (2^(16 - k)
is 1 from k = 16 on; m / T is 0 where m < T or T = 0; lmb - 5 is 0 below 5): the terms mean what
their names say only at numbers that pass the layout's tests, which are not asked here. moe and the
padding in kvOf go by a layer's number in the group, lOf by its number in the model: the two
parities agree for every group only if Lam, the number of layers of a group, is even: that is not
asked here either. A "cell" is a row of cells: in the programs one of three lanes of a committed
symbol. Nothing is said on an honest prover, on completeness or on hiding.
Not claimed: anything on soundness, completeness or hiding.


-/
import OnBytes.Model.Layer
import OnBytes.Tie.Pv.Lookup.Ends.Joint
import OnBytes.Tie.Pv.Lookup.Ends.H
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends.G

open OnBytes.Model OnBytes.Ends

/-- A name at G. -/
inductive NameG where
  /-- the cell (row, column) of matrix number mat of the group's list -/
  | cell (mat r c : ℕ)
  /-- the cell (row, column) of the committed matrix of weights -/
  | w (r c : ℕ)
  deriving DecidableEq, Repr

/-- Feature F at token t of a family of matrices. -/
def cellAt (M0 m k T F t : ℕ) : NameG :=
  .cell (M0 + F / (k * (m / T))) (F % (m / T) * T + t) (F / (m / T) % k)

/-! ## The group's list of matrices: af's parts, ad's parts, ar, b, qa, xbO, xbI -/

/-- The number of ar in the list. -/
def iAR (y : Layer.Lay) : ℕ := y.parts.getD 0 0 + y.parts.getD 1 0
/-- The number of b. -/
def iB (y : Layer.Lay) : ℕ := iAR y + 1
/-- The number of qa. -/
def iQA (y : Layer.Lay) : ℕ := iAR y + 2
/-- The number of the stream that goes out. -/
def iXO (y : Layer.Lay) : ℕ := iAR y + 3
/-- The number of the stream that comes in. -/
def iXI (y : Layer.Lay) : ℕ := iAR y + 4

/-- The first matrix of family μ: 0 af, 1 ad, 2 ar, 3 qa. -/
def famM0 (y : Layer.Lay) (μ : ℕ) : ℕ :=
  if μ == 0 then 0 else if μ == 1 then y.parts.getD 0 0 else if μ == 2 then iAR y else iQA y

/-- Feature F at token t of family μ. -/
def famCell (y : Layer.Lay) (μ F t : ℕ) : NameG :=
  cellAt (famM0 y μ) (y.mrow.getD μ 0) (y.kcol.getD μ 0) y.T F t

section Terms

variable {R : Type} [CommRing R]

/-- The sum of f k over k below n. -/
def sumN (n : ℕ) (f : ℕ → R) : R := (List.range n).foldl (fun s k => s + f k) 0

/-- The offset of a digit tensor of the given form. -/
def oOf (form : ℕ) : R := if form == 1 then 128 else 32896

/-- **The low key of a rounding site**: accumulator A, quotient Q, shift k, digit form, high digits
rh. -/
def site (A Q : R) (k form : ℕ) (rh : R) : R :=
  2 ^ (16 - k) * (A + 2 ^ (k - 1) - 2 ^ k * Q) - (if form == 0 then 0 else 2 ^ 16 * (oOf form + rh))

/-- **The key of the high digits of a rounding site.** -/
def high (rh : R) (k form : ℕ) : R :=
  2 ^ ((if form == 1 then 24 else 32) - max k 16) * (oOf form + rh)

theorem site_split (A Q : R) (k form : ℕ) (rh : R) :
    site A Q k form rh = site 0 Q k form rh + 2 ^ (16 - k) * A := by
  unfold site
  ring

variable (P : Layer.Pub) (g : ℕ) (cell : NameG → R)

/-- Entry (inst, x) of the tensor with the name n at token i. -/
def ten (n : String) (inst x i : ℕ) : R :=
  match P.y.T_ n with
  | some X =>
    sumN X.nl fun l =>
      (256 : R) ^ l * cell (famCell P.y X.mat (X.OFF + (l * X.cnt + inst) * X.J + x) i)
  | none => 0

/-- Channel x at token i of the stream's matrix number M0. -/
def xb (M0 x i : ℕ) : R :=
  sumN P.y.h.xl fun l =>
    (256 : R) ^ l * cell (cellAt M0 P.y.mxb P.y.kxb P.y.T (l * P.y.h.d + x) i)

/-- The residual stream after write number s of the group. -/
def xs (s x i : ℕ) : R :=
  if s == 0 then xb P cell (iXI P.y) x i
  else if s == 2 * P.y.Lam then xb P cell (iXO P.y) x i
  else ten P cell "xs" (s - 1) x i

/-- Digit j of the row of norm ν: a cell holds its digit minus 128. -/
def dig (ν j i : ℕ) : R := ten P cell "row" ν j i + 128

/-- The reciprocal of norm ν: six digits. -/
def recip (ν i : ℕ) : R :=
  sumN 6 fun j => (256 : R) ^ j * dig P cell ν ((if P.y.h.xl == 5 then 80 else 57) + j) i

/-- The weight of the unit of kind X of layer l of the model at the indices idx, one for each of
the unit's groups; 0 if the layout has no such unit. -/
def wt (X l : ℕ) (idx : List ℕ) : R :=
  match (P.wsLay.unitOf X l).bind (fun ui => P.wsLay.U[ui]?) with
  | some u =>
    sumN u.nlw fun δ => (256 : R) ^ δ * cell (.w (H.wcell u δ idx).1 (H.wcell u δ idx).2)
  | none => 0

/-- The number of layer lam of the group in the model. -/
def lOf (lam : ℕ) : ℕ := g * P.y.Lam + lam

/-- True if layer lam of the group has routed experts. -/
def moe (lam : ℕ) : Bool := P.y.h.p3 && lam % 2 == 1

/-- True at an entry of G, U, GH, UH that belongs to the routed expert. -/
def routed (lam x : ℕ) : Bool := moe P lam && decide (P.y.h.fe ≤ x)

/-- The shift of the gate's (up: the up product's) site at entry x. -/
def kGU (up : Bool) (lam x : ℕ) : ℕ :=
  if routed P lam x then P.sc.klM (lOf P g lam) (if up then 2 else 1)
  else P.sc.kl (lOf P g lam) (if up then Layer.Lku else Layer.Lkg)

/-- The shift of the site of q (x below dq) or of k. -/
def kQK (lam x : ℕ) : ℕ :=
  P.sc.kl (lOf P g lam) (if x < P.y.dq then Layer.Lkq else Layer.Lkk)

/-- Word w of the layer's record. -/
def kL (lam w : ℕ) : ℕ := P.sc.kl (lOf P g lam) w

/-- The router's shift. -/
def kR (lam : ℕ) : ℕ := P.sc.klM (lOf P g lam) 0

/-- The gate's quotient. -/
def gQ (lam x i : ℕ) : R :=
  if P.y.h.gcl then ten P cell "g0" lam x i + 256 * ten P cell "gh" lam x i
  else ten P cell "gi" lam x i

/-- The constant of the key of a clamp table. -/
def clampK : R := 2 ^ 15 + 2 ^ 39

/-- **The part of a segment's key that is affine in the cells.** -/
def affG (sn : String) (lam x i : ℕ) : R :=
  let h := P.y.h
  let lamM := lam / 2
  let t (n : String) : R := ten P cell n lam x i
  let tM (n : String) : R := ten P cell n lamM x i
  if sn == "G" then site 0 (gQ P cell lam x i) (kGU P g false lam x) h.hgD (t "rg")
  else if sn == "U" then site 0 (t "u") (kGU P g true lam x) h.huD (t "ru")
  else if sn == "GH" then high (t "rg") (kGU P g false lam x) h.hgD
  else if sn == "UH" then high (t "ru") (kGU P g true lam x) h.huD
  else if sn == "UT" then t "u" + 2 ^ 15
  else if sn == "QK" then site 0 (t "qkw") (kQK P g lam x) h.hq (t "rqk")
  else if sn == "QKH" then high (t "rqk") (kQK P g lam x) h.hq
  else if sn == "N1" then site 0 (t "aw") (kL P g lam Layer.LK1) 2 (t "ra")
  else if sn == "N2" then site 0 (t "mw") (kL P g lam Layer.LK2) 2 (t "rm")
  else if sn == "N1H" then high (t "ra") (kL P g lam Layer.LK1) 2
  else if sn == "N2H" then high (t "rm") (kL P g lam Layer.LK2) 2
  else if sn == "O" then
    site 0 (xs P cell (2 * lam + 1) x i - xs P cell (2 * lam) x i) (kL P g lam Layer.Lko) h.ho
      (t "ro")
  else if sn == "D" then
    site 0 (xs P cell (2 * lam + 2) x i - xs P cell (2 * lam + 1) x i) (kL P g lam Layer.Lkd) h.hdD
      (t "rd")
  else if sn == "V" then site 0 (t "vw") (kL P g lam Layer.Lkv) h.hv (t "rv")
  else if sn == "OH" then high (t "ro") (kL P g lam Layer.Lko) h.ho
  else if sn == "DH" then high (t "rd") (kL P g lam Layer.Lkd) h.hdD
  else if sn == "VH" then high (t "rv") (kL P g lam Layer.Lkv) h.hv
  else if sn == "ROW" then
    ((ledMu h.xl (x % ledNR h.xl) : ℕ) : R) *
      dig P cell (2 * lam + x / ledNR h.xl) (x % ledNR h.xl) i
  else if sn == "CN1" then t "aw" + 2 ^ 28 * t "a" + clampK
  else if sn == "CN2" then t "mw" + 2 ^ 28 * t "m" + clampK
  else if sn == "CQK" then
    t "qkw" + 2 ^ 28 * (if x < P.y.dq then t "q" else ten P cell "kx" lam (x - P.y.dq) i) + clampK
  else if sn == "CV" then t "vw" + 2 ^ 28 * t "v" + clampK
  else if sn == "F" then
    (if h.gcl then t "g0" + 256 * t "gc" else t "gi") + 2 ^ 28 * t "s" + 2 ^ 15 + 2 ^ 40
  else if sn == "G0" then t "g0" + 128
  else if sn == "CG" then t "gh" + 2 ^ 28 * t "gc" + 49152 + 2 ^ 35 + 2 ^ 40
  else if sn == "XR" then 2 ^ 15 - 2 ^ 16 * tM "xr"
  else if sn == "LR" then
    site 0 (if h.rcl then 8 * tM "ly" + tM "l3" else tM "lr") (kR P g lam) h.hr (tM "rl")
  else if sn == "LT" then 2 * (tM "lr" + 2 ^ 14)
  else if sn == "DD" then
    -tM "lr" - sumN (h.NE - (x + 1)) fun k => ten P cell "sel" lamM (x + 1 + k) i
  else if sn == "LH" then high (tM "rl") (kR P g lam) h.hr
  else if sn == "SEL" then 128 * tM "sel"
  else if sn == "MR" then 2 ^ (if h.gcl then 14 else 15) + 2 ^ 17 * ten P cell "sc" lamM 0 i
  else if sn == "L3" then 32 * tM "l3"
  else if sn == "CLR" then tM "ly" + 2 ^ 25 * (tM "lr" - tM "l3") + clampK
  else 0

/-- The gate's (up: the up product's) accumulator at an entry that is not the routed expert's:
the normalized activation m against the dense unit (kinds 3, 4) or the shared expert's (5, 6). -/
def accDense (up : Bool) (lam x i : ℕ) : R :=
  let X := if moe P lam then (if up then 6 else 5) else (if up then 4 else 3)
  sumN P.y.h.d fun k2 => ten P cell "m" lam k2 i * wt P cell X (lOf P g lam) [k2, x]

/-- The same at an entry of the routed expert: the selector times the scaled activation xr against
expert e's unit (kinds 7, 8). -/
def accRouted (up : Bool) (lam x i : ℕ) : R :=
  sumN P.y.h.NE fun e =>
    ten P cell "sel" (lam / 2) e i *
      sumN P.y.h.d fun k2 =>
        ten P cell "xr" (lam / 2) k2 i *
          wt P cell (if up then 8 else 7) (lOf P g lam) [k2, e, x - P.y.h.fe]

/-- The attention output at layer lam, feature k2, token i: a tensor at profile 4, else public. -/
def attO (lam k2 i : ℕ) : R :=
  if P.y.h.p4 then ten P cell "o" lam k2 i else ((Layer.stubO P.y (lOf P g lam) i k2 : ℤ) : R)

/-- The gated product s u at feature k. -/
def gated (lam k i : ℕ) : R := ten P cell "s" lam k i * ten P cell "u" lam k i

/-- The down product's accumulator. -/
def accD (lam x i : ℕ) : R :=
  (sumN (if moe P lam then P.y.h.fe else P.y.h.f) fun k =>
      gated P cell lam k i * wt P cell 9 (lOf P g lam) [k, x]) +
    (if moe P lam then
      sumN P.y.h.NE fun e =>
        ten P cell "sel" (lam / 2) e i *
          sumN P.y.h.fe fun k =>
            gated P cell lam (P.y.h.fe + k) i * wt P cell 10 (lOf P g lam) [k, e, x]
    else 0)

/-- Coordinate cd of head hd of q and k before the rotation. -/
def accQK (lam hd cd i : ℕ) : R :=
  sumN P.y.h.d fun k2 => ten P cell "a" lam k2 i * wt P cell 0 (lOf P g lam) [hd, cd, k2]

/-- Entry x of q and k after the rotation by the rotary table at token i. -/
def rotQK (lam x i : ℕ) : R :=
  let dh := P.y.h.dh
  let hd := x / dh
  let cd := x % dh
  let C : R := ((Layer.ropeC P.y.h P.sc P.rope (lOf P g lam) i (cd / 2) false : ℤ) : R)
  let S : R := ((Layer.ropeC P.y.h P.sc P.rope (lOf P g lam) i (cd / 2) true : ℤ) : R)
  if cd % 2 == 0 then C * accQK P g cell lam hd cd i - S * accQK P g cell lam hd (cd + 1) i
  else S * accQK P g cell lam hd (cd - 1) i + C * accQK P g cell lam hd cd i

/-- The chosen expert's logit: the selector against the logits. -/
def selLr (lam i : ℕ) : R :=
  sumN P.y.h.NE fun e => ten P cell "sel" (lam / 2) e i * ten P cell "lr" (lam / 2) e i

/-- **The products in a segment's key.** -/
def gamG (sn : String) (lam x i : ℕ) : R :=
  if sn == "G" || sn == "U" then
    let up := sn == "U"
    2 ^ (16 - kGU P g up lam x) *
      (if routed P lam x then accRouted P g cell up lam x i else accDense P g cell up lam x i)
  else if sn == "V" then
    2 ^ (16 - kL P g lam Layer.Lkv) *
      sumN P.y.h.d fun k2 => ten P cell "a" lam k2 i * wt P cell 1 (lOf P g lam) [k2, x]
  else if sn == "O" then
    2 ^ (16 - kL P g lam Layer.Lko) *
      sumN P.y.dq fun k2 => attO P g cell lam k2 i * wt P cell 2 (lOf P g lam) [k2, x]
  else if sn == "D" then 2 ^ (16 - kL P g lam Layer.Lkd) * accD P g cell lam x i
  else if sn == "LR" then
    2 ^ (16 - kR P g lam) *
      sumN P.y.h.d fun k2 => ten P cell "m" lam k2 i * wt P cell 11 (lOf P g lam) [k2, x]
  else if sn == "N1" then
    2 ^ (16 - kL P g lam Layer.LK1) * (recip P cell (2 * lam) i * xs P cell (2 * lam) x i)
  else if sn == "N2" then
    2 ^ (16 - kL P g lam Layer.LK2) * (recip P cell (2 * lam + 1) i * xs P cell (2 * lam + 1) x i)
  else if sn == "QK" then 2 ^ (16 - kQK P g lam x) * rotQK P g cell lam x i
  else if sn == "XR" then ten P cell "sc" (lam / 2) 0 i * ten P cell "m" lam x i
  else if sn == "DD" || sn == "MR" then selLr P cell lam i
  else 0

/-- **The key of entry x of a segment on layer lam of the group at token i.** -/
def segG (sn : String) (lam x i : ℕ) : R := affG P g cell sn lam x i + gamG P g cell sn lam x i

end Terms

/-- Which entry of which segment stands in column j of call q. -/
def colG (y : Layer.Lay) (q j : ℕ) : Option (Seg × ℕ) :=
  (y.calls.getD q default).segs.findSome? fun s =>
    (s.pos.findIdx? (· == j)).map fun x => (s, x)

section Vectors

variable {R : Type} [CommRing R] (P : Layer.Pub) (g : ℕ) (cell : NameG → R)

/-- A call's key vector from a function on segments, layers, entries and tokens. -/
def kvOf (f : String → ℕ → ℕ → ℕ → R) (q X : ℕ) : R :=
  let lJ := (P.y.calls.getD q default).lJ
  let i := X % P.y.T
  let j := X / P.y.T % 2 ^ lJ
  let lam := X / P.y.T / 2 ^ lJ
  match colG P.y q j with
  | some (s, x) =>
    if s.moe && lam % 2 == 0 then (tauN P.y.fo q (t0N P.y.fo q) : R) else f s.name lam x i
  | none => (tauN P.y.fo q (t0N P.y.fo q) : R)

/-- **Call q's key number X at G.** -/
def kvG (q X : ℕ) : R := kvOf P (segG P g cell) q X

/-- The joint key vector at G. -/
def keyG (θ : R) (X : ℕ) : R := jointKey P.y.fo (kvG P g cell) θ X

/-- The joint table at G. -/
def tabG (θ : R) (u : ℕ) : R := jointTab P.y.fo θ u

theorem keyG_eq : keyG P g cell = jointKey P.y.fo (kvG P g cell) := rfl

theorem tabG_eq : (tabG P : R → ℕ → R) = jointTab P.y.fo := rfl

theorem segG_eq (sn : String) (lam x i : ℕ) :
    segG P g cell sn lam x i = affG P g cell sn lam x i + gamG P g cell sn lam x i := rfl

end Vectors

/-- **Where bit j of the count of row u of the joint table lies at G.** -/
def placeG (y : Layer.Lay) (u j : ℕ) : Option NameG :=
  if u % 2 ^ y.fo.cK < y.fo.NC ∧ j < 32 ∧ u < 2 ^ y.fo.d then
    some (.cell (iB y) (u / 2 ^ y.fo.cK % 2 ^ (y.h.lmb - 5) * 32 + j)
      (u % 2 ^ y.fo.cK * 2 ^ (y.fo.kT + 5 - y.h.lmb) + u / 2 ^ y.fo.cK / 2 ^ (y.h.lmb - 5)))
  else none

/-- The planes at G as one vector: entry X = u * 32 + j is the bit at placeG u j; 0 where there is
no place. -/
def bitsG {R : Type} [Zero R] (y : Layer.Lay) (cell : NameG → R) (X : ℕ) : R :=
  match placeG y (X / 32) (X % 32) with
  | some x => cell x
  | none => 0

end OnBytes.Ends.G

#print axioms OnBytes.Ends.G.site_split
#print axioms OnBytes.Ends.G.ten
#print axioms OnBytes.Ends.G.wt
#print axioms OnBytes.Ends.G.affG
#print axioms OnBytes.Ends.G.gamG
#print axioms OnBytes.Ends.G.kvG
#print axioms OnBytes.Ends.G.keyG
#print axioms OnBytes.Ends.G.tabG
#print axioms OnBytes.Ends.G.placeG
#print axioms OnBytes.Ends.G.bitsG
#print axioms OnBytes.Ends.G.keyG_eq
