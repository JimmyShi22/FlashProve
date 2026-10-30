-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionShape.lean: the shape of the attention sub-proof.

A proof has one attention sub-proof for each group of layers. This file holds the first part of what
follows from public parameters alone: the sizes, the table of exponentials, the lookup calls and
the layout of the matrices. OnBytes/Model/AttentionPlan.lean builds the rest on it. Nothing here
reads a word of a proof. The file follows verifier/src/vf_attention_shape.h, except the index
routines at its head (they are in OnBytes/Model/Tensors.lean), and these parts of
verifier/src/vf_attention_check.h: aforkShapeHid; holds, npOf, nvKF, nvE, nvVM, nvVD, nvF, nvH and
scdDegrees; and the number NP that its function plan computes. OnBytes/Model/AttentionConfig.lean
fills Cfg, OnBytes/Model/AttentionPlan.lean calls shapeHid, and the files of the check read Shape.

What the file holds, in this order. Each section begins with its own account.
 1. Words: tile, place, gap, softmax weight, pair, lookup call, piece, segment, padding.
 2. Functions on points.
 3. The configuration, and how its numbers relate to the C++ program's words of 32, 64 and 128 bits.
 4. The shape (its account stands with the configuration's).
 5. Variables and degrees of the sumchecks.
 6. The names of the refusals, and how a refusal is named.

Not claimed. The file holds no theorem. The C++ program computes the table of exponentials in
floating point. Here it is computed in whole numbers (OnBytes/Model/AttentionExp.lean, whose head
says what is known of the two tables' agreement). That a caller's numbers fit the C++ program's
words is arithmetic on the ranges stated at Cfg; no theorem and no test here covers it (section The
configuration).
-/
import OnBytes.Iop.Ground
import OnBytes.Model.Forest
import OnBytes.Model.Tensors
import OnBytes.Model.AttentionExp

namespace OnBytes.Attention

open OnBytes.Model (scaleNat refuseIf roundUp TenAt clamp)

/-- The value of x, or a failure under the given name if there is none. -/
def orRefuse {α : Type} (x : Option α) (name : String) : Except String α :=
  match x with
  | some a => .ok a
  | none => .error name

/-! ## Words

(The page on this sub-proof is docs/format/11-3-attention-segment.md, section 11.3 of the
format.) The scores of a query head form a matrix: a row for each query token, a column for each key
token. It is cut into square tiles. Only the tiles on and below the diagonal are used. A place is
one entry of such a tile at one head of keys and values. The gap at a place is the row's maximum
minus the score. The softmax weight at the place is the entry of the table of exponentials that
belongs to the gap. A pair (lam, a) is a layer of the group and one of the HA query heads that read
the same head of keys and values. A lookup call states that every key of a vector is a row of a
public table (Call in OnBytes/Model/Frame.lean). The keys are of seven kinds. A piece is the keys of
one kind for one pair, and a segment is all pieces of one kind in one call. The keys after a call's
last piece are padding.

## Functions on points

Small functions on points, which the check of the sub-proof applies to what the verifier drew:
eqAt, eqPts, onesOf, idOf, leOf.
-/

/-- The equality polynomial eq(z, idx) at the point z and the index idx of z.size bits. Coordinate 0
belongs to the top bit of idx. -/
def eqAt (z : Array E) (idx : Nat) : E :=
  (List.range z.size).foldl (fun p v =>
    let x := z.getD v zeroE
    mulE p (if (idx >>> (z.size - 1 - v)) % 2 == 1 then x else subE oneE x)) oneE

/-- The factor of one coordinate in eq(x, y): x y + (1 - x) (1 - y). -/
def eqPair (x y : E) : E := addE (mulE x y) (mulE (subE oneE x) (subE oneE y))

/-- The equality polynomial eq(x, y) of two points, over the x.size coordinates of x. A missing
coordinate of y counts as 0; the callers pass points of equal length. -/
def eqPts (x y : Array E) : E :=
  (List.range x.size).foldl (fun p v => mulE p (eqPair (x.getD v zeroE) (y.getD v zeroE))) oneE

/-- The product of all coordinates: eq(z, idx) at the index whose bits are all 1. -/
def onesOf (z : Array E) : E := z.foldl mulE oneE

/-- The multilinear extension of the map that sends an index to its number, at the point z.
Coordinate 0 belongs to the top bit. -/
def idOf (z : Array E) : E :=
  (List.range z.size).foldl (fun s v =>
    addE s (scaleNat (z.getD v zeroE) (2 ^ (z.size - 1 - v)))) zeroE

/-- The multilinear extension of the relation "the first index is at most the second", at the
points x and y, over the x.size coordinates of x. Coordinate 0 belongs to the top bit. A missing
coordinate of y counts as 0; the callers pass points of equal length. -/
def leOf (x y : Array E) : E :=
  (List.range x.size).reverse.foldl (fun le v =>
    let a := x.getD v zeroE
    let b := y.getD v zeroE
    addE (mulE (subE oneE a) b) (mulE (eqPair a b) le)) oneE

/-! ## The configuration

The configuration Cfg, and the shape Shape that the function shape derives from it: the sizes,
the table of exponentials, the lookup calls with their pieces and tables, and the layout of the
sub-proof's matrices (OnBytes/Model/AttentionHeard.lean says what `as`, ah, ao, qa and bA hold).
All calls of the sub-proof run as one lookup (OnBytes/Model/Forest.lean), and shapeHid adds the
numbers of that lookup.

Numbers. Every public number is a natural number. The C++ program computes in words of 32, 64 and
128 bits. A caller that keeps to the ranges stated at Cfg gets numbers that fit those words, so the
results agree. This is arithmetic on the ranges; no theorem and no test here covers it. A field of
Cfg that is a signed number in the C++ source comes from a word of 32 bits. Where such a word is
2^31 or more, the C++ program sees a negative number and refuses under the same name under which the
large number is refused here, by a reading of that source (no theorem). This holds for lt, lB, S,
rx, kFD, la, lmS and lmb. For lgk, ldh, ll and nmin the caller's tests exclude such a word (see
Cfg).
-/

/-- The seven kinds of segments of lookup keys. For a gap below C (see ShD) the remainder is the
gap modulo 2^sh and the flag is 0. For a gap of C or more the remainder is between 2^sh and 2^16 -
1, the flag is 1 and the softmax weight is 0. -/
inductive Seg where
  /-- the remainder of the gap and its flag, at the places of the tiles below the diagonal -/
  | rm
  /-- the remainder of the gap and its flag, at the places of the diagonal tiles -/
  | rd
  /-- the gap without its remainder, the flag and the softmax weight, below the diagonal -/
  | fm
  /-- the gap without its remainder, the flag and the softmax weight, at the places of the diagonal
  tiles -/
  | fd
  /-- the low 16 bits of the two remainders of the division that gives the output o -/
  | wl
  /-- the digits above the low 16 bits of the two remainders of the division that gives the output
  o -/
  | wh
  /-- the distance from the index of the maximum to the query's position -/
  | ix
  deriving DecidableEq, Repr, Inhabited

/-- All kinds of segments, in the order of their numbers 0 to 6. -/
def Seg.all : List Seg := [.rm, .rd, .fm, .fd, .wl, .wh, .ix]

/-- The four kinds of a call's table. A parameter file spells them KR, KFD, R16 and WH. -/
inductive Table where
  /-- the two bytes of the row's number, and the flag "the number is at least 2^sh" -/
  | kr
  /-- the exponentials, and rows for the gaps at which the softmax weight is 0 -/
  | kfd
  /-- the numbers below 2^16 -/
  | r16
  /-- the two bytes of the row's number -/
  | wh
  deriving DecidableEq, Repr, Inhabited

/-- True for the kinds whose table depends on the shift sh. A line of the call list (see Line) of
such a kind stands for one call for each value of sh in the group of layers. -/
def Table.bySh : Table → Bool
  | .kr | .kfd => true
  | _ => false

/-- True if keys of the segment kind s are looked up in a table of this kind. -/
def Table.admits : Table → Seg → Bool
  | .kr, .rm | .kr, .rd | .kfd, .fm | .kfd, .fd | .r16, .wl | .r16, .ix | .wh, .wh => true
  | _, _ => false

/-- One line of the call list: a name, the kind of table and the kinds of segments. -/
structure Line where
  /-- the call's name, without the shift -/
  name : String
  /-- the kind of table -/
  kind : Table
  /-- the kinds of segments whose keys the call holds -/
  segs : List Seg
  deriving DecidableEq, Repr, Inhabited

/-- The configuration of one attention sub-proof. The caller fills it from the public files; Ty
is in no file: it is a constant of the smallness test. The function shape uses lgk, ldh and ll
as exponents and divides by NAs and wcH without a test. The caller must have tested: ll ≤ 6;
H + 2^lgk ≤ 64; H 2^ldh ≤ 2^20; nmin ≤ 28; lmS ≤ 24; lmb ≤ 24; 1 ≤ NAs ≤ 64;
1 ≤ wcH; wcH 2^lt, wcO 2^lt and wcQ 2^lt are at most 2^24; Ty = 2^18. Model.Layer.layout and config
(OnBytes/Model/AttentionConfig.lean) make these tests, and plan tests Ty. The C++ record ACfg has
one more field, oInQa: whether the features of o count among those of qa. It is true by default and
nothing in verifier/src sets it, so shape is written for that case only. -/
structure Cfg where
  /-- a request has 2^lt tokens -/
  lt : Nat := 0
  /-- a tile has 2^lB tokens on each side -/
  lB : Nat := 0
  /-- there are 2^lgk heads of keys and values -/
  lgk : Nat := 0
  /-- a head has 2^ldh features -/
  ldh : Nat := 0
  /-- the group has 2^ll layers -/
  ll : Nat := 0
  /-- the largest softmax weight is 2^S -/
  S : Nat := 0
  /-- the step of the table of exponentials is 2^-rx -/
  rx : Nat := 0
  /-- the table of kind KFD has 2^kFD rows -/
  kFD : Nat := 0
  /-- a part of the matrix `as` has 2^lmS rows; this matrix holds five cells for each pair and place
  (five planes): two bytes of the remainder, the flag, two bytes of the softmax weight -/
  lmS : Nat := 0
  /-- a block has 2^la rows (see OnBytes/Model/Tensors.lean) -/
  la : Nat := 0
  /-- the matrix bA, which holds the bit planes of the lookup's counts, has 2^lmb rows -/
  lmb : Nat := 0
  /-- a call has at least 2^nmin keys -/
  nmin : Nat := 0
  /-- the number of query heads -/
  H : Nat := 0
  /-- for each layer of the group its shift: a step of the table of exponentials is 2^sh units of a
  score -/
  sh : Array Nat := #[]
  /-- the features in a column of the matrix ah -/
  wcH : Nat := 0
  /-- the features in a column of the matrix ao -/
  wcO : Nat := 0
  /-- the features in a column of the matrix qa -/
  wcQ : Nat := 0
  /-- the number of parts of the matrix `as` -/
  NAs : Nat := 1
  /-- the bound on a committed cell that the smallness test is meant to give -/
  Ty : Nat := 0
  /-- the call list -/
  lines : List Line := []
  deriving Repr, Inhabited

/-- One piece of a call's keys: the keys of one segment kind for one pair (lam, a). The pair stands
for the layer lam and, at each head g of keys and values, the query head g HA + a. The piece has
2^b keys, from key number off on. -/
structure Piece where
  /-- the kind of segment -/
  seg : Seg := .rm
  /-- the layer in the group -/
  lam : Nat := 0
  /-- which of the HA query heads that read one head of keys and values -/
  a : Nat := 0
  /-- the piece has 2^b keys -/
  b : Nat := 0
  /-- the number of its first key -/
  off : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- One lookup call of the sub-proof. -/
structure ACall where
  /-- the call as the lookup sees it: name, sizes and table -/
  call : Model.Call := {}
  /-- the kind of table -/
  kind : Table := .r16
  /-- the shift, for a kind whose table depends on it; otherwise 0 -/
  sh : Nat := 0
  /-- the kinds of segments in the call, each once, in the order of the list -/
  segs : List Seg := []
  /-- the pieces in the order of their keys -/
  pcs : Array Piece := #[]
  /-- the sum of the pieces' sizes: the keys from tot on are padding -/
  tot : Nat := 0
  deriving Inhabited

/-- True if the call holds keys of the segment kind s. -/
def ACall.holds (c : ACall) (s : Seg) : Bool := c.segs.contains s

/-- The number of the call's pieces of the segment kind s. -/
def ACall.npOf (c : ACall) (s : Seg) : Nat := (c.pcs.filter fun p => p.seg == s).size

/-- The numbers that depend on the shift, for one value of it. -/
structure ShD where
  /-- at a gap of C or more the softmax weight is 0 -/
  C : Nat := 0
  /-- the step between the rows of the table of kind KFD for the gaps of C or more -/
  rho : Nat := 0
  /-- the number of rows of the table of kind KFD for the gaps of C or more, without the rows that
  only fill the table up -/
  nHD : Nat := 0
  /-- what is added to the gap at a place above the diagonal of the scores -/
  Om : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The numbers that depend on the shift, for the shift sh. u0 is the length of the table of
exponentials and Smax the bound on a score. Meant for sh below 16; shape admits 4 to 12. -/
def shdOf (u0 Smax sh : Nat) : ShD :=
  let rho := 65536 - 2 ^ sh
  { C := u0 * 2 ^ sh, rho := rho, nHD := (4 * Smax + 1 + rho - 1) / rho,
    Om := 2 * Smax + u0 * 2 ^ sh }

/-! ## The shape -/

/-- The region of the tiles below the diagonal has 2^(nMOf cf) places for one pair, over all heads
of keys and values. The empty tile slots count (see Shape.cover). -/
def nMOf (cf : Cfg) : Nat := cf.lgk + 2 * cf.lt - 1

/-- The diagonal tiles have 2^(nDOf cf) places for one pair, over all heads of keys and values. -/
def nDOf (cf : Cfg) : Nat := cf.lgk + cf.lt + cf.lB

/-- A piece of the segment kind s has 2^(segBits cf s) keys. -/
def segBits (cf : Cfg) : Seg → Nat
  | .rm | .fm => nMOf cf
  | .rd | .fd => nDOf cf
  | .wl => 1 + cf.lgk + cf.lt + cf.ldh
  | .wh => cf.lgk + cf.lt + cf.ldh
  | .ix => cf.lgk + cf.lt

/-- The shape of the attention sub-proof: its configuration, and the sizes, the table of
exponentials and the calls with their tables, which the function shape derives from it. -/
structure Shape where
  /-- the configuration -/
  cf : Cfg := {}
  /-- the number of tokens, 2^lt -/
  T : Nat := 0
  /-- the side of a tile, 2^lB -/
  B : Nat := 0
  /-- the number of tiles along one side, 2^lnT -/
  nT : Nat := 0
  /-- half the number of tiles along one side -/
  hP : Nat := 0
  /-- the number of heads of keys and values, 2^lgk -/
  G : Nat := 0
  /-- the number of query heads that read one head of keys and values -/
  HA : Nat := 0
  /-- the features of a head, 2^ldh -/
  dh : Nat := 0
  /-- the features of q and of o in one layer -/
  dq : Nat := 0
  /-- the features of k and of v in one layer -/
  dkv : Nat := 0
  /-- the number of layers in the group, 2^ll -/
  Lam : Nat := 0
  /-- the length of the table of exponentials -/
  u0 : Nat := 0
  /-- lt - lB -/
  lnT : Nat := 0
  /-- see nMOf -/
  nM : Nat := 0
  /-- see nDOf -/
  nD : Nat := 0
  /-- la - lt: a block has the rows of 2^ls features -/
  ls : Nat := 0
  /-- the table of exponentials (see expTable) -/
  Tt : Array Nat := #[]
  /-- the lookup calls, in the order of the list -/
  calls : Array ACall := #[]
  /-- the columns of all parts of the matrix `as` together, rounded up to a multiple of NAs -/
  kAs : Nat := 0
  /-- the columns of the matrix bA; shapeHid sets it -/
  kbA : Nat := 0
  /-- the features in use in the matrix ah -/
  featH : Nat := 0
  /-- the features in use in the matrix ao -/
  featO : Nat := 0
  /-- the features in use in the matrix qa -/
  featQ : Nat := 0
  /-- featH, rounded up to whole columns -/
  fillH : Nat := 0
  /-- featO, rounded up to whole columns -/
  fillO : Nat := 0
  /-- featQ, rounded up to whole columns -/
  fillQ : Nat := 0
  /-- in ah: the first feature of the rows' maxima -/
  oMr : Nat := 0
  /-- in ah: the first feature of the denominators -/
  oZr : Nat := 0
  /-- in ah: the first feature of the index bits -/
  oIb : Nat := 0
  /-- in ao: the first feature of the top digit of the division's first remainder -/
  oRh : Nat := 0
  /-- in ao: the first feature of the top digit of the division's second remainder -/
  oRhp : Nat := 0
  /-- in qa: the first feature of q -/
  oQ : Nat := 0
  /-- in qa: the first feature of k -/
  oK : Nat := 0
  /-- in qa: the first feature of v -/
  oV : Nat := 0
  /-- in qa: the first feature of o -/
  oO : Nat := 0
  /-- where q is in qa, by this sub-proof's own numbers; group (AttentionConfig.lean) compares them
  with the owner's -/
  atQ : TenAt := {}
  /-- where k is in qa (see atQ) -/
  atK : TenAt := {}
  /-- where v is in qa (see atQ) -/
  atV : TenAt := {}
  /-- where o is in qa (see atQ) -/
  atO : TenAt := {}
  /-- the bound on a score: dh clamp^2 -/
  Smax : Nat := 0
  deriving Inhabited

/-- shdOf with this shape's numbers. -/
def Shape.shd (A : Shape) (sh : Nat) : ShD := shdOf A.u0 A.Smax sh

/-- segBits of this shape's configuration. -/
def Shape.segB (A : Shape) (s : Seg) : Nat := segBits A.cf s

/-- The number of pairs (lam, a) (see Piece). -/
def Shape.NP (A : Shape) : Nat := A.Lam * A.HA

/-- The tests that shape makes for one value sh of the shift. The last two are no-overflow
conditions (see wrapTests), for the keys of the segments fm and fd. -/
def shTests (cf : Cfg) (u0 Smax sh : Nat) : Except String Unit := do
  refuseIf (sh < 4 || sh > 12) "af-policy-sh"
  let d := shdOf u0 Smax sh
  let rows := 2 ^ cf.kFD
  refuseIf (rows < u0 + d.nHD || rows - u0 - d.nHD > d.nHD) "af-policy-kF"
  refuseIf (d.C + 65536 > 2 ^ 24) "af-policy-C"
  refuseIf (!(6 * Smax + 2 * d.C + 3 * 65536 + 2 ^ 32 + 2 ^ 33 * (cf.Ty * 257 + 128 + 2 ^ cf.S)
    < 2 ^ 61 - 1)) "af-no-wrap-N3"
  refuseIf (!(6 * Smax + 2 * d.C + 3 * 65536 < 2 ^ 32)) "af-no-wrap-N4"

/-- The no-overflow conditions of shape that do not depend on the shift. T is 2^lt. Each condition
belongs to one equation in the field. It says that the two sides, read as whole numbers, differ by
less than 2^61 - 1, in most conditions by less than 2^60. The prime of the base field
(OnBytes/Field/Word.lean) is larger, so the equation then holds over the whole numbers. The
equations:
 - N1: a row's maximum is the score at the row's index.
 - N2: a key of the segments rm, rd and wh is a row of its table.
 - N3 and N4 (in shTests): a key of the segments fm and fd is a row of its table.
 - N5: a row's denominator is the sum of its softmax weights.
 - N6: the two keys of the segment wl are numbers below 2^16.
 - N9: a key of the segment ix is a number below 2^16.
The C++ source has no N7 and no N8. Two bounds are of a different kind. The second half of N2, and
N4, say that the two sides differ in one part of a key by less than the power of two at which the
next part begins (2^20, 2^32), so that the parts agree one by one. 257 Ty and 16843009 Ty bound a
value of two and of four limbs. The sizes rest on the bound Ty on a committed cell, which the
smallness test is meant to give. No theorem here says that the equations hold over the whole
numbers. -/
def wrapTests (cf : Cfg) (T Smax : Nat) : Except String Unit := do
  let Ty := cf.Ty
  let TS := T * 2 ^ cf.S
  refuseIf (!(Ty * 16843009 + Smax < 2 ^ 60)) "af-no-wrap-N1"
  refuseIf (!(2 ^ 40 * Ty + 2 ^ 20 * (Ty + 128) + Ty + 128 + 2 ^ 41 < 2 ^ 61 - 1 &&
    Ty + 128 + 256 < 2 ^ 20)) "af-no-wrap-N2"
  refuseIf (!(TS + Ty * 16843009 < 2 ^ 60)) "af-no-wrap-N5"
  -- 2 TS clamp is for v, which is the output of a clamp, and for o, a rounded mean of values of v
  -- (no clamp). 2 TS + 1 is for the second key of wl, which is 2 Z - 1 minus the remainder in the
  -- first key; Z is the denominator.
  refuseIf (!(2 * TS * clamp + TS + 2 * TS * (Ty * 257) + 2 * TS + 1 + 65536 * (Ty + 128) + 65536
    < 2 ^ 60)) "af-no-wrap-N6"
  refuseIf (!(2 ^ (16 - cf.lt) * 2 * T < 2 ^ 60)) "af-no-wrap-N9"

/-- True if the call list is valid: every line has a segment, every segment is in a line of its
kind of table, and each of the seven kinds of segments occurs exactly once. Since every line has a
segment, so has every expanded call, and the claim that ties the call's keys to the committed cells
is not empty. -/
def linesValid (lines : List Line) : Bool :=
  lines.all (fun l => !l.segs.isEmpty) &&
  lines.all (fun l => l.segs.all l.kind.admits) &&
  Seg.all.all fun s => ((lines.flatMap (·.segs)).filter (· == s)).length == 1

/-- A call before its keys are placed: name, kind of table, shift, kinds of segments. -/
abbrev Listed : Type := String × Table × Nat × List Seg

/-- The calls that one line of the list stands for. shs holds the values of the shift in the group
of layers, in increasing order. A line whose table depends on the shift gives one call for each
value; the value is added to the name if there is more than one. -/
def expandLine (shs : List Nat) (l : Line) : List Listed :=
  if l.kind.bySh then
    shs.map fun sh => (l.name ++ (if shs.length == 1 then "" else toString sh), l.kind, sh, l.segs)
  else [(l.name, l.kind, 0, l.segs)]

/-- Gives each piece of a list the number of its first key, from off on. Returns the pieces and the
number after the last key. -/
def layOff (l : List Piece) (off : Nat) : Array Piece × Nat :=
  l.foldl (fun (st : Array Piece × Nat) p => (st.1.push { p with off := st.2 }, st.2 + 2 ^ p.b))
    (#[], off)

/-- The pieces of a call in the order of their keys, and the sum of their sizes. Larger pieces come
first. Pieces of one size keep the order: segment kind as listed, then lam, then a. A call whose
table depends on the shift holds only the layers that have its shift. -/
def placePieces (cf : Cfg) (HA : Nat) (kind : Table) (sh : Nat) (segs : List Seg) :
    Array Piece × Nat :=
  let listed : List Piece := segs.flatMap fun s =>
    (List.range (2 ^ cf.ll)).flatMap fun lam =>
      if kind.bySh && cf.sh.getD lam 0 != sh then []
      else (List.range HA).map fun a =>
        ({ seg := s, lam := lam, a := a, b := segBits cf s } : Piece)
  layOff (listed.mergeSort fun x y => decide (y.b ≤ x.b)) 0

/-- Row t of the table of kind KR: the low byte, the high byte from bit 20 on, and at bit 40 the
flag "t is at least 2^sh". -/
def rowKR (sh t : Nat) : Nat := t % 256 + t / 256 * 2 ^ 20 + (if t ≥ 2 ^ sh then 2 ^ 40 else 0)

/-- Row t of the table of kind WH: the low byte, and the high byte from bit 20 on. -/
def rowWH (t : Nat) : Nat := t % 256 + t / 256 * 2 ^ 20

/-- Row t of the table of kind KFD. The first Tt.size rows hold a gap and, from bit 33 on, its
softmax weight. The other rows are for the gaps at which that weight is 0, and have bit 32 set. The
first d.nHD of them go up in steps of d.rho. The rest only fill the table up: they go up from the
same start, moved by half a step. -/
def rowKFD (Tt : Array Nat) (d : ShD) (sh t : Nat) : Nat :=
  let u0 := Tt.size
  if t < u0 then t * 2 ^ sh + Tt.getD t 0 * 2 ^ 33
  else if t < u0 + d.nHD then d.C - 2 ^ sh + d.rho * (t - u0) + 2 ^ 32
  else d.C - 2 ^ sh + d.rho * (t - u0 - d.nHD) + d.rho / 2 + 2 ^ 32

/-- A table of 2^k rows from the function that gives a row. The type is that of Call.tau. -/
def tableOf (k : Nat) (row : Nat → Nat) : Option (Array UInt64) :=
  some ((Array.range (2 ^ k)).map fun t => UInt64.ofNat (row t))

/-- Places the keys of one call and builds its table. Refused: the call would have fewer than 2^10
or more than 2^44 keys. The lower limit cannot fail after shape's test af-policy-nmin; the C++
source has it too. The C++ program adds the call's name to the name of this refusal. The number iota
of the call is set later, by shapeHid. Call in OnBytes/Model/Frame.lean says what n, k, kappa, fn,
t0, tau and iota are. -/
def layCall (cf : Cfg) (HA Smax : Nat) (Tt : Array Nat) (x : Listed) : Except String ACall := do
  let (name, kind, sh, segs) := x
  let (pcs, tot) := placePieces cf HA kind sh segs
  let n := max (ceilLog2 tot) cf.nmin
  refuseIf (n < 10 || n > 44) "af-shape-call"
  let call : Model.Call :=
    match kind with
    | .kr => { name := name, n := n, kappa := 5, k := 16, fn := 2, tau := tableOf 16 (rowKR sh) }
    | .wh => { name := name, n := n, kappa := 5, k := 16, fn := 2, tau := tableOf 16 rowWH }
    | .r16 => { name := name, n := n, kappa := 5, k := 16, fn := 0 }
    | .kfd => { name := name, n := n, kappa := 5, k := cf.kFD, fn := 1, t0 := Tt.size,
                tau := tableOf cf.kFD (rowKFD Tt (shdOf Tt.size Smax sh) sh) }
  pure { call := call, kind := kind, sh := sh, segs := segs, pcs := pcs, tot := tot }

/-- Derives the sizes, the table of exponentials and the calls with their tables from the
configuration, and tests the configuration. The tests are made in the order of the C++ source. Each
failure has the name that it has there, except af-shape-call (see layCall). Both are by a reading of
that source (no theorem). The lower limit on kFD, 8, is above kappa = 5 (Call.kappa). The test that
there are at most twelve expanded calls is this function's own test of that bound: fill
(OnBytes/Model/AttentionConfig.lean) makes it earlier, under the name policy-call-list-A. -/
def shape (cf : Cfg) : Except String Shape := do
  let lt := cf.lt
  refuseIf (lt < 2 || lt > 16 || cf.lB + 2 > lt) "af-shape-tiles"
  let T := 2 ^ lt
  let lnT := lt - cf.lB
  let G := 2 ^ cf.lgk
  refuseIf (cf.H == 0 || cf.H % G != 0) "af-shape-heads"
  let HA := cf.H / G
  let dh := 2 ^ cf.ldh
  let dq := cf.H * dh
  let dkv := G * dh
  let Lam := 2 ^ cf.ll
  refuseIf (cf.sh.size != Lam) "af-shape-sh"
  refuseIf (cf.la < lt || cf.la - lt > cf.ldh || cf.la > 16) "af-shape-la"
  let ls := cf.la - lt
  -- A remainder of the division has three bytes: lt + S + 1 is at most 24.
  refuseIf (cf.S < 1 || cf.S > 14 || cf.rx < 1 || cf.rx > 12 || lt + cf.S + 1 > 24)
    "af-policy-softmax"
  let Tt ← orRefuse (expTable cf.S cf.rx) "af-policy-softmax"
  let Smax := dh * clamp * clamp
  refuseIf (cf.lmS > nDOf cf || cf.lmS < 1) "af-shape-lmS"
  let shs := (cf.sh.toList.mergeSort fun a b => decide (a ≤ b)).eraseDups
  refuseIf (cf.kFD < 8 || cf.kFD > 16) "af-policy-kF"
  shs.forM (shTests cf Tt.size Smax)
  wrapTests cf T Smax
  refuseIf (!linesValid cf.lines) "af-policy-call-list"
  let listed := cf.lines.flatMap (expandLine shs)
  refuseIf (cf.nmin < 10) "af-policy-nmin"
  -- A block is no larger than a column of ao or of qa, and whole blocks fill a column.
  refuseIf (2 ^ cf.la > cf.wcO * T || 2 ^ cf.la > cf.wcQ * T || cf.wcO % 2 ^ ls != 0 ||
    cf.wcQ % 2 ^ ls != 0) "af-shape-la"
  refuseIf (listed.length > 12) "af-policy-call-list"
  let calls ← listed.mapM (layCall cf HA Smax Tt)
  let cells := 5 * Lam * HA * (2 ^ nMOf cf + 2 ^ nDOf cf)
  let unit := cf.NAs * 2 ^ cf.lmS
  -- In ah a row's maximum and its denominator have four limbs each, for every layer and query head.
  let oIb := 8 * Lam * cf.H
  let featH := oIb + Lam * lt * cf.H
  let featO := 2 * Lam * dq
  let oK := 2 * Lam * dq
  let oV := oK + 2 * Lam * dkv
  let oO := oV + 2 * Lam * dkv
  let featQ := oO + 2 * Lam * dq
  pure {
    cf := cf, T := T, B := 2 ^ cf.lB, nT := 2 ^ lnT, hP := 2 ^ lnT / 2, G := G, HA := HA, dh := dh,
    dq := dq, dkv := dkv, Lam := Lam, u0 := Tt.size, lnT := lnT, nM := nMOf cf, nD := nDOf cf,
    ls := ls, Tt := Tt, calls := calls.toArray, kAs := (cells + unit - 1) / unit * cf.NAs,
    featH := featH, featO := featO, featQ := featQ, fillH := roundUp featH cf.wcH,
    fillO := roundUp featO cf.wcO, fillQ := roundUp featQ cf.wcQ, oMr := 0,
    oZr := 4 * Lam * cf.H, oIb := oIb, oRh := 0, oRhp := Lam * dq, oQ := 0, oK := oK, oV := oV,
    oO := oO, atQ := ⟨0, 2, Lam, dq⟩, atK := ⟨oK, 2, Lam, dkv⟩,
    atV := ⟨oV, 2, Lam, dkv⟩, atO := ⟨oO, 2, Lam, dq⟩, Smax := Smax }

/-- The number of elements of the committed vector that holds the sub-proof's tables of
evaluations. These are not the tables of its lookup calls. -/
def Shape.tableElems (A : Shape) : Nat :=
  let nKF := A.calls.foldl (fun n c => if c.kind == .kfd then n + c.segs.length else n) 0
  3 * A.kAs + (nKF + 6) * A.fillH + A.fillO * A.T / 2 ^ A.cf.la +
    (2 * nKF + 5) * (A.fillQ * A.T / 2 ^ A.cf.la) + 3 * A.kbA

/-- The tile (row, column) at tile slot sg of slot row P. The tiles below the diagonal are arranged
in hP slot rows: slot row P holds the P tiles of tile row P and then the tiles of tile row
nT - 1 - P. Meant for P below hP and sg below nT - 1; the tile slot nT - 1 holds no tile. -/
def Shape.cover (A : Shape) (P sg : Nat) : Nat × Nat :=
  if sg < P then (P, sg) else (A.nT - 1 - P, sg - P)

/-- The shape together with the numbers of the one lookup in which all its calls run. After shape
it derives the lookup's numbers and makes the lookup's tests, then the two conditions of the
attention sub-proof on them. It sets iota of every call, the number of columns of the matrix bA and
the number of padding keys in every tree of the lookup, and it refuses a call that is all padding.
That test is made here, on public numbers, and again by the lookup when a proof is read
(Forest.pad, OnBytes/Model/Look.lean). A tree holds at most 2^lid keys (lid is LIDB in the C++
source; the head of OnBytes/Model/Forest.lean explains the trees). -/
def shapeHid (lid : Nat) (cf : Cfg) : Except String (Shape × Model.Forest.Shape) := do
  let A ← shape cf
  let h ← Model.Forest.shape (A.calls.map (·.call)) lid
  -- Two tables of evaluations serve several calls: they are read at the last lmS, or lt + ldh,
  -- coordinates of the calls' key points (the points at which the lookup reads the key vectors).
  -- These coordinates are the same for all calls only if they are among the dT that place a key in
  -- its tree.
  refuseIf (h.dT < max cf.lmS (cf.lt + cf.ldh)) "forest-depth-A"
  let kbA ← Model.Forest.planeCols h cf.lmb
  let calls := A.calls.mapIdx fun q c => { c with call := { c.call with iota := h.iota.getD q 0 } }
  -- The padding keys of a call are one run of keys, from number tot to the last.
  let counted ← calls.foldlM (fun (st : Array Nat × Nat) c => do
    let pub ← Model.Forest.pubRun h st.1 st.2 c.tot (2 ^ c.call.n - c.tot)
    pure (pub, st.2 + 1)) (Model.Forest.noPub h, 0)
  Model.Forest.pubAsk h counted.1
  pure ({ A with kbA := kbA, calls := calls },
    { h with pub := counted.1, calls := calls.map (·.call) })

/-! ## Variables and degrees of the sumchecks

The numbers of variables of the sub-proof's sumchecks (nvKF, nvE, nvVM, nvVD, nvF, nvH) and the
degrees of one more (scdDegrees).
-/

/-- The number of variables of the sumcheck for the scores of the segment kind seg (fm, or else
fd). -/
def Shape.nvKF (A : Shape) (seg : Seg) : Nat :=
  if seg == .fm then A.cf.lgk + 2 * A.lnT - 1 + A.cf.ldh else A.cf.lgk + A.lnT + A.cf.ldh

/-- The number of variables of the sumcheck for the product of denominator and output. -/
def Shape.nvE (A : Shape) : Nat := A.cf.lgk + A.cf.lt

/-- The number of variables of the sumcheck for the value product below the diagonal. -/
def Shape.nvVM (A : Shape) : Nat := A.cf.lgk + 2 * A.lnT - 1 + A.cf.lB

/-- The number of variables of the sumcheck for the value product on the diagonal. -/
def Shape.nvVD (A : Shape) : Nat := A.cf.lgk + A.lnT + A.cf.lB

/-- The number of variables of the sumcheck for the score at the index of the maximum. -/
def Shape.nvF (A : Shape) : Nat := A.cf.lt + A.cf.lgk + A.cf.ldh

/-- The number of variables of the sumcheck for the claim that the index bits are bits. The last 4
are for the number of the bit: an index has lt bits, at most 16 (af-shape-tiles). -/
def Shape.nvH (A : Shape) : Nat := A.cf.lt + A.cf.lgk + 4

/-- The degrees of the rounds of the sumcheck for the key at the index of the maximum: 2 in a bit
of the key's position, lt + 2 in a bit of the head of keys and values, lt + 1 in a bit of the
query's position. -/
def Shape.scdDegrees (A : Shape) : List Nat :=
  List.replicate A.cf.lt 2 ++ List.replicate A.cf.lgk (A.cf.lt + 2) ++
    List.replicate A.cf.lt (A.cf.lt + 1)

/-! ## The names of the refusals

The names of the refusals: shapeNames.

A function that tests public numbers returns a value or the name of the first test that failed. The
tests, their order and their names are those of the C++ source, by a reading of it (no theorem). One
name is shorter here: the C++ program ends af-shape-call with the call's name, which comes from a
file. shapeNames lists all names of this file.
-/

/-- The names under which this file refuses. shapeHid also passes on the refusals of
OnBytes/Model/Forest.lean, which lists its own names. -/
def shapeNames : List String :=
  ["af-shape-tiles", "af-shape-heads", "af-shape-sh", "af-shape-la", "af-policy-softmax",
   "af-shape-lmS", "af-policy-kF", "af-policy-sh", "af-policy-C", "af-no-wrap-N3", "af-no-wrap-N4",
   "af-no-wrap-N1", "af-no-wrap-N2", "af-no-wrap-N5", "af-no-wrap-N6", "af-no-wrap-N9",
   "af-policy-call-list", "af-policy-nmin", "af-shape-call", "forest-depth-A"]

end OnBytes.Attention
