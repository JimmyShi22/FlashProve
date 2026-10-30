-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionHeard.lean: the records that the parts of the check of the attention
sub-proof pass to one another, and the terms that the attention files use.

The check has seven parts, which OnBytes/Model/Attention.lean lists. Three groups of them pass data
to one another: the lookup's and the sub-proof's own messages (parts 1 and 2), the tables (part 3)
and the claims (part 6). A later part reads only what an earlier part has stored. This file defines
the records that store it, and a few functions on the pieces of a call that several parts use. Heard
stands for what the verifier has received and drawn so far.

Terms. The section Terms below explains the words that the attention files use.

Main definitions: PW, pieces, inner, sumW, timesW, lastHolding, tileSums, PlaneClaim, Score, Divide,
Attain, ScoreTables, Tables, Heard, Joins.

This file receives nothing and tests nothing. It holds no theorem.
-/
import OnBytes.Model.Look
import OnBytes.Model.AttentionShape
import OnBytes.Model.AttentionSums

namespace OnBytes.Attention

open OnBytes.Model

/-! ## Terms

The section Words of OnBytes/Model/AttentionShape.lean explains tile, place, gap, softmax weight,
pair, lookup call, piece, segment and padding. Seg and Table there name the kinds of segments (rm,
rd, fm, fd, wl, wh, ix) and of a call's table (KR, KFD, R16, WH). The attention files add the
following.
 - Heads. g is a head of keys and values. The pair (lam, a) stands, at each g, for the query head
   g HA + a of layer lam. Pair number b is (b / HA, b % HA).
 - Slot rows. The tiles below the diagonal are numbered by a slot row P and a tile slot sg within it
   (Shape.cover). The tiles on the diagonal are numbered by their tile row. These slots are not the
   slots of sent scalars below.
 - Unit. A call together with one segment that it holds.
 - Key point. The lookup draws one point for all calls: zx, on the positions within a tree, and
   zy, on the trees. A call with one tree has the key point zx. A call with 2^i trees has the last i
   coordinates of zy, put before zx (Forest.pad in OnBytes/Model/Look.lean). So a key point has a
   coordinate for each bit of a key's number, and all key points end in the same coordinates. The
   last coordinates of a key point, as many as a piece of a segment has bits, are the segment's
   inner point. They are the same for all pieces of the segment. The first coordinates pick the
   piece and give it its weight.
 - Slot. The number of a scalar that the prover sends. It also names the hidden value that the
   scalar stands for (OnBytes/Model/Hide.lean).
 - Key form. The affine form for the multilinear extension of a call's key vector at its key point.
   The lookup has one claim, the join, that takes the key forms of all calls.
 - Row of a sumcheck. The one claim that a sumcheck leaves. OnBytes/Model/AttentionSums.lean
   explains it, the two kinds of sumcheck (of products, with its maps A_b and B_b; by degrees) and
   end value.
 - Index of a row of scores. The key token at which the row has its maximum.
 - The five committed matrices, under the names of the C++ verifier (vf_attention_check.h). `as`:
   five planes for each pair and place, namely two bytes of the gap's remainder, a flag, and two
   bytes of the softmax weight. ah: for each row of scores its maximum, its denominator and the bits
   of its index. ao: the high parts of the division's two remainders. qa: queries, keys, values and
   outputs; the layer sub-proof commits to it. bA: the bit planes of the lookup's multiplicities.
   The prover commits to `as` in NAs parts, each a matrix of its own with 2^lmS rows, so the list of
   matrices has NAs + 4 members. Cell number n of `as` is row n mod 2^lmS of column n / 2^lmS, and
   column c is in part c / (kAs / NAs), where kAs is the number of columns of all parts together.
 - Table. Short for table of evaluations: sums over blocks of rows of one of the five matrices under
   public weights (OnBytes/Model/AttentionTables.lean). A table on `as` is the tables of its parts
   side by side, so that column c of `as` is entry c. The public table of a lookup call is always
   called the call's table.
 - The values of the division. ACC is the accumulator, the sum of softmax weights times values. ZC
   is the denominator, the sum of the softmax weights. ZO is the denominator times the output. RH
   and RHP are the high parts of the two remainders at wl's inner point. RH2 and RHP2 are the same
   two high parts at wh's inner point. IB_k is bit k of the index at ix's inner point.
 - The values of a unit of the scores. R0 and R1 are the two bytes of the gap's remainder, FL is the
   flag, and E0 and E1 are the two bytes of the softmax weight: the five planes of `as`, in this
   order. MS is the row maximum, and SS is the score. A unit of a call of kind KR has only the first
   three.
 - eq. The equality polynomial of two points (eqPts) or of a point and an index (eqAt, eqTab).

## The pieces of a call -/

/-- What a sum over pieces needs of one piece: its pair (lam, a) and its weight at the call's key
point. -/
structure PW where
  /-- the layer, counted within the sub-proof's group of layers -/
  lam : Nat
  /-- which of the HA query heads that read one head of keys and values -/
  a : Nat
  /-- the weight: eq of the key point's first coordinates with off / 2^b, the number of the piece's
  block of 2^b keys -/
  wp : E
  deriving Inhabited

/-- The order in which a sum takes the pieces of a unit: by lam, then by a. -/
def PW.le (x y : PW) : Bool := x.lam < y.lam || (x.lam == y.lam && x.a ≤ y.a)

/-- The pieces of segment s in call c, each with its weight at the call's key point zk, by lam and
then by a. The order in which the pieces are placed in the call is different: there the larger
pieces come first. -/
def pieces (c : ACall) (zk : Array E) (s : Seg) : Array PW :=
  let found := c.pcs.toList.filterMap fun pc =>
    if pc.seg == s then
      some { lam := pc.lam, a := pc.a,
             wp := eqAt (zk.extract 0 (c.call.n - pc.b)) (pc.off >>> pc.b) : PW }
    else none
  (found.mergeSort PW.le).toArray

/-- The inner point of segment s at the key point zk: its last coordinates, as many as a piece of
the segment has bits. If zk is shorter, all of zk is returned. Forest.pad has tested that zk has the
call's n coordinates; scoreUnit and divide test the inner point's length again, planeUnit does
not. -/
def inner (S : Shape) (zk : Array E) (s : Seg) : Array E :=
  zk.extract (zk.size - S.segB s) zk.size

/-- The sum of the pieces' weights. -/
def sumW (v : Array PW) : E := v.foldl (fun s x => addE s x.wp) zeroE

/-- Each piece's weight times f. -/
def timesW (v : Array PW) (f : E) : Array E := v.map fun x => mulE x.wp f

/-- The number of the last call in list order that holds segment s. -/
def lastHolding (S : Shape) (s : Seg) : Option Nat :=
  (S.calls.toList.zipIdx.filter fun x => x.1.holds s).getLast?.map (·.2)

/-! ## The tiles below the diagonal -/

/-- Tile weights from weights on slot rows and tile slots. There are hP slot rows of nT tile slots,
and the last tile slot of each slot row is empty. eP holds a weight for each slot row, es one for
each tile slot of a slot row. Tile slot sg of slot row P stands for the tile that Shape.cover names,
and has the weight eP[P] es[sg]. Returns, for each tile row and for each tile column, the sum of the
weights of its tile slots. A missing weight counts as 0. -/
def tileSums (S : Shape) (eP es : Array E) : Array E × Array E :=
  let zeros := Array.replicate S.nT zeroE
  (List.range S.hP).foldl (init := (zeros, zeros)) fun acc P =>
    (List.range (S.nT - 1)).foldl (init := acc) fun (wI, wJ) sg =>
      let w := mulE (eP.getD P zeroE) (es.getD sg zeroE)
      let tile := S.cover P sg
      (wI.modify tile.1 (addE · w), wJ.modify tile.2 (addE · w))

/-! ## What parts 1 and 2 store -/

/-- A point on the planes of the matrix `as`, with the slots of the plane values sent there. -/
structure PlaneClaim where
  /-- the call's number in list order -/
  call : Nat
  /-- the segment; the C++ record has it too, and no claim reads it -/
  seg : Seg
  /-- the segment's inner point -/
  z : Array E
  /-- true for a segment of the diagonal tiles -/
  isD : Bool
  /-- the segment's pieces -/
  pw : Array PW
  /-- the slot of the first plane's value -/
  s0 : Nat
  /-- the number of planes whose values were sent -/
  np : Nat

/-- What is stored of one unit (call, segment) of the scores: the parts of its inner point, the slot
of the first of the seven values sent, and its sumcheck. -/
structure Score where
  /-- the call's number in list order -/
  call : Nat
  /-- the number of this unit's entry in the list of plane claims -/
  claim : Nat
  /-- the segment: fm or fd -/
  seg : Seg
  /-- the segment's pieces -/
  pw : Array PW
  /-- the inner point's coordinates of g -/
  zg : Array E
  /-- below the diagonal: the coordinates of the tile slot within its slot row -/
  zs : Array E := #[]
  /-- the coordinates of the row within a tile -/
  zi : Array E
  /-- the coordinates of the column within a tile -/
  zj : Array E
  /-- for each tile row, its weight at the inner point -/
  wI : Array E
  /-- the slot of the first of the seven values -/
  s0 : Nat
  /-- the sumcheck, with the claim that it leaves -/
  sc : Sc3

/-- What is stored of the division and of the value product. -/
structure Divide where
  /-- the pieces of segment wl -/
  pwW : Array PW
  /-- the pieces of segment ix -/
  pwX : Array PW
  /-- the pieces of segment wh -/
  pwH : Array PW
  /-- the number of the call that holds segment wh -/
  qWH : Nat
  /-- the first coordinate of wl's inner point: it picks one of the two remainders -/
  zsl : E
  /-- wl's inner point: g -/
  zgW : Array E
  /-- wl's inner point: the token -/
  ziW : Array E
  /-- wl's inner point: the feature within a head -/
  zcW : Array E
  /-- ix's inner point: g -/
  zgX : Array E
  /-- ix's inner point: the token -/
  ziX : Array E
  /-- wh's inner point: g -/
  zgH : Array E
  /-- wh's inner point: the token -/
  ziH : Array E
  /-- wh's inner point: the feature within a head -/
  zcH : Array E
  /-- the slot of the first of the five values ACC, ZO, ZC, RH, RHP -/
  s5 : Nat
  /-- the slot of the first index bit's value -/
  sIB : Nat
  /-- the slot of the first of the two values RH2, RHP2 -/
  s5h : Nat
  /-- the sumcheck for the product of denominator and output -/
  scE : Sc3
  /-- the drawn element gam, which combines accumulator and denominator in one sum: ACC + gam ZC -/
  gam : E
  /-- the slot of the first of the value product's two sums -/
  sCl : Nat
  /-- the value product's sumcheck below the diagonal -/
  vpm : Sc3
  /-- for each tile column, its weight at the point of the sumcheck vpm -/
  wJv : Array E
  /-- the value product's sumcheck on the diagonal -/
  vpd : Sc3

namespace Divide

/-- The slot of ACC, the accumulator. -/
def sACC (d : Divide) : Nat := d.s5

/-- The slot of ZO, the product of denominator and output. -/
def sZO (d : Divide) : Nat := d.s5 + 1

/-- The slot of ZC, the denominator. -/
def sZC (d : Divide) : Nat := d.s5 + 2

/-- The slot of RH, the first remainder's high part. -/
def sRH (d : Divide) : Nat := d.s5 + 3

/-- The slot of RHP, the second remainder's high part. -/
def sRHP (d : Divide) : Nat := d.s5 + 4

/-- The last lB coordinates of wl's token: the token's position within the tile. -/
def zilo (d : Divide) (S : Shape) : Array E := d.ziW.extract S.lnT (S.lnT + S.cf.lB)

end Divide

/-- What is stored of the test that the row maximum is attained and of the test that the index's
cells are bits. -/
structure Attain where
  /-- the drawn point for the maxima: g -/
  tg : Array E
  /-- the drawn point for the maxima: the token -/
  ti : Array E
  /-- the slot of the first maximum's value -/
  sM6 : Nat
  /-- the sumcheck for the score at the index -/
  scF : Sc3
  /-- the sumcheck for the key at the index -/
  scd : Scd
  /-- the sumcheck for the bits -/
  scH : Sc3

namespace Attain

/-- The point of the score's sumcheck: the token. -/
def ri (x : Attain) (S : Shape) : Array E := x.scF.r.extract 0 S.cf.lt

/-- The point of the score's sumcheck: g. -/
def rg (x : Attain) (S : Shape) : Array E := x.scF.r.extract S.cf.lt (S.cf.lt + S.cf.lgk)

/-- The point of the score's sumcheck: the feature within a head. -/
def rc (x : Attain) (S : Shape) : Array E := x.scF.r.extract (S.cf.lt + S.cf.lgk) x.scF.r.size

/-- The point of the key's sumcheck: the token of the key. -/
def pj (x : Attain) (S : Shape) : Array E := x.scd.r.extract 0 S.cf.lt

/-- The point of the key's sumcheck: g. -/
def pg (x : Attain) (S : Shape) : Array E := x.scd.r.extract S.cf.lt (S.cf.lt + S.cf.lgk)

/-- The point of the key's sumcheck: the token of the query. -/
def pi (x : Attain) (S : Shape) : Array E :=
  x.scd.r.extract (S.cf.lt + S.cf.lgk) (2 * S.cf.lt + S.cf.lgk)

/-- The slot of the key's end value for layer 0. -/
def sKC (x : Attain) : Nat := x.scd.sEnd

/-- The slot of the end value for bit k of the index of pair b. keyTerm in
OnBytes/Model/AttentionDivide.lean writes the same sum out; the two must agree. -/
def sIb (x : Attain) (S : Shape) (b k : Nat) : Nat := x.scd.sEnd + (S.Lam + b * S.cf.lt + k)

/-- The point of the bits' sumcheck: the token. -/
def ri2 (x : Attain) (S : Shape) : Array E := x.scH.r.extract 0 S.cf.lt

/-- The point of the bits' sumcheck: g. -/
def rg2 (x : Attain) (S : Shape) : Array E := x.scH.r.extract S.cf.lt (S.cf.lt + S.cf.lgk)

/-- The point of the bits' sumcheck: which bit. -/
def rk (x : Attain) (S : Shape) : Array E :=
  x.scH.r.extract (S.cf.lt + S.cf.lgk) (S.cf.lt + S.cf.lgk + 4)

end Attain

/-! ## What part 3 stores -/

/-- Where the three tables of one unit of the scores begin. -/
structure ScoreTables where
  /-- the table on the maxima -/
  tM : Nat
  /-- the table on the queries -/
  tQ : Nat
  /-- the table on the keys -/
  tK : Nat
  deriving Inhabited

/-- The tables, which are stored one after the other in one committed array. Each field that is a
number says where a table begins. -/
structure Tables where
  /-- the point at which the value product below the diagonal reads the matrix `as` -/
  ptM : Array E
  /-- the point at which the value product on the diagonal reads the matrix `as` -/
  ptD : Array E
  /-- on `as`, at the lookup's point: it serves every plane claim -/
  tA : Nat
  /-- on `as`, at ptM -/
  tVM : Nat
  /-- on `as`, at ptD -/
  tVD : Nat
  /-- the tables of each unit of the scores, in the order of the list of scores -/
  score : Array ScoreTables
  /-- on ah, at wl's token -/
  hW : Nat
  /-- on ah, at ix's token -/
  hX : Nat
  /-- on ah, at the token of the sumcheck for denominator times output -/
  hE : Nat
  /-- on ah, at the drawn token for the maxima -/
  hT : Nat
  /-- on ah, at the query's token of the key's sumcheck -/
  hPi : Nat
  /-- on ah, at the token of the bits' sumcheck -/
  hR2 : Nat
  /-- on ao, at the lookup's point: it serves wl and wh -/
  tO : Nat
  /-- on qa: the output -/
  qO : Nat
  /-- on qa: the values below the diagonal -/
  qVM : Nat
  /-- on qa: the values on the diagonal -/
  qVD : Nat
  /-- on qa: the query of the score at the index -/
  qF : Nat
  /-- on qa: the key of the score at the index -/
  qKx : Nat
  /-- on bA, at the leaves' point -/
  tBit0 : Nat
  /-- on bA, at the bits' point -/
  tBit1 : Nat
  /-- on bA: the sum of all multiplicities -/
  tPin : Nat
  /-- pairs (where a table begins, its length), the latest first. If two pairs have the same
  beginning, the later one counts: a search from the front finds it first. -/
  tabLen : List (Nat × Nat)
  /-- the tables as the smallness test takes them -/
  funs : Array Model.HFun

/-! ## What the claims read -/

/-- What the claims read: the shape, and what parts 1 to 3 have stored. -/
structure Heard where
  /-- the shape -/
  S : Shape
  /-- what the lookup of the sub-proof's calls has stored -/
  g : Model.Forest.Heard
  /-- the plane claims, in the order in which their values were sent -/
  planes : Array PlaneClaim
  /-- the units of the scores, in the order in which their values were sent -/
  scores : Array Score
  /-- the division and the value product -/
  d : Divide
  /-- the maximum and the index's bits -/
  x : Attain
  /-- the tables -/
  t : Tables
  /-- the number of the tables' array in the sub-proof's list of arrays -/
  iU3 : Nat

/-- The calls' key forms. -/
structure Joins where
  /-- kf[q] is the key form of call q -/
  kf : Array Aff
  /-- joined[q] counts how often the key form of call q has been set -/
  joined : Array Nat

namespace Joins

/-- No key form is set yet, for n calls. -/
def empty (n : Nat) : Joins :=
  { kf := Array.replicate n (Aff.ofConst zeroE), joined := Array.replicate n 0 }

/-- Sets the key form of call q and counts it. Does nothing if there is no call q. -/
def set (j : Joins) (q : Nat) (v : Aff) : Joins :=
  { kf := j.kf.setIfInBounds q v, joined := j.joined.modify q (· + 1) }

end Joins

end OnBytes.Attention
