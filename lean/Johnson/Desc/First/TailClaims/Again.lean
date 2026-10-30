-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/Again.lean: DEFINITIONS WITH CODE; NO THEOREM: THE TESTS THAT THE
SMALLNESS TEST's TWO SELF TESTS CALL (Johnson/Desc/First/TailClaims/SelfTests.lean: selfTestP,
rkSelfTestP), AS TEXT OF THE DESCRIPTION: so that these call no function of `verify-on-bytes` that
can say no, but the field's own test for 0 (isZeroE, OnBytes/Field/Ext.lean).
WHAT THEY ARE. "No entry's weight is 0" (noneZero, allBelow), and A SECOND COMPUTATION: the pieces
of the two lookup calls, the lookup's public numbers, the calls' points, and the weights that the
adding has left on the rows of ZZ, BZ and the symbol arrays are reckoned again from the plan's
numbers, chi and the drawn points, and held against what stands in the record and the ledger.
A COPY BY PROGRAM: each definition is `verify-on-bytes`'s own (OnBytes/Model/Tail.lean:
noneZero, isPow2, wants, forestHeld, pieceHeld, callHeld, Want.meets, noneMeet, piecesTile,
pointsHeld, pieceWeightsHeld, leE, neighboursDiffer, tieShapeHeld, tieWeightsHeld, planesShapeHeld,
planesWeightsHeld, readShapeHeld, readWeightsHeld; OnBytes/Model/FormF.lean: allFrom, allBelow,
EqRun.allLoop, EqRun.all), with its comment, TOKEN FOR TOKEN but for the calls among them. It says
nothing in other words than that text does. A theorem of agreement is another file's. The records
and the functions that cannot refuse (weightsOf, zOf, callWeightAgain, EqRun.start | value | next,
clog2, powE and the like), and isZeroE, are called by name.

-/
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

/-- True if p holds at i, i + 1, .., i + count - 1. It builds no list. -/
def allFrom (p : Nat → Bool) : (count i : Nat) → Bool
  | 0, _ => true
  | count + 1, i => p i && allFrom p count (i + 1)

/-- True if p holds at every number below n. -/
def allBelow (n : Nat) (p : Nat → Bool) : Bool := allFrom p n 0

/-- True if test i (eq(z, idx + i)) holds for i = done, .., done + count - 1, where r is at index
idx + done. -/
def EqRun.allLoop (test : Nat → E → Bool) : (count done : Nat) → EqRun → Bool
  | 0, _, _ => true
  | count + 1, i, r => test i r.value && EqRun.allLoop test count (i + 1) r.next

/-- True if test i (eq(z, first + i)) holds for every i below count. -/
def EqRun.all (z : Array E) (first count : Nat) (test : Nat → E → Bool) : Bool :=
  EqRun.allLoop test count 0 (EqRun.start z first)

/-- True if L holds the entries first, .., first + count - 1 and none of them is 0. -/
def noneZero (L : Array E) (first count : Nat) : Bool :=
  decide (first + count ≤ L.size) && (L.extract first (first + count)).all fun x => !isZeroE x

/-- True if x is a power of two. -/
def isPow2 (x : Nat) : Bool := x != 0 && 2 ^ Nat.log2 x == x

/-- The number of blocks of ZZ's rows and the pieces of the two calls, computed again without t2BL
and piecesF. The first block has 2^floor(log2 tau) rows; the second, if there is one, has the
remaining rows. Returns none if rows remain and their number is not a power of two (C++:
internal-t2f-untiled). The second computation is not wholly independent: like t2BL it takes the
logarithm from Nat.log2, so a slip in Nat.log2 is not found. (The C++ goes two ways: a loop that
doubles in t2BL, the top bit of tau in tileSelfTestF.) -/
def wants (tl : HTailF2) : Option (Nat × List Want) :=
  let rows1 := 2 ^ Nat.log2 tl.tau
  let rows2 := tl.tau - rows1
  let nbW := if rows2 != 0 then 2 else 1
  if rows2 != 0 && !isPow2 rows2 then none
  else
    some (nbW, [0, 1].flatMap fun q =>
      { call := q, i := 0, row := q * nbW, r0 := 0, Rp := rows1, c0 := q * tl.mz, Cp := tl.mz } ::
        (if rows2 != 0 then
          [{ call := q, i := 1, row := q * nbW + 1, r0 := rows1, Rp := rows2, c0 := q * tl.mz,
             Cp := tl.mz }]
        else []))

/-- True if the lookup's public numbers are those that are written out here a second time. Both
calls have 2^n9 keys. -/
def forestHeld (tl : HTailF2) (g : Forest.Heard) : Bool :=
  let h := tl.f9
  let n9 := tl.z1.call.n
  let dW := min n9 tl.lidb
  let io := n9 - dW
  tl.z2.call.n == n9 && h.dT == dW && h.kT == 10 && h.NT == 2 ^ (io + 1) && h.rK == io + 1 &&
    h.iota == #[io, io] && h.first == #[0, 2 ^ io] && g.zy.size == io + 1 && g.zx.size == dW &&
    g.e.size == 2

/-- True if one piece of a call with 2^n keys is well placed. The last two conditions say that the
piece's 2^b places begin at a multiple of 2^b and end inside the call. -/
def pieceHeld (n : Nat) (p : Piece) : Bool :=
  p.Rp != 0 && p.Cp != 0 && decide (p.a ≤ 40) && 2 ^ p.a == p.Rp && p.r0 % p.Rp == 0 &&
    decide (p.Cp ≤ p.CP) && isPow2 p.CP && p.b == p.a + clog2 p.CP && decide (p.b ≤ n) &&
    p.off % 2 ^ p.b == 0 && decide (p.off + 2 ^ p.b ≤ 2 ^ n)

/-- True if call q is as expected: its name; a range table (fn = 0) of 2^10 rows for q = 0 and 2^8
for q = 1; counts of 32 bits (kappa = 5; Call.kappa is a number of the lookup, not a claim's
weight); the padding row 0; nbW pieces, each well placed (pieceHeld), whose ranges of places do not
overlap; n = max 10 (clog2 of the pieces' places), at most 44; a point of n coordinates; and iota,
which is n - lidb, or 0 if n is smaller. -/
def callHeld (tl : HTailF2) (g : Forest.Heard) (nbW q : Nat) : Bool :=
  let c := tl.zOf q
  let n := c.call.n
  let keys := c.pieces.foldl (fun s p => s + 2 ^ p.b) 0
  let a := c.pieces.getD 0 {}
  let b := c.pieces.getD 1 {}
  c.call.name == (if q == 0 then "R10z" else "R8d") && c.call.fn == 0 &&
    c.call.k == (if q == 0 then 10 else 8) && c.call.kappa == 5 && c.call.t0 == 0 &&
    c.pieces.size == nbW && decide (10 ≤ n) && decide (n ≤ 44) && (g.zk.getD q #[]).size == n &&
    c.pieces.all (pieceHeld n) &&
    (nbW != 2 || !(decide (a.off < b.off + 2 ^ b.b) && decide (b.off < a.off + 2 ^ a.b))) &&
    n == max 10 (clog2 keys) && c.call.iota == n - tl.lidb

/-- True if the rectangles of two expected pieces overlap. -/
def meets (w x : Want) : Bool :=
  decide (w.r0 < x.r0 + x.Rp) && decide (x.r0 < w.r0 + w.Rp) && decide (w.c0 < x.c0 + x.Cp) &&
    decide (x.c0 < w.c0 + w.Cp)

/-- True if no two rectangles of the list overlap. -/
def noneMeet : List Want → Bool
  | [] => true
  | w :: t => t.all (fun x => !meets w x) && noneMeet t

/-- True if the pieces of the two calls are the expected ones and tile ZZ: they are inside it, no
two overlap, and their areas add up to ZZ's. -/
def piecesTile (tl : HTailF2) (F : Fork) (W : List Want) : Bool :=
  let T := F.trees.getD tl.ix.ZZ {}
  T.name == "ZZ" && T.R == tl.tau && T.K == 2 * tl.mz && noneMeet W &&
    (W.foldl (fun s w => s + w.Rp * w.Cp) 0) == T.R * T.K &&
    W.all fun w =>
      let p := (tl.zOf w.call).pieces.getD w.i {}
      let row := T.rows.getD w.row {}
      p.tree == tl.ix.ZZ && p.row == w.row && p.r0 == w.r0 && p.Rp == w.Rp && p.c0 == w.c0 &&
        p.Cp == w.Cp && decide (w.r0 + w.Rp ≤ T.R) && decide (w.c0 + w.Cp ≤ T.K) &&
        row.coef.size == T.R && row.L.size == T.K

/-- True if the lookup's weights of the calls and the calls' points are those of the second
computation: both calls have the point (zy_1, .., zy_(rK - 1) | zx). -/
def pointsHeld (tl : HTailF2) (g : Forest.Heard) : Bool :=
  let n9 := tl.z1.call.n
  let io := n9 - min n9 tl.lidb
  [0, 1].all fun q =>
    g.e.getD q zeroE == callWeightAgain g q &&
      (List.range n9).all fun i =>
        (g.zk.getD q #[]).getD i zeroE ==
          (if i < io then g.zy.getD (1 + i) zeroE else g.zx.getD (i - io) zeroE)

/-- True if, on the rectangle of one expected piece, the weight of entry (r, cc) in the one equation
is -kappa e_q eq(zk, off + r CP + cc), where off + r CP + cc is the entry's place in the call, and
is not 0, and the row weights and the column weights of the piece's virtual row are 0 outside the
rectangle. kappa is the weight of the claim on the key vectors. The weight is a row weight times a
column weight, and so is the expected value. So it is enough to compare the first row and the first
column, in which no weight may be 0. -/
def pieceWeightsHeld (tl : HTailF2) (F : Fork) (g : Forest.Heard) (kappa : E) (w : Want) : Bool :=
  let p := (tl.zOf w.call).pieces.getD w.i {}
  let row := (F.trees.getD tl.ix.ZZ {}).rows.getD w.row {}
  let cv := row.coef
  let L := row.L
  let zk := g.zk.getD w.call #[]
  let ka := mulE kappa (callWeightAgain g w.call)
  let mk := subE zeroE ka
  let cv0 := cv.getD w.r0 zeroE
  let L0 := L.getD w.c0 zeroE
  !isZeroE ka && !isZeroE cv0 && !isZeroE L0 &&
    (EqRun.all zk p.off w.Cp fun cc e =>
      let v := mulE mk e
      !isZeroE v && mulE cv0 (L.getD (w.c0 + cc) zeroE) == v) &&
    ((List.range w.Rp).all fun r =>
      let v := mulE mk (eqPlainF zk (p.off + r * p.CP))
      !isZeroE v && mulE (cv.getD (w.r0 + r) zeroE) L0 == v) &&
    mulE (cv.getD (w.r0 + w.Rp - 1) zeroE) (L.getD (w.c0 + w.Cp - 1) zeroE) ==
      mulE mk (eqPlainF zk (p.off + (w.Rp - 1) * p.CP + (w.Cp - 1))) &&
    allFrom (fun r => isZeroE (cv.getD r zeroE)) w.r0 0 &&
    allFrom (fun r => isZeroE (cv.getD r zeroE)) (cv.size - (w.r0 + w.Rp)) (w.r0 + w.Rp) &&
    allFrom (fun cc => isZeroE (L.getD cc zeroE)) w.c0 0 &&
    allFrom (fun cc => isZeroE (L.getD cc zeroE)) (L.size - (w.c0 + w.Cp)) (w.c0 + w.Cp)

/-- Lexicographic order on the coordinates. It is used only to sort, so that equal elements become
neighbours. -/
def leE (a b : E) : Bool :=
  decide (a.c0 < b.c0) || (a.c0 == b.c0 && (decide (a.c1 < b.c1) ||
    (a.c1 == b.c1 && decide (a.c2 ≤ b.c2))))

/-- True if no two neighbours in the list are equal. -/
def neighboursDiffer : List E → Bool
  | a :: b :: t => a != b && neighboursDiffer (b :: t)
  | _ => true

/-- True if the tie of matrix mu meets the public conditions: its symbol array holds one row of
symbols in each row, no further row and no further column (J = 1, R = Rr = mS, Rd = 0, K1 = Kc = k),
the tie's claim is one of the plan's, and all vectors have the expected lengths. Under these
conditions every row and every column of the array holds symbols, so tieWeightsHeld has no other
places to consider. tieLeft and tieRight (FormF.lean) are written for any J. -/
def tieShapeHeld (tl : HTailF2) (F : Fork) (mu : Nat) : Bool :=
  let s := tl.shp.getD mu {}
  let X := F.trees.getD (tl.gtTree.getD mu 0) {}
  let row := X.rows.getD 0 {}
  let mS2 := ((tl.mats.getD mu {}).m + 2) / 3
  X.kind == .symbols && X.rows.size == 1 && X.R == s.Rr && X.K == s.Kc &&
    decide (mu < tl.tieObj.size) && mS2 == s.mS && s.J == 1 && s.R == mS2 && s.Rr == mS2 &&
    s.Rd == 0 && s.k == (tl.mats.getD mu {}).k && s.K1 == s.k && s.Kc == s.k &&
    (tl.rowX.getD mu #[]).size == mS2 && (tl.loX.getD mu #[]).size == 1 &&
    decide (tl.tieObj.getD mu 0 < F.planClaimsF) && row.coef.size == s.Rr && row.L.size == s.k &&
    (tl.gamX.getD mu #[]).size == s.k && (tl.gamV.getD mu #[]).size == s.k

/-- True if the weights of the tie of matrix mu equal a second computation from the drawn matrix and
the batching element theta. The tie's whole factor is ka = theta^(planClaims + the index of the
matrix's first equation), whatever the claim's own index is; planClaims is Fork.planClaimsF. Row i
of symbols has the weight (theta^Np)^i, with Np = tau rounded up to a power of two (pow2Again).
These weights must not be 0 and must differ from each other. The C++ source gives the reason: if two
rows had one weight, a false tie could pass. Only the challenges decide whether that happens, and
the design's error term for the tie is meant to cover these events whether or not they are refused.
No theorem here says so. The low digit of row 3 i + l of cells has the weight ka (theta^Np)^i B^l in
the ties' row of ZZ, with B = 2^20, the radix of FormF.lean; the high digit has 2^10 times that.
Column c of the symbol array has the weight -ka gam[c]. gam[c] is summed a second time by sumAgain,
with the column's index counted afresh and under powers that powE computes. Besides the field's
operations, the two computations still share the constants radb and t2D0 and the function powE, so a
slip in one of these is not found. L5: the column weights of the ties' row of ZZ. -/
def tieWeightsHeld (tl : HTailF2) (F : Fork) (L5 : Array E) (mu : Nat) : Bool :=
  let s := tl.shp.getD mu {}
  let row := (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}
  let np2 := pow2Again tl.tau
  let ka := powE F.theta (F.planClaimsF + tl.firstAgain mu)
  let hi := powersAgain F.theta np2 s.mS
  let c0 := tl.off.getD mu 0
  let c1 := tl.mz + c0
  let before := (List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0
  let xi2 := (Array.range tl.tau).map fun u => powE F.theta u
  (tl.loX.getD mu #[]).getD 0 zeroE == oneE &&
    (allBelow s.R fun R =>
      row.coef.getD R zeroE == hi.getD R zeroE && !isZeroE (row.coef.getD R zeroE)) &&
    neighboursDiffer (row.coef.toList.mergeSort leE) &&
    decide (s.m ≤ 3 * s.mS) &&
    (allBelow s.mS fun R =>
      -- B^l by repeated multiplication, where tieLeft takes radixPower l
      let x := mulE ka (hi.getD R zeroE)
      let xB := scaleE (fOfNat radb) x
      let xBB := scaleE (fOfNat radb) xB
      allFrom (fun i =>
        let v := if i % 3 == 0 then x else if i % 3 == 1 then xB else xBB
        !isZeroE v && L5.getD (c0 + i) zeroE == v &&
          L5.getD (c1 + i) zeroE == scaleNat v (2 ^ t2D0)) (min 3 (s.m - 3 * R)) (3 * R)) &&
    (allBelow s.k fun c =>
      let gam := sumAgain tl.cfF ((before + c) * tl.tau) xi2 tl.tau 0 zeroE
      (tl.gamX.getD mu #[]).getD c zeroE == gam && (tl.gamV.getD mu #[]).getD c zeroE == gam &&
        row.L.getD c zeroE == mulE (subE zeroE ka) gam)

/-- True if BZ meets the public conditions: 32 rows, bzColumns columns and three virtual rows, a
lookup of two calls, and weight vectors and points of the expected lengths. -/
def planesShapeHeld (tl : HTailF2) (F : Fork) (g : Forest.Heard) : Bool :=
  let B := F.trees.getD tl.ix.BZ {}
  let lKB := tl.f9.kT + tl.f9.cK
  B.rows.size == 3 && B.R == 32 && B.K == tl.bzColumns && tl.f9.NC == 2 && tl.f9.cK == 1 &&
    B.K == 2 ^ lKB &&
    (List.range 3).all (fun r =>
      (B.rows.getD r {}).coef.size == 32 && (B.rows.getD r {}).L.size == B.K) &&
    g.zb0.size == 5 + lKB && g.zb1.size == 5 + lKB

/-- True if the weights on BZ equal a second computation: the row weights of its three virtual rows,
and their column weights, each a claim's weight (t2fKappaByText) times the claim's factor times an
equality weight or a power of two. The factor of the first claim is not computed again: it is
bitFactor9, as linBits9 left it. jo: the index of the claim on the key vectors among the claims; the
three claims that read the planes follow it. -/
def planesWeightsHeld (tl : HTailF2) (F : Fork) (g : Forest.Heard) (jo : Nat) : Bool :=
  let B := F.trees.getD tl.ix.BZ {}
  let kp := t2fKappaByText F.theta (jo + 3)
  (B.rows.getD 2 {}).coef.all (· == oneE) &&
    ([0, 1].all fun e =>
      let row := B.rows.getD e {}
      let z := g.zb e
      let mk := mulE (t2fKappaByText F.theta (jo + 1 + e))
        (if e == 0 then tl.bitFactor9 else subE zeroE oneE)
      ((List.range 32).all fun r => row.coef.getD r zeroE == eqPlainF (z.extract 0 5) r) &&
        EqRun.all (z.extract 5 z.size) 0 B.K fun x e => row.L.getD x zeroE == mulE mk e) &&
    allBelow B.K fun x =>
      (B.rows.getD 2 {}).L.getD x zeroE == scaleNat kp (2 ^ (x % 32))

/-- True if the public numbers of the reads are fit for readWeightsAgain. L4: the column weights of
the reads' row of ZZ, one for each digit of each row of cells. Each table on one of the matrices, in
U1 or U3, has as many weights as a segment has rows, and its segments fill the matrix's rows of
cells. These tables have as many segments as objectsF has added reads (nX4Laid). The matrices' rows
of cells add up to mz. Any other table is passed over, as in the C++; objectsF has refused it
(internal-t2f-functional). -/
def readShapeHeld (tl : HTailF2) (L4 : Array E) : Bool :=
  let read := tl.funs.filter fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)
  L4.size == 2 * tl.mz &&
    (read.all fun Fn =>
      let m := (tl.mats.getD Fn.mat {}).m
      m != 0 && Fn.len != 0 && m % Fn.len == 0 && Fn.phi.size == Fn.len) &&
    read.foldl (fun q Fn => q + (tl.mats.getD Fn.mat {}).m / Fn.len) 0 == tl.nX4Laid &&
    (List.range tl.NM).foldl (fun n mu => n + (tl.mats.getD mu {}).m) 0 == tl.mz

/-- True if the column weights L4 of the reads' row of ZZ are those of the second computation. By
the C++ comment no value of theta makes this test fail: it compares two computations of one
polynomial in theta. -/
def readWeightsHeld (tl : HTailF2) (F : Fork) (L4 : Array E) : Bool :=
  let want := tl.readWeightsAgain F
  allBelow (2 * tl.mz) fun x => L4.getD x zeroE == want.getD x zeroE

end VerifiableInference.Desc.First.TailClaims
