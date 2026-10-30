-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/Req.lean: the tests on the plan's numbers of a request (the first chain's shape,
its codes and its layout of arrays) in the description's own text, for the block that opens the
first segment (Johnson/Desc/K1/First.lean: firstPlanOk). They read public numbers alone.

  stageFits, stageFitsAt, stagesFitFrom, stagesFit   the sizes of the last proximity test's stages.
  reqMessageFits, momentsFit, reqLinkFits, reqShapeFits   what the request's shape shows by itself.
  reqFits               what shape and codes show together.
  laidEven, laidBlockFits, laidMeets, noTwo, laidMatrixFits, laidFits   matrices laid in one table.
  reqArrayFits, laidHolds, reqMessageLaid, reqLayoutFits   the layout of a request's arrays.

Written after the program's stageOk, ioppStageOk, ioppStagesOk, ioppOk (OnBytes/Iop/Prox.lean),
reqMessageOk, reqMomentsOk, reqLinkOk, reqShapeOk, reqOk (OnBytes/Iop/Req.lean), laidAligned,
laidBlockOk, laidMeet, noPair, laidMatrixOk, laidOk, reqArrayOk, laidCovers, reqMessageLayoutOk and
reqLayoutOk (OnBytes/Iop/ReqRows.lean), clause by clause, in their order. For what these call in
turn stand: codeFits, twoPower, shapeSound (Johnson/Desc/Own/Lin.lean), padMade
(Johnson/Desc/Own/Send.lean), and "the mask code is no longer than the main code", written out.
What is taken from the hand-written program's files: the records with their fields, and plain
functions that cannot refuse: reqGroups, reqMostRows, reqMostClass, reqCarried, foldMaskColumns,
ceilLog2, mostLogN, zipT, Code.logEll. No function of these files that returns a Bool, an Option or
an Except is called.
That each says just what the program's says, at all arguments, is proved beside, in
Johnson/Desc/Own/ReqAgree.lean, which no block imports.
Beside it stands Johnson/Desc/K12/Sizes.lean: that kind's own writing of the stages' sizes, over
stages that hold their codes; no theorem ties the two.
LIMIT: whether these tests ask enough is not said here.
No theorem here. Nothing on soundness.

-/
import OnBytes.Iop.ReqRows
import Johnson.Desc.Own.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape IoppStage LaidBlock ReqArray ReqLayout)

/-- A stage by itself: not too many row variables, and no more mask rows than main rows. -/
def stageFits (s : IoppStage) : Bool := decide (s.k ≤ mostLogN) && decide (s.h ≤ s.k)

/-- One stage, given the stage before it (nothing for the first) and whether it is the last. -/
def stageFitsAt (codes : Codes) (answers : Nat) (before : Option IoppStage) (s : IoppStage)
    (last : Bool) : Bool :=
  match codes.base[s.code]?, codes.mask[s.maskCode]? with
  | some c, some zk =>
    codeFits c && codeFits zk && twoPower c.ell && twoPower zk.ell && decide (zk.logN ≤ c.logN) &&
    stageFits s &&
    (if last then s.k == 0
     else decide (1 ≤ s.k) && decide (foldMaskColumns s.k s.h ≤ zk.ell)) &&
    (match before with
      | none => true
      | some p =>
        let pc := codes.base.getD p.code default
        let pzk := codes.mask.getD p.maskCode default
        c.ell * 2 ^ s.k == pc.ell &&
        decide (2 * pzk.ell + pc.r + 2 * pzk.r + answers ≤ zk.ell * 2 ^ s.h) &&
        decide (answers ≤ zk.ell))
  | _, _ => false

/-- Consecutive stages, given the stage before the first of them, if any. -/
def stagesFitFrom (codes : Codes) (answers : Nat) : Option IoppStage → List IoppStage → Bool
  | _, [] => true
  | before, s :: rest =>
    stageFitsAt codes answers before s rest.isEmpty && stagesFitFrom codes answers (some s) rest

/-- The sizes of a proximity test's stages fit together. -/
def stagesFit (codes : Codes) (stages : List IoppStage) (answers : Nat) : Bool :=
  decide (2 ≤ stages.length) && decide (1 ≤ answers) && stagesFitFrom codes answers none stages

/-- One oracle message of a link. A kept message has main rows only and goes in its link's first
message. -/
def reqMessageFits (m : ReqMessage) : Bool :=
  decide (0 < m.shape.mainRows + m.shape.maskRows) &&
  decide (m.shape.mainRows ≤ reqMostRows) && decide (m.shape.maskRows ≤ reqMostRows) &&
  (m.shape.mainRows == 0 || m.shape.mainDeg == 1 || m.shape.mainDeg == 3) &&
  shapeSound m.shape &&
  (m.life == 0 || (m.shape.mainRows != 0 && m.shape.maskRows == 0 && m.moment == 0))

/-- The messages come by moment and no moment is empty. t: the moment of the message before. -/
def momentsFit : Nat → List ReqMessage → Bool
  | _, [] => true
  | t, m :: ms => (m.moment == t || m.moment == t + 1) && momentsFit m.moment ms

/-- One link by itself. -/
def reqLinkFits (l : ReqLink) : Bool :=
  (l.messages.head?.any fun m => m.moment == 0) && momentsFit 0 l.messages &&
  l.messages.all reqMessageFits

/-- What the request's shape shows by itself. -/
def reqShapeFits (s : ReqShape) : Bool :=
  let groups := reqGroups s
  let lastGroup := groups.getD s.link.length {}
  !s.link.isEmpty && decide (1 ≤ s.answers) &&
  (s.link.zipIdx.all fun x =>
    reqLinkFits x.1 && x.1.messages.all fun m =>
      m.shape.answers == s.answers &&
      (m.shape.mainRows == 0 || m.shape.code == s.code) &&
      (m.shape.maskRows == 0 || m.shape.maskCode == s.maskCode) &&
      decide (x.2 + m.life < s.link.length)) &&
  (s.link.head?.any fun l => l.messages.any fun m => m.shape.mainRows != 0 && m.life == 0) &&
  (s.atStart.all fun n =>
    n.shape.mainRows == 0 && n.shape.maskRows != 0 && decide (n.shape.maskRows ≤ reqMostRows) &&
    shapeSound n.shape && n.shape.answers == s.answers && decide (reqMostClass s < n.leafClass)) &&
  ((groups.toList.take s.link.length).all fun G => decide (G.k ≤ mostLogN)) &&
  decide (2 ≤ s.last.length) && s.last.all stageFits &&
  (s.last.head?.any fun t =>
    t.code == s.code && t.maskCode == s.maskCode && t.k == lastGroup.k && t.h == lastGroup.h)

/-- **What shape and codes show together.** -/
def reqFits (codes : Codes) (s : ReqShape) : Bool :=
  let groups := reqGroups s
  reqShapeFits s &&
  match codes.base[s.code]?, codes.mask[s.maskCode]? with
  | some c, some zk =>
    decide (s.answers < c.ell) && decide (s.answers < zk.ell) &&
    (s.atStart.all fun n =>
      match codes.mask[n.shape.maskCode]? with
      | some z => decide (n.shape.answers < z.ell)
      | none => false) &&
    ((List.range s.link.length).all fun l =>
      let G := groups.getD l {}
      decide (foldMaskColumns G.k G.h ≤ zk.ell) &&
      decide (reqCarried s c zk (groups.getD (l + 1) {}) ≤ c.ell)) &&
    stagesFit codes s.last s.answers
  | _, _ => false

/-- A first number is a multiple of its side; both are small. -/
def laidEven (first bits : Nat) : Bool :=
  decide (bits < 48) && decide (first < 2 ^ 48) && first % 2 ^ bits == 0

/-- A block is as large in the table as in its matrix, even on all four sides, and inside the
table. -/
def laidBlockFits (b : LaidBlock) (tableRowBits tablePlaceBits : Nat) : Bool :=
  b.rowBits + b.placeBits == b.bitsI + b.bitsC &&
  decide (b.rowBits ≤ tableRowBits) && decide (b.placeBits ≤ tablePlaceBits) &&
  laidEven b.firstI b.bitsI && laidEven b.firstC b.bitsC &&
  laidEven b.firstRow b.rowBits && laidEven b.firstPlace b.placeBits &&
  decide (b.firstRow < 2 ^ tableRowBits) && decide (b.firstPlace < 2 ^ tablePlaceBits)

/-- Two even stretches meet. -/
def laidMeets (a aBits b bBits : Nat) : Bool :=
  decide (a < b + 2 ^ bBits) && decide (b < a + 2 ^ aBits)

/-- No two members of the list are related by r. -/
def noTwo {α : Type} (r : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => (l.all fun b => !r a b) && noTwo r l

/-- One matrix is laid out lawfully by itself. -/
def laidMatrixFits (a : ReqArray) (tableRowBits tablePlaceBits : Nat) : Bool :=
  (a.blocks.all fun b =>
    laidBlockFits b tableRowBits tablePlaceBits &&
    decide (b.firstI + 2 ^ b.bitsI ≤ a.sizeI) && decide (b.firstC + 2 ^ b.bitsC ≤ a.sizeC)) &&
  noTwo (fun (x y : LaidBlock) =>
    laidMeets x.firstI x.bitsI y.firstI y.bitsI && laidMeets x.firstC x.bitsC y.firstC y.bitsC)
    a.blocks &&
  (a.blocks.map fun b => 2 ^ (b.bitsI + b.bitsC)).foldl (· + ·) 0 == a.sizeI * a.sizeC

/-- The matrices are laid out lawfully in one table. -/
def laidFits (matrices : List ReqArray) (tableRowBits tablePlaceBits : Nat) : Bool :=
  (matrices.all fun a => laidMatrixFits a tableRowBits tablePlaceBits) &&
  noTwo (fun (x y : LaidBlock) =>
    laidMeets x.firstRow x.rowBits y.firstRow y.rowBits &&
    laidMeets x.firstPlace x.placeBits y.firstPlace y.placeBits)
    (matrices.flatMap (·.blocks))

/-- What an array shows by itself. -/
def reqArrayFits (a : ReqArray) : Bool :=
  !a.name.isEmpty && a.sizeI != 0 && a.sizeC != 0 &&
  decide (a.sizeI < 2 ^ 48) && decide (a.sizeC < 2 ^ 48) && !a.blocks.isEmpty &&
  a.blocks.all fun b =>
    b.rowBits + b.placeBits == b.bitsI + b.bitsC &&
    laidEven b.firstI b.bitsI && laidEven b.firstC b.bitsC &&
    laidEven b.firstRow b.rowBits && laidEven b.firstPlace b.placeBits

/-- The block covers the entry `index` of a table with 2 ^ rowBits rows. -/
def laidHolds (b : LaidBlock) (rowBits index : Nat) : Bool :=
  let row := index % 2 ^ rowBits
  let place := index / 2 ^ rowBits
  decide (b.firstRow ≤ row) && decide (row < b.firstRow + 2 ^ b.rowBits) &&
  decide (b.firstPlace ≤ place) && decide (place < b.firstPlace + 2 ^ b.placeBits)

/-- The arrays that are in one oracle message fit it. -/
def reqMessageLaid (codes : Codes) (o : OracleShape) (inIt : List ReqArray) : Bool :=
  inIt.isEmpty ||
  (o.mainRows != 0 &&
   match codes.base[o.code]?, padMade codes o with
   | some c, some pad =>
     let rowBits := ceilLog2 o.mainRows
     laidFits inIt rowBits c.logEll &&
     (inIt.flatMap (·.blocks)).all fun b =>
       decide (b.firstRow + 2 ^ b.rowBits ≤ o.mainRows) &&
       pad.all fun p => p.part != .main || !laidHolds b rowBits p.index
   | _, _ => false)

/-- **The layout is lawful for the request's shape under the codes.** -/
def reqLayoutFits (codes : Codes) (s : ReqShape) (layout : ReqLayout) : Bool :=
  layout.link.length == s.link.length &&
  (zipT s.link layout.link).all fun x =>
    let messages := x.1.messages
    x.2.all reqArrayFits &&
    (x.2.all fun a => decide (a.message < messages.length)) &&
    noTwo (fun (a b : ReqArray) => a.name == b.name) x.2 &&
    messages.zipIdx.all fun m =>
      reqMessageLaid codes m.1.shape (x.2.filter fun a => a.message == m.2)

end VerifiableInference.Desc.Own
