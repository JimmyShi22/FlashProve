-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/Lin.lean: the tests that the shared chain's block "LIN point" asks, on the plan and
in its decision, of the codes and of the public shape of the linear part, as a named part of the
description. It is not their only caller: the linear claim's first part calls linFits too.

THESE ARE THE HAND-WRITTEN PROGRAM's TESTS TAKEN OVER TOKEN FOR TOKEN UNDER NEW NAMES:
Codes.lengthsOk and powerOfTwo (OnBytes/Iop/Ground.lean); linOk and all that it asks: LinShape.ok,
splitMessageOk, vectorMessageOk (OnBytes/Iop/Lin.lean), foldeqOk, FoldeqShape.ok, IndexShape.ok
(OnBytes/Iop/Foldeq.lean), Code.ok, shapeFaultless (OnBytes/Iop/Ground.lean). THEY ADD NO SECOND,
INDEPENDENT EYE: what they buy is that the description's text says by itself what it asks, and calls
none of these tests. ONE THING IS NOT TAKEN OVER AS IT WAS: where the program asks "n ≤ vectorRoom
…", a number that is 0 in three cases and calls the maker Send.pad, these texts ask "n ≤ roomOf …"
(Johnson/Desc/Own/Room.lean), whose three cases are a named test (roomCan) and whose meaning is
stated and proved (RoomMeans.lean: le_roomOf).

  twoPower n         n is a power of two.
  lengthsFit c       every code's message length, of main rows and of mask rows, is a power of two.
  shapeSound s       a message's shape by itself: it has rows; it names a code for the rows that it
                     has; its main rows are over one of the two fields.
  codeFits c         three numbers describe a code: 1 ≤ logN ≤ mostLogN (the program's number: 60);
                     1 ≤ ell; ell, r and the dimension (the program's Code.dim: ell + r) are at
                     most 2 ^ logN; the dimension is at most 2 ^ min logN 32.
  indexFits s        a stored table's shape: its code fits; at most 40 row bits; the pads are fewer
                     than the message's entries; the salt's length is one that the format allows.
  foldeqShapeFits S    the fold's shape by itself: the table's shape fits; o_u's shape is sound, has
                     main rows over the large field and a sample; a column is drawn.
  foldFits codes S   with the codes: o_u's code is there, and the folded row has room in o_u.
  splitMessageFits o maskCode     a split's message: mask rows alone, sampled, under that mask code.
  vectorMessageFits o             o_omega or W: sound; main rows over the large field; sampled.
  linShapeFits S     the linear part's shape by itself: fifteen clauses, in the program's order.
  linFits codes S    with the codes: the four codes that it names are there; the matrix's rows have
                     room in o_omega and 2 ^ kCol entries in W.
What is still called of the program's files. Functions that return a number or a record's field:
ceilLog2, noId, mostLogN, Code.dim, IndexShape.pads and plain, FoldeqShape.entries, LinShape.kRow.
plain is a difference cut off at 0 (ell - pads): the clause that reads it is to be read as written
only because indexFits asks pads < ell, which stands in the same conjunction. TWO THAT RETURN yes OR
no: LinShape.sharedSplitNeeded and ownSplitNeeded: each compares two of the shape's code numbers and
says which of two cases the shape is; nothing is refused at them. Of the format's files, one test:
Fmt.saltLenOK.
That each says just what the program's says, at all arguments, is proved beside, in
Johnson/Desc/Own/LinAgree.lean, which no block imports.
LIMIT: whether these tests ask enough is not said here.
No theorem here. Nothing on soundness.

-/
import OnBytes.Iop.Lin
import Johnson.Desc.Own.Room

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Params

/-- n is a power of two. -/
def twoPower (n : Nat) : Bool := n != 0 && 2 ^ ceilLog2 n == n

/-- Every code's message length is a power of two. -/
def lengthsFit (c : Codes) : Bool :=
  c.base.all (fun x => twoPower x.ell) && c.mask.all fun x => twoPower x.ell

/-- A message's shape by itself. -/
def shapeSound (s : OracleShape) : Bool :=
  !(s.mainRows == 0 && s.maskRows == 0) && !(s.mainRows != 0 && s.code == noId) &&
    !(s.maskRows != 0 && s.maskCode == noId) &&
    !(s.mainRows != 0 && s.mainDeg != 1 && s.mainDeg != 3)

/-- Three numbers describe a code. -/
def codeFits (c : Code) : Bool :=
  decide (1 ≤ c.logN) && decide (c.logN ≤ mostLogN) && decide (1 ≤ c.ell) &&
    decide (c.ell ≤ 2 ^ c.logN) && decide (c.r ≤ 2 ^ c.logN) && decide (c.dim ≤ 2 ^ c.logN) &&
    decide (c.dim ≤ 2 ^ min c.logN 32)

/-- A stored table's shape. -/
def indexFits (s : IndexShape) : Bool :=
  codeFits s.code && decide (s.v ≤ 40) && decide (s.pads < s.code.ell) && Fmt.saltLenOK s.saltBytes

/-- The fold's shape by itself. -/
def foldeqShapeFits (S : FoldeqShape) : Bool :=
  indexFits S.index && shapeSound S.u && decide (0 < S.u.mainRows) && S.u.mainDeg == 3 &&
    decide (1 ≤ S.u.answers) && decide (1 ≤ S.columns)

/-- The fold's shape with the codes that it names. -/
def foldFits (codes : Codes) (S : FoldeqShape) : Bool :=
  foldeqShapeFits S && decide (S.u.code < codes.base.size) &&
    decide (S.entries ≤ roomOf codes S.u S.rowsHigh)

/-- A split's message: sampled, of mask rows only, under its groups' mask code. -/
def splitMessageFits (o : OracleShape) (maskCode : Nat) : Bool :=
  o.mainRows == 0 && o.maskRows != 0 && decide (1 ≤ o.answers) && o.maskCode == maskCode

/-- o_omega or W: main rows over the large field, sampled. -/
def vectorMessageFits (o : OracleShape) : Bool :=
  shapeSound o && o.mainRows != 0 && o.mainDeg == 3 && decide (1 ≤ o.answers)

/-- The linear part's shape by itself. -/
def linShapeFits (S : LinShape) : Bool :=
  foldeqShapeFits S.fold &&
  decide (1 ≤ S.matrixRows) && decide (S.kLo ≤ 30) && decide (S.kRow ≤ 30) &&
  decide (S.kCol ≤ 60) &&
  decide (S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain) &&
  vectorMessageFits S.omega && vectorMessageFits S.w &&
  (S.fold.u.maskRows == 0 || S.fold.u.maskCode == S.sharedMaskCode) &&
  (S.w.maskRows == 0 || S.w.maskCode == S.ownMaskCode) &&
  -- o_omega joins groups with different mask codes, so it must not have mask rows
  S.omega.maskRows == 0 &&
  -- messages that are opened at different lists of positions share no leaf
  (!S.sharedSplitNeeded || S.omegaLeafClass != S.sharedSplitLeafClass) &&
  (!S.ownSplitNeeded || S.wLeafClass != S.ownSplitLeafClass) &&
  (!S.sharedSplitNeeded || splitMessageFits S.sharedSplit S.sharedMaskCode) &&
  (!S.ownSplitNeeded || splitMessageFits S.ownSplit S.ownMaskCode)

/-- The linear part's shape with the codes that it names. -/
def linFits (codes : Codes) (S : LinShape) : Bool :=
  linShapeFits S && foldFits codes S.fold &&
  decide (S.omega.code < codes.base.size) && decide (S.w.code < codes.base.size) &&
  decide (S.sharedMaskCode < codes.mask.size) && decide (S.ownMaskCode < codes.mask.size) &&
  decide (S.matrixRows ≤ roomOf codes S.omega S.omegaRowsHigh) &&
  decide (2 ^ S.kCol ≤ roomOf codes S.w S.wRowsHigh)

end VerifiableInference.Desc.Own
