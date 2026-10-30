-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3Asks.lean: THE LOOKUPS' TESTS ON PUBLIC DATA, WRITTEN OUT ONCE MORE OVER
LIGHT IMPORTS: what the laws on the kind "lookup" (K3) take as premises on the public record and on
the request's shape and layout, as functions to Bool that a verifier can run. Definitions alone; no
theorem; WITHOUT MATHLIB. NO SOUNDNESS IS CLAIMED. Nothing is evaluated in this file.

Why a second writing. The tests that the laws name (digB, K3CallerTests.lean; readsB,
K3CallerAttReads.lean, both in this folder) stand in files above Mathlib and call tests of the
library's older layers. What a verifier runs is to bring neither beneath it. So each definition
beneath them is written out here anew, in this file's own namespace, and calls none of those. That a
yes of a test here gives the law's own test: Johnson/Desc/First/Look/K3AsksLaw.lean.

OBJECT: no block's text: functions of the public record X and the data D beside it.
USER: Johnson/Desc/First/Look/K3AsksDoor.lean (digRow, readsRow), and through it the proof file's
  entry tests (Johnson/Desc/Laid/ProofAsks.lean).
LETTERS: X : Verify.Public; D : Sent.
Compiled with the whole library.


Main names, by section.
 1 `Sent`: the data beside the public record: the first chain's codes, the request's shape, the
   rows' layout, link by link the table of arrays. `messagesAt`, `lastMoment`, `sigList` (a link's
   own oracle messages' shapes up to a moment), `keptAt`, `bornAt`, `sigListCalls` (the kept ones,
   then the link's own of moment 0), `mainEll`, `maskEll` (the length of a shape's code).
 2 `meetB`, `blockB`, `blocksB`: an array's blocks cover it, without a meeting, inside a table.
   `arrB`, `maskB`: an array, the mask row, of a link's own. `msgIn`, `symArrB`, `maskCallsB`: the
   like where kept messages stand in front. `nMat`, `symRowsAt`, `colsAt`: the three numbers of a
   smallness test's record that symArrB is handed.
 3 The numbers of a lookup's record: `nOf` … `fT`; `shapeOkB`: what is asked of them.
 4 The digits' lookup against the smallness test's record: `piecesL` … `padsOkB`; `tailB`, `rowB`,
   `callB`, `portB`; `shapeB`: the four together.
 5 `digAddrB`, `digB`, `digAt`, `digRow`: THE DIGITS' ROW: at every link.
 6 `sampledB`, `keptSameB`, `seatsB`, `readsB`, `attLinks`, `readsRow`: THE ROW OF THE GUARDS OF
   attention's callers' reading: at every attention link.

Limits. A yes says what the clauses say and no more. The walks are as long as the records' numbers:
2 ^ (kT + cK) rows, 2 ^ rK trees, tau combinations at the digits. Where the record has no attention
link readsRow says yes over nothing.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.LookKind
import Johnson.Desc.First.Look.Laid
import OnBytes.Iop.ReqRows
import OnBytes.Iop.Req
import OnBytes.Params.DeriveReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Asks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Place P lookAt tlAt)

/-! ## 1 The data beside the public record -/

/-- **What the tests read beside Verify.Public**: plain data. -/
structure Sent where
  /-- the first chain's codes -/
  codes : Codes
  /-- the request's shape: link by link the oracle messages, by moment -/
  shape : Params.ReqShape
  /-- the layout: link by link the arrays, each with its message and its blocks -/
  layout : Params.ReqLayout
  /-- link by link, for each array of the sub-proof's list: the link that sent it, its name there -/
  arrayOf : Array (Array (Nat × String))

/-- Link i's oracle messages. -/
def messagesAt (D : Sent) (i : Nat) : List Params.ReqMessage :=
  ((D.shape.link[i]?).map (·.messages)).getD []

/-- The link's last moment. -/
def lastMoment (D : Sent) (i : Nat) : Nat := (((messagesAt D i).getLast?).map (·.moment)).getD 0

/-- The shapes of the link's own oracle messages sent up to a moment: a first stretch of the link's
list, so that a message keeps its number. -/
def sigList (D : Sent) (i mom : Nat) : List OracleShape :=
  ((messagesAt D i).takeWhile fun m => decide (m.moment ≤ mom)).map (·.shape)

/-- The kept oracle messages that are sent anew in link i's first prover's message. -/
def keptAt (D : Sent) (i : Nat) : List KeptTarget :=
  (((reqGroups D.shape)[i]?).map Params.keptOf).getD []

/-- For each of them, in their order: as what it was first sent: (link, number among its link's). -/
def bornAt (D : Sent) (i : Nat) : Array (Nat × Nat) :=
  (((reqGroups D.shape)[i]?).map (·.born)).getD #[]

/-- The shapes of the oracle messages that stand sent when the shift of link i's lookup on the calls
is drawn: the kept ones, then the link's own of moment 0. -/
def sigListCalls (D : Sent) (i : Nat) : List OracleShape :=
  (keptAt D i).map (·.shape) ++ sigList D i 0

/-- The length of the code of a shape's main rows. -/
def mainEll (cs : Codes) (s : OracleShape) : Nat := (cs.base.getD s.code default).ell

/-- The length of the code of its mask rows. -/
def maskEll (cs : Codes) (s : OracleShape) : Nat := (cs.mask.getD s.maskCode default).ell

/-! ## 2 An array's blocks in its message's table -/

/-- Two blocks hold a common element. -/
def meetB (x y : Params.LaidBlock) : Bool :=
  laidMeet x.firstI x.bitsI y.firstI y.bitsI && laidMeet x.firstC x.bitsC y.firstC y.bitsC

/-- One block: inside the array; as large in the table as in the array; inside the table. -/
def blockB (R K rows ell : Nat) (b : Params.LaidBlock) : Bool :=
  decide (b.firstI + 2 ^ b.bitsI ≤ R) && decide (b.firstC + 2 ^ b.bitsC ≤ K) &&
    decide (b.rowBits + b.placeBits = b.bitsI + b.bitsC) &&
    decide (b.firstRow + 2 ^ b.rowBits ≤ rows) && decide (b.firstPlace + 2 ^ b.placeBits ≤ ell)

/-- **The test on an array's blocks**: each is well placed; no two meet; together they have as many
elements as the array. -/
def blocksB (bs : List Params.LaidBlock) (R K rows ell : Nat) : Bool :=
  bs.all (blockB R K rows ell) && noPair meetB bs &&
    decide ((bs.map fun b => 2 ^ b.bitsI * 2 ^ b.bitsC).sum = R * K)

/-- **The test on array number t of link i's list**, where the link itself sent it. trees: the
link's arrays. l: the shapes of the link's messages. -/
def arrB (trees : Array HTree) (D : Sent) (l : List OracleShape) (i t : Nat) : Bool :=
  match trees[t]?, (D.arrayOf.getD i #[])[t]? with
  | some T, some bn =>
    bn.1 == i &&
      match reqArray D.layout i bn.2 with
      | some a =>
        match l[a.message]? with
        | some o => blocksB a.blocks T.R T.K o.mainRows (mainEll D.codes o)
        | none => false
      | none => false
  | _, _ => false

/-- **The test on the link's mask row**: it is there, and has room for upTo entries. -/
def maskB (D : Sent) (l : List OracleShape) (i upTo : Nat) : Bool :=
  match (messagesAt D i).findIdx? fun x => x.shape.maskRows != 0 with
  | some m =>
    match l[m]? with
    | some o => decide (0 < o.maskRows) && decide (upTo ≤ maskEll D.codes o)
    | none => false
  | none => false

/-- In which message of the list sigListCalls the array's message stands. b: the link that sent the
array. msg: the array's message's number among that link's. -/
def msgIn (D : Sent) (i b msg : Nat) : Option Nat :=
  if b == i then some ((keptAt D i).length + msg) else (bornAt D i).idxOf? (b, msg)

/-- **The test on array number t of link i's list**, of R rows and K columns, whoever sent it. -/
def symArrB (D : Sent) (l : List OracleShape) (i t R K : Nat) : Bool :=
  match (D.arrayOf.getD i #[])[t]? with
  | some bn =>
    match reqArray D.layout bn.1 bn.2 with
    | some a =>
      match msgIn D i bn.1 a.message with
      | some k =>
        match l[k]? with
        | some o => blocksB a.blocks R K o.mainRows (mainEll D.codes o)
        | none => false
      | none => false
    | none => false
  | none => false

/-- **The test on the mask row**, behind the kept messages. -/
def maskCallsB (D : Sent) (l : List OracleShape) (i upTo : Nat) : Bool :=
  match (messagesAt D i).findIdx? fun x => x.shape.maskRows != 0 with
  | some m =>
    match l[(keptAt D i).length + m]? with
    | some o => decide (0 < o.maskRows) && decide (upTo ≤ maskEll D.codes o)
    | none => false
  | none => false

/-- The number of matrices of a smallness test. -/
def nMat (tl : HTailF2) : Nat := tl.NM

/-- The rows of symbols of matrix mu: three cells a symbol. -/
def symRowsAt (tl : HTailF2) (mu : Nat) : Nat := ((tl.mats.getD mu {}).m + 2) / 3

/-- Its columns. -/
def colsAt (tl : HTailF2) (mu : Nat) : Nat := (tl.mats.getD mu {}).k

/-! ## 3 The numbers of a lookup's record -/

/-- Call c has 2 ^ n keys. -/
def nOf (h : Forest.Shape) (c : Nat) : Nat := ((h.calls[c]?).map (·.n)).getD 0
/-- Its table has 2 ^ k rows. -/
def kOf (h : Forest.Shape) (c : Nat) : Nat := ((h.calls[c]?).map (·.k)).getD 0
/-- The row that its padding keys point to. -/
def t0Of (h : Forest.Shape) (c : Nat) : Nat := ((h.calls[c]?).map (·.t0)).getD 0
/-- It has 2 ^ io trees. -/
def io (h : Forest.Shape) (c : Nat) : Nat := h.iota.getD c 0
/-- Its first tree. -/
def fst (h : Forest.Shape) (c : Nat) : Nat := h.first.getD c 0
/-- The call of tree y. -/
def co (h : Forest.Shape) (y : Nat) : Nat := h.callOf.getD y 0
/-- The call of the joint key X. -/
def fK (h : Forest.Shape) (X : Nat) : Nat := if X % 2 ^ h.rK < h.NT then co h (X % 2 ^ h.rK) else 0
/-- The call of the joint row Y. -/
def fT (h : Forest.Shape) (Y : Nat) : Nat := min (Y % 2 ^ h.cK) (h.NC - 1)

/-- **What is asked of the record's numbers**: there is a call; the calls and the trees have room in
their bits; each tree lies in its call's range; call 0's padding row is a row; each call's table has
room, its keys are its trees' keys, and its trees are numbered on from a multiple of their
number. -/
def shapeOkB (h : Forest.Shape) : Bool :=
  decide (1 ≤ h.NC ∧ h.NC ≤ 2 ^ h.cK ∧ h.NT ≤ 2 ^ h.rK ∧
  (∀ y < h.NT, co h y < h.NC ∧ fst h (co h y) ≤ y ∧ y < fst h (co h y) + 2 ^ io h (co h y)) ∧
  t0Of h 0 < 2 ^ kOf h 0 ∧
  ∀ c < h.NC, kOf h c ≤ h.kT ∧ nOf h c = io h c + h.dT ∧
    ∀ b < 2 ^ io h c, fst h c + b < h.NT ∧ co h (fst h c + b) = c ∧ (fst h c + b) % 2 ^ io h c = b)

/-! ## 4 The digits' lookup against the smallness test's record -/

/-- The call of the low digits (q = 0), of the high digits (else), with its pieces. -/
def zAt (tl : HTailF2) (q : Nat) : CallZ := if q == 0 then tl.z1 else tl.z2

/-- The pieces of call q. -/
def piecesL (tl : HTailF2) (q : Nat) : List Piece := (zAt tl q).pieces.toList

/-- The piece of call q whose rows hold the combination u. -/
def pieceAt (tl : HTailF2) (q u : Nat) : Option Piece :=
  (piecesL tl q).find? fun p => decide (p.r0 ≤ u) && decide (u < p.r0 + p.Rp)

/-- How many numbers below n meet a test. -/
def countBelow (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countBelow f n + if f n then 1 else 0

/-- The keys in the trees that hold only padding. -/
def emptyKeys (h : Forest.Shape) : Nat := (2 ^ h.rK - h.NT) * 2 ^ h.dT

/-- The public padding by call: (the padding row in the joint numbering, the number of padding
keys): those of the call's trees, and for call 0 those of the trees of padding alone. -/
def padsOf (h : Forest.Shape) : List (Nat × Nat) :=
  (List.range h.NC).map fun c =>
    (c + 2 ^ h.cK * t0Of h c,
      (((List.range h.NT).filter fun y => co h y = c).map fun y => h.pub.getD y 0).sum +
        if c = 0 then emptyKeys h else 0)

/-- How many padding keys hold the joint row u. -/
def padCnt (pads : List (Nat × Nat)) (u : Nat) : Nat :=
  (pads.map fun e => if e.1 = u then e.2 else 0).sum

/-- Every padding row is a row of the joint table; there are at most as many padding keys as
keys. -/
def padsOkB (n T : Nat) (pads : List (Nat × Nat)) : Bool :=
  pads.all (fun e => decide (e.1 < 2 ^ T)) && decide ((pads.map Prod.snd).sum ≤ 2 ^ n)

/-- Call c's padding row in the joint numbering. -/
def zRow (h : Forest.Shape) (c : Nat) : Nat := c + 2 ^ h.cK * t0Of h c

/-- The value of the joint row Y in its call's table. -/
def rowV (h : Forest.Shape) (Y : Nat) : Nat := Y / 2 ^ h.cK % 2 ^ kOf h (fT h Y)

/-- Row a of call c in the joint numbering. -/
def rowOf (h : Forest.Shape) (c a : Nat) : Nat := a * 2 ^ h.cK + c

/-- **The pieces against the record**: the record's numbers are lawful; two calls; each piece has
the half's columns, a range of places that is its rectangle's, inside its call and inside the
combinations; every combination lies in a piece; two pieces that meet in rows or in places agree in
their six numbers of place;
each call's keys are its padding and its digits. -/
def tailB (tl : HTailF2) : Bool :=
  shapeOkB tl.f9 && decide (tl.f9.NC = 2) &&
  decide (∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q, p.Cp = tl.mz ∧ p.Cp ≤ p.CP ∧ p.CP * p.Rp = 2 ^ p.b ∧
    p.off + 2 ^ p.b ≤ 2 ^ nOf tl.f9 q ∧ p.r0 + p.Rp ≤ tl.tau) &&
  decide (∀ q < tl.f9.NC, ∀ u < tl.tau, (pieceAt tl q u).isSome = true) &&
  decide (∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q, ∀ p' ∈ piecesL tl q,
    ((p.r0 < p'.r0 + p'.Rp ∧ p'.r0 < p.r0 + p.Rp) ∨
      (p.off < p'.off + 2 ^ p'.b ∧ p'.off < p.off + 2 ^ p.b)) →
    p.off = p'.off ∧ p.r0 = p'.r0 ∧ p.Rp = p'.Rp ∧ p.CP = p'.CP ∧ p.Cp = p'.Cp ∧ p.b = p'.b) &&
  decide (∀ c < tl.f9.NC,
    2 ^ tl.f9.dT * countBelow (fun y => decide (fK tl.f9 y = c)) (2 ^ tl.f9.rK) =
      padCnt (padsOf tl.f9) (zRow tl.f9 c) + tl.mz * tl.tau)

/-- **The joint rows**: each belongs to a call and holds a value of that call's table (q values for
call 0, H for call 1); a row that is no call's padding row has no padding key; and each value of
each table has its row. -/
def rowB (h : Forest.Shape) (q H : Nat) : Bool :=
  decide (∀ Y < 2 ^ (h.kT + h.cK), fT h Y < h.NC ∧ (fT h Y = 0 → rowV h Y < q) ∧
    (fT h Y = 1 → rowV h Y < H) ∧ ((∀ c < h.NC, zRow h c ≠ Y) → padCnt (padsOf h) Y = 0)) &&
  decide (∀ a < q, rowOf h 0 a < 2 ^ (h.kT + h.cK) ∧ fT h (rowOf h 0 a) = 0 ∧
    rowV h (rowOf h 0 a) = a) &&
  decide (∀ a < H, rowOf h 1 a < 2 ^ (h.kT + h.cK) ∧ fT h (rowOf h 1 a) = 1 ∧
    rowV h (rowOf h 1 a) = a)

/-- **The calls**: each call's padding row is a row of its own with the value 0; its number is below
pp; two calls have two padding rows; and the padding has room. -/
def callB (h : Forest.Shape) (pp : Nat) : Bool :=
  decide (∀ c < h.NC, (zRow h c < 2 ^ (h.kT + h.cK) ∧ fT h (zRow h c) = c ∧ rowV h (zRow h c) = 0) ∧
    c < pp ∧ (∀ c' < h.NC, zRow h c = zRow h c' → c = c')) &&
  padsOkB (h.dT + h.rK) (h.kT + h.cK) (padsOf h)

/-- x is a power of two. -/
def pow2B (x : Nat) : Bool := x != 0 && 2 ^ Nat.log2 x == x

/-- The least l with n at most 2 ^ l. -/
def logUp (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- One piece of a call with 2 ^ n keys is well placed. -/
def pieceB (n : Nat) (p : Piece) : Bool :=
  p.Rp != 0 && p.Cp != 0 && decide (p.a ≤ 40) && 2 ^ p.a == p.Rp && p.r0 % p.Rp == 0 &&
    decide (p.Cp ≤ p.CP) && pow2B p.CP && p.b == p.a + logUp p.CP && decide (p.b ≤ n) &&
    p.off % 2 ^ p.b == 0 && decide (p.off + 2 ^ p.b ≤ 2 ^ n)

/-- The value of row t of a call's table. -/
def tauAt (c : Call) (t : Nat) : UInt64 :=
  match c.tau with
  | none => t.toUInt64
  | some a => a.getD t 0

/-- **The record of the lookup against the two calls of the smallness test**: each piece is well
placed, on the digits' array, in its call's half; the record's call has the test's call's numbers,
no table of its own, the padding row 0; the calls fill their bits; the tables have 2 ^ 10 and 2 ^ 8
rows; row t holds t. -/
def portB (tl : HTailF2) : Bool :=
  decide (∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q,
    pieceB (zAt tl q).call.n p = true ∧ p.tree = tl.ix.ZZ ∧ p.c0 = q * tl.mz) &&
  decide (∀ q < tl.f9.NC, nOf tl.f9 q = (zAt tl q).call.n ∧ kOf tl.f9 q = (zAt tl q).call.k ∧
    t0Of tl.f9 q = (zAt tl q).call.t0 ∧ (zAt tl q).call.tau.isNone = true ∧
    (tl.f9.calls.getD q {}).tau.isNone = true ∧ t0Of tl.f9 q = 0) &&
  decide (2 ^ tl.f9.cK = tl.f9.NC) && decide (kOf tl.f9 0 = 10 ∧ kOf tl.f9 1 = 8) &&
  decide (∀ q < tl.f9.NC, ∀ t < 2 ^ kOf tl.f9 q, (tauAt (tl.f9.calls.getD q {}) t).toNat = t)

/-- **THE WHOLE TEST ON THE SMALLNESS TEST's RECORD.** pp: the field's characteristic. -/
def shapeB (tl : HTailF2) (pp : Nat) : Bool :=
  tailB tl && rowB tl.f9 (2 ^ 10) (2 ^ 8) && callB tl.f9 pp && portB tl

/-! ## 5 The digits' row -/

/-- **The test on the addresses that the digits' lookup reads.** l: the shapes of the link's own
messages. The digits' array has at least tau rows and 2 mz columns; the array of the counts' bits
has room for them; both are the link's own, laid, their blocks inside their message's table; the
lookup's mask entries lie below the number of slots and in the link's mask row. -/
def digAddrB (x : Place) (tl : HTailF2) (D : Sent) (l : List OracleShape) : Bool :=
  (match x.base.trees[tl.ix.ZZ]? with
    | some T => decide (tl.tau ≤ T.R) && decide (tl.mz + tl.mz ≤ T.K)
    | none => false) &&
  (match x.base.trees[tl.ix.BZ]? with
    | some T => decide (2 ^ (tl.f9.kT + tl.f9.cK) ≤ T.K) &&
        decide (2 ^ tl.f9.kT * 2 ^ tl.f9.cK * 2 ^ 5 ≤ 2 ^ (tl.f9.kT + tl.f9.cK) * T.R)
    | none => false) &&
  arrB x.base.trees D l x.link tl.ix.ZZ && arrB x.base.trees D l x.link tl.ix.BZ &&
  decide (x.F.next + Forest.elems tl.f9 ≤ x.ns) &&
  maskB D l x.link (x.F.next + Forest.elems tl.f9)

/-- The field's characteristic: 2 ^ 64 - 2 ^ 32 + 1. -/
def prime : Nat := 18446744069414584321

/-- **THE DIGITS' ONE TEST AT A LINK**: the planner makes the lookup's rounds; the test on the
smallness test's record; every message of the link has one answer to its sample; the addresses. -/
def digB (set : Params.Setting) (x : Place) (tl : HTailF2) (D : Sent) : Bool :=
  (P.ofPlace set true x).entries.isSome && shapeB tl prime &&
    (sigList D x.link (lastMoment D x.link)).all (fun o => o.answers == 1) &&
    digAddrB x tl D (sigList D x.link (lastMoment D x.link))

/-- Link i's place and the record of its smallness test, the lookup's record laid anew as the one
that the kind's own parameters make. -/
def digAt (X : Verify.Public) (i : Nat) : Option (Place × HTailF2) :=
  (lookAt X i true).bind fun x => (tlAt X i).bind fun tl =>
    (P.ofPlace (Params.settingOf X.P.frame) true x).shape.map fun h => (x, { tl with f9 := h })

/-- The number of links of the first chain. -/
def linksOf (X : Verify.Public) : Nat := (if X.p4 then 2 else 1) * X.NGr + 1

/-- **THE DIGITS' ROW**: at every link the place is there and the test says yes. -/
def digRow (X : Verify.Public) (D : Sent) : Bool :=
  (List.range (linksOf X)).all fun i =>
    (digAt X i).any fun xt => digB (Params.settingOf X.P.frame) xt.1 xt.2 D

/-! ## 6 The row of the guards of attention's callers' reading -/

/-- Every message that stands sent has one answer to its sample. -/
def sampledB (x : Place) (D : Sent) : Bool :=
  (sigListCalls D x.link).all fun o => o.answers == 1

/-- A kept message has the shape of the message whose rows it took. -/
def keptSameB (x : Place) (D : Sent) : Bool :=
  (List.range (keptAt D x.link).length).all fun k =>
    decide ((((messagesAt D ((bornAt D x.link).getD k (0, 0)).1)[((bornAt D x.link).getD k
      (0, 0)).2]?).map (·.shape)) = ((keptAt D x.link)[k]?).map (·.shape))

/-- Every symbol of every matrix of the list, and every mask entry of the lookup, has a seat. -/
def seatsB (x : Place) (tl : HTailF2) (D : Sent) : Bool :=
  ((List.range (nMat tl)).all fun mu =>
    symArrB D (sigListCalls D x.link) x.link (tl.gtTree.getD mu 0) (symRowsAt tl mu)
      (colsAt tl mu)) &&
    maskCallsB D (sigListCalls D x.link) x.link (x.F.next + Forest.elems x.fs)

/-- **THE THREE GUARDS AT A LINK.** -/
def readsB (x : Place) (tl : HTailF2) (D : Sent) : Bool :=
  sampledB x D && keptSameB x D && seatsB x tl D

/-- The attention links' numbers. -/
def attLinks (X : Verify.Public) : List Nat :=
  (List.range ((if X.p4 then 2 else 1) * X.NGr)).filter fun i => i % (if X.p4 then 2 else 1) != 0

/-- **THE ROW OF THE GUARDS**: at every attention link. -/
def readsRow (X : Verify.Public) (D : Sent) : Bool :=
  (attLinks X).all fun i =>
    (lookAt X i false).any fun x => (tlAt X i).any fun tl => readsB x tl D

end VerifiableInference.Desc.K3Asks
