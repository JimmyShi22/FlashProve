-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Foldeq.lean: from a committed table to one fresh oracle message, on the verifier's side.
C++ counterpart: blocks/iop/foldeq.h.
Ground.lean explains chain, plan, group and strict reader; Send.lean explains sample. Numbers like
R4.8 name rules of the format page, docs/format/FORMAT.md.

From, to. A committer has encoded 2^v rows over the base field F under one code and has published
the root of a tree over the columns. The table outlives a proof and is not one of its oracle
messages. The verifier has drawn gamma: one coordinate in the extension field E for each bit of a
row's number. The fold is the sum of the rows with the weights eq(r, gamma). Encoding is linear, so
the fold of the code words is the code word, over E, of the folded messages and the folded random
tails. Claims about the fold become equations on a fresh oracle message, called G_u here, which
holds the whole folded row: message entries, pads and random tail.

Messages. SEND of G_u (root, seeds, answers). Then the verifier draws positions of the table, and
the prover opens the table's columns there.

Rows that come out. Such a row (Row in Ground.lean) is a linear equation on what oracle messages
hold, not a row of the table. All are on G_u and are left to the proximity test on its group:
 - with a record, one plain row for each of its seeds: all rows' answers under that seed, folded;
 - for each draw x, one generator row: what G_u holds, encoded under the table's code, has at x the
   value to which the opened column folds.

The record. A table may come with a record: for each row, answers to an out-of-domain sample whose
seeds are a hash of the table's name (R4.8). The name is the root, the digest of the public files
and the six numbers of the shape (R4.10). The answers are part of the key and of every later
statement.
Why a record. Beyond half the minimum distance of a code
a word can be close to several tables,
and a prover could speak for another one in each proof.
A record is meant to settle which: "the table" is then the near table that agrees with the record.
Its equations are linear in the rows, so at gamma they fold into one row on G_u for each seed.
Pads. With a record, each row's message ends in pads: for each answer three entries over F, one
element of E in the basis 1, X, X^2 (R13.8). In their own answer they have the coefficients
beta (1, X, X^2), beta being the seed's factor, and in the others 0. The committer fills them at
random, to hide the row from its answers: the protocol's pages give them this purpose. This file
follows the verifier's steps and claims nothing about hiding. G_u's own sample has another pad,
which is SEND's.

Main definitions: vectorLay, vectorRoom, IndexShape.ok, FoldeqShape.ok, foldeqOk, TableKey,
FoldedRow, foldeqRecordRow, foldeqColumnRow, foldeqJoined, foldeqColumnsVerify, foldeqVerify.

What this file does not do.
 - The strict reader, not this file, tests that the opened columns lead to the table's root.
 - The record's seeds are a field of TableKey, since a block (Blk) calls no hash. Whoever makes a
   TableKey must compute them from the table's name, as tableKey does (OnBytes/Entry/Table.lean).
 - foldeq_verify (foldeq.h) has the table compared with the one for which the plan's numbers were
   computed; foldeq_columns_verify compares the distances of its one-time test with the run's. Here
   neither is done: the number of draws is compared only with the shape's columns. A number computed
   for a table of lower rate is too small for the table that is read, and nothing here notices.
 - gamma must be drawn after root and record are fixed: the protocol's argument is that a prover
   that knows gamma first could fit the answers to any table near the committed word. foldeqVerify
   does not test this: its caller must draw gamma on a chain whose statement holds root and record.
 - A TableKey is an ordinary structure. Whether the committer's one-time test on the table has ever
   passed, and at which distances, is the matter of whoever made the key.
 - No theorem is stated here.
-/
import OnBytes.Iop.Send
import OnBytes.Params.Items

namespace OnBytes

open Params (IndexShape FoldeqShape)

/-! ## How a vector is laid out in an oracle message -/

/-- How a vector is laid out in the main table of an oracle message of this shape. -/
def vectorLay (codes : Codes) (s : OracleShape) (rowsHigh : Bool) : VectorLay :=
  ⟨ceilLog2 s.mainRows, (codes.base.getD s.code default).logEll, rowsHigh⟩

/-- The number of entries, from entry 0 on, that are in real rows and before every place of the pad
of the oracle message's sample. It is 0 in three cases: rowsHigh is false and the number of rows is
not a power of two (that layout uses all 2^rowBits rows from the first entries on); the table has
more than 60 index bits; a row is too short for the pad. -/
def vectorRoom (codes : Codes) (s : OracleShape) (rowsHigh : Bool) : Nat :=
  let lay := vectorLay codes s rowsHigh
  if !rowsHigh && s.mainRows != 2 ^ lay.rowBits then 0
  else if 60 < lay.bits then 0
  else
    let room := s.mainRows * 2 ^ lay.placeBits
    if s.answers == 0 then room
    else
      match Send.pad codes s with
      | none => 0
      | some places =>
        places.foldl (fun m p => if p.part == .main then min m (lay.entryAt p.index) else m) room

/-! ## The committed table: what is public -/

namespace Params.IndexShape

/-- The number of rows. -/
def rows (s : IndexShape) : Nat := 2 ^ s.v

/-- The number of entries at the end of a row's message that are pads. -/
def pads (s : IndexShape) : Nat := 3 * s.answers

/-- The number of entries before the pads. -/
def plain (s : IndexShape) : Nat := s.code.ell - s.pads

/-- The place, in a row's message, of coordinate t of the pad of an answer. -/
def padPlace (s : IndexShape) (answer t : Nat) : Nat := s.plain + 3 * answer + t

/-- The number of coordinates of the point of the record's sample. -/
def cubeBits (s : IndexShape) : Nat := s.code.logEll

/-- The conditions on a table's shape. -/
def ok (s : IndexShape) : Bool :=
  s.code.ok && decide (s.v ≤ 40) && decide (s.pads < s.code.ell) && Fmt.saltLenOK s.saltBytes

/-- The shape of the tree over the columns: 2^v symbols of F in a leaf. The format gives the tree
of each stored table the number 0. -/
def tree (s : IndexShape) : Fmt.Shape :=
  { a := s.code.logN, W := s.rows, stored := true, tree := 0 }

end Params.IndexShape

/-- What a verifier knows of a table besides its shape. -/
structure TableKey where
  /-- the number, from 0, of the item of the chain's statement that holds the table's root -/
  item : Nat := 0
  /-- entry r * answers + i is the answer of row r under seed i -/
  record : Array E := #[]
  /-- the record's seeds, one for each answer; all rows share them. They are a function of the
  table's name -/
  seeds : List SampleSeed := []
  deriving Inhabited

/-- The key's sizes fit the shape s: the record has s.rows * s.answers entries, there are s.answers
seeds, and each seed's point has s.cubeBits coordinates. -/
def TableKey.fits (key : TableKey) (s : IndexShape) : Bool :=
  key.record.size == s.rows * s.answers && key.seeds.length == s.answers &&
    key.seeds.all fun x => x.z.length == s.cubeBits

/-! ## The folded row inside G_u, and the rows on it -/

namespace Params.FoldeqShape

/-- Where the folded tail begins in G_u's message, read as a vector: at the first multiple of
2^logR, the least power of two that holds the tail, at or after the end of the folded message. So
the bits of an index inside the tail are the low bits of the entry's number. -/
def tailFirst (S : FoldeqShape) : Nat :=
  let step := 2 ^ S.index.code.logR
  (S.index.code.ell + step - 1) / step * step

/-- The number of entries of G_u's message, from entry 0 on, that the folded row takes: the message,
the gap up to tailFirst, and the tail. -/
def entries (S : FoldeqShape) : Nat := S.tailFirst + S.index.code.r

/-- By itself: index is ok, u is faultless with main rows over E and a sample, a column is drawn. -/
def ok (S : FoldeqShape) : Bool :=
  S.index.ok && shapeFaultless S.u && decide (0 < S.u.mainRows) && S.u.mainDeg == 3 &&
    decide (1 ≤ S.u.answers) && decide (1 ≤ S.columns)

end Params.FoldeqShape

/-- The conditions on the shape with the codes that it names. -/
def foldeqOk (codes : Codes) (S : FoldeqShape) : Bool :=
  S.ok && decide (S.u.code < codes.base.size) &&
    decide (S.entries ≤ vectorRoom codes S.u S.rowsHigh)

/-- Where the folded row is: the oracle message, and how the row is laid out in its main table. -/
structure FoldedRow where
  /-- the number of G_u -/
  oracle : Nat := noId
  /-- how the folded row is laid out in it -/
  lay : VectorLay := {}
  deriving Inhabited

/-- The weights of the table's rows: entry r is eq(r, gamma), for r below 2^(length of gamma). -/
def foldeqWeights (gamma : List E) : Array E := eqTable gamma

/-- The value of the fold at a position, from the column there. -/
def foldeqSymbol (eqGamma : Array E) (column : Array F) : E :=
  (List.range eqGamma.size).foldl
    (fun s r => maddS s (column.getD r 0) (eqGamma.getD r zeroE)) zeroE

/-- Adds tensors on a vector's entries to a row, as terms on the main table of the oracle message o
that holds the vector. -/
def addLaid (row : Row) (o : Nat) (lay : VectorLay) (l : List Tensor) : Row :=
  l.foldl (fun r t => r.add o .main (lay.onTable t)) row

/-- Adds tensors on the folded row's entries to a row, as terms on G_u's main table. -/
def FoldedRow.addAll (u : FoldedRow) (row : Row) (l : List Tensor) : Row :=
  addLaid row u.oracle u.lay l

/-- Closes the named round and returns the elements drawn in it. Fails unless there are count. -/
def drawPoint (round : String) (count : Nat) : Blk (List E) := do
  let x ← Blk.closeElems round
  Blk.must (x.length == count)
  pure x

/-- The record's answer number i, folded: a row on G_u. On the folded message it has eq(., seed.z)
before the pads, beta (1, X, X^2) on the pads of answer i, and 0 on those of the other answers. -/
def foldeqRecordRow (S : FoldeqShape) (seed : SampleSeed) (record : Array E) (i : Nat)
    (eqGamma : Array E) (u : FoldedRow) : Option Row := do
  let s := S.index
  guard (seed.z.length == s.cubeBits && record.size == s.rows * s.answers)
  let under := Tensor.eq seed.z
  let cut ← tensorBelow under 0 s.cubeBits s.code.ell
  let onPads := (List.range s.answers).foldl
    (fun (r : Row) a =>
      (List.range 3).foldl
        (fun (r : Row) t =>
          let p := s.padPlace a t
          r.addUnit u.oracle .main (u.lay.index p)
            (subE (if a == i then mulE seed.beta (thetaE t) else zeroE) (under.entry p))) r)
    (u.addAll {} cut)
  pure { onPads with
    target := (List.range s.rows).foldl
      (fun t r => maddE t (eqGamma.getD r zeroE) (record.getD (r * s.answers + i) zeroE)) zeroE }

/-- "The code word of the folded row has the value y at position x of the table's code": a row on
G_u. -/
def foldeqColumnRow (S : FoldeqShape) (x : Nat) (y : E) (u : FoldedRow) : Option Row := do
  let c := S.index.code
  let g := generatorAt c x
  let onMessage ←
    tensorBelow (Tensor.product (g.f.take c.logEll) (ofF g.messageScale)) 0 c.logEll c.ell
  let onTail ←
    if c.r == 0 then pure []
    else tensorBelow (Tensor.product (g.f.take c.logR) (ofF g.tailScale)) 0 c.logR c.r
  let placed := onTail.map fun t =>
    t.insertChoice c.logR (u.lay.bits - c.logR) (S.tailFirst / 2 ^ c.logR)
  pure { u.addAll (u.addAll {} onMessage) placed with kind := .generator, target := y }

/-! ## The block

The block is written in pieces (foldeqRequire, foldeqJoined, foldeqColumnsVerify) for a caller that
sends several folded rows in one prover's message or draws the columns of several tables in one
round (OnBytes/Iop/Link.lean). foldeqVerify runs the pieces in their order for one table, with SEND
and the round of positions between them. -/

/-- To be called once G_u is sent and its sample answered: G_u joins the group g and the record's
rows go there. Blk.join fails unless G_u is sampled and g has the code of G_u's main rows. -/
def foldeqJoined (S : FoldeqShape) (key : TableKey) (eqGamma : Array E) (oracle g : Nat) :
    Blk FoldedRow := do
  let st ← Blk.statement
  let u : FoldedRow := ⟨oracle, vectorLay st.codes S.u S.rowsHigh⟩
  Blk.join g oracle
  Blk.addRowsOnView g fun _ =>
    key.seeds.zipIdx.mapM fun x => foldeqRecordRow S x.1 key.record x.2 eqGamma u
  pure u

/-- Reads the table's opened columns and adds to group g one row on G_u for each of the table's
draws. pos: all positions of the round that was closed last. The table's draws are those from number
first on, as many as the shape says. The caller must have closed that round after G_u's answers;
this is not tested here. -/
def foldeqColumnsVerify (key : TableKey) (S : FoldeqShape) (eqGamma : Array E) (pos : Positions)
    (first : Nat) (u : FoldedRow) (g : Nat) : Blk Unit := do
  let s := S.index
  Blk.must (decide (first + S.columns ≤ pos.draws.size) && pos.logN == s.code.logN)
  let (list, columns) ← Blk.readStored ⟨s.tree, s.saltBytes, key.item, first, S.columns⟩ pos
  let draws := (pos.draws.toList.drop first).take S.columns
  let rows ← Blk.getOnView [] fun _ => draws.mapM fun x => do
    let i ← list.idxOf? x
    foldeqColumnRow S x (foldeqSymbol eqGamma (← columns[i]?)) u
  Blk.addRowsOnView g fun _ => some rows
  if let some row := rows.head? then
    Blk.note "FOLDEQ: (Col_1)'s target" row.target
    Blk.noteBy "FOLDEQ: (Col_1) on G_u<0>" fun _ =>
      row.coefficient u.oracle .main (u.lay.index 0)
    if 0 < s.code.r then
      Blk.noteBy "FOLDEQ: (Col_1) on G_u<B>" fun _ =>
        row.coefficient u.oracle .main (u.lay.index S.tailFirst)

/-- Before anything is read: the public conditions on shape and key, and no seed has the factor 0
on its pad. -/
def foldeqRequire (key : TableKey) (S : FoldeqShape) : Blk Unit := do
  let st ← Blk.statement
  Blk.must (foldeqOk st.codes S)
  Blk.must (key.fits S.index)
  Blk.test (key.seeds.all fun x => !isZeroE x.beta)

/-- The block for one table. The caller must have drawn gamma on a chain whose statement holds the
table's root and record; this is not tested here (see the file's head). g is a group of G_u's code;
G_u joins it and the rows go there. others: further oracle messages of G_u's prover message. Returns
where the folded row is, and the numbers of the others. -/
def foldeqVerify (key : TableKey) (S : FoldeqShape) (gamma : List E) (g : Nat)
    (others : Array OracleNotice := #[]) : Blk (FoldedRow × Array Nat) := do
  foldeqRequire key S
  Blk.must (gamma.length == S.index.v)
  let eqGamma ← Blk.onView #[] fun _ => foldeqWeights gamma
  let ids ← sendVerify (#[(⟨S.u, S.leafClass⟩ : OracleNotice)] ++ others)
  let u ← foldeqJoined S key eqGamma (ids.getD 0 noId) g
  Blk.note "FOLDEQ: e_0" (eqGamma.getD 0 zeroE)
  if let some seed := key.seeds.head? then
    Blk.noteBy "FOLDEQ: (Rec_0)'s target" fun _ =>
      ((foldeqRecordRow S seed key.record 0 eqGamma u).map (·.target)).getD zeroE
  let drawn ← Blk.closePositions "LOC" S.index.code.logN
  Blk.must (drawn.2.isEmpty && drawn.1.draws.size == S.columns)
  foldeqColumnsVerify key S eqGamma drawn.1 0 u g
  pure (u, ids.extract 1 ids.size)

end OnBytes
