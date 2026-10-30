-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Link.lean: the link, the protocol of an entry file. An entry file holds a further stored
copy's root, its record and the link's chain (docs/format/FORMAT.md, R13.3). This link is not
the link of OnBytes/Iop/Req.lean, which is a part of a request's computation.
C++ counterpart: blocks/iop/link.h.

A committer lets a stored table (OnBytes/Iop/Foldeq.lean) be opened at a bounded number of columns
only: the head of blocks/iop/link.h gives the table's random tails the purpose of hiding so many
opened columns. So the committer makes further stored copies of the same rows under fresh coins.
(This file follows the verifier's steps and claims nothing about hiding.) The link is run once for
each copy. Its claim: the copy's rows agree with the first table's in every entry before the cut,
which is where the pads of a row's message begin (docs/format/FORMAT.md, R13.8 to R13.10). It
starts from what the first table's one-time test is meant to show, and does not ask whether that
test was run: that the first key means a table. Of the copy nothing is known before except its root
and, with a record, its record.

The course of the chain, whose statement must hold both tables' roots and records:
  the verifier draws one fold point for both tables;
  the prover sends, in one message, each table's fold at that point, whole, and the verifier samples
  both;
  the verifier draws positions in one message: the first draws are columns of the first table, the
  others of the copy; the prover opens these columns;
  the verifier draws the point of comparison;
  a proximity test on the one group that holds the two folded rows ends the chain.
The strict reader of the chain's bytes, not this file, tests that the opened columns lead to the two
roots. Two conditions on values are tested directly: no seed of a sample and no seed of a record has
the factor 0. Everything else that the link claims is a row with a public target on that group, left
to the proximity test: for each table one row for each drawn column and, with a record, one for each
answer; and the equality row, which says that the two folded rows agree before the cut. No target of
these rows is named by the prover: each is 0, a fold of a key's record, or a fold of symbols that
were read under a root. (The sample rows of the two folded rows, whose targets are the prover's
answers, are SEND's.)

Main definitions: `Params.LinkShape.side`, `Params.LinkShape.test`, `linkOk`, `linkMessage`,
`linkEqualityRow`, `LinkRun`, `linkStepsVerify`, `linkTestVerify`, `linkVerify`.

What is not claimed. The shape says how the draws of positions are cut between the two tables, a
plan's entry only their sum. That the plan's maker counted the same two numbers and priced the same
table is not tested here (link.h, steps_verify: require_first_list, require_table). It holds where
shape and plan are derived from one value, as in every call of the program. It is the duty of
whoever makes the two otherwise. No theorem is stated here.
-/
import OnBytes.Iop.Foldeq
import OnBytes.Iop.Prox

namespace OnBytes

open Params (LinkShape FoldeqShape IoppStage)

/-! ## The public shape -/

namespace Params.LinkShape

/-- The number of bits of the index of an entry in a row's message. -/
def entryBits (S : LinkShape) : Nat := S.table.cubeBits

/-- The cut: the tables are compared on this many entries at the start of a row's message, that is,
on all entries before the pads (on the whole message, if there are no pads). It follows from the
tables' shape and is no number of its own. Places that no matrix uses are compared too, so every
place of an honest table is either compared or fresh randomness. A shorter cut would let a copy
differ in an entry that later proofs read. -/
def cut (S : LinkShape) : Nat := S.table.plain

/-- One side of the link as the shape of a fold of a table. The two sides differ only in their
numbers of columns. samples: the answers to a sample, as the plan has them. -/
def side (S : LinkShape) (ofTheFurtherTable : Bool) (samples : Nat) : FoldeqShape :=
  { index := S.table
    u := { code := S.code, mainRows := S.rows, mainDeg := 3, answers := samples }
    rowsHigh := S.rowsHigh
    leafClass := S.leafClass
    columns := if ofTheFurtherTable then S.columnsFurther else S.columnsFirst }

/-- The first stage of the proximity test: the group of the two folded rows. Each member takes an
aligned block of rows, the least power of two that holds its own; there are no mask rows except the
fold's. -/
def firstStage (S : LinkShape) : IoppStage :=
  { code := S.code, maskCode := S.maskCode, k := 1 + ceilLog2 S.rows, h := 0 }

/-- All stages of the proximity test. -/
def test (S : LinkShape) : List IoppStage := S.firstStage :: S.later

/-- What the shape shows without the codes. -/
def ok (S : LinkShape) : Bool :=
  S.table.ok && decide (1 ≤ S.columnsFirst) && decide (1 ≤ S.columnsFurther) &&
  decide (1 ≤ S.rows) && !S.later.isEmpty && S.later.all stageOk

end Params.LinkShape

/-- The conditions on the shape by itself and with the codes that it names. foldeqOk is asked of the
first side only: the other side differs only in its number of columns, which LinkShape.ok has
tested. -/
def linkOk (codes : Codes) (S : LinkShape) (samples : Nat) : Bool :=
  S.ok && foldeqOk codes (S.side false samples) && decide (S.maskCode < codes.mask.size) &&
  ioppOk codes S.test samples

/-- The first fold of the test, as far as its fresh mask needs it. The mask's size follows from the
stage's h and mask code (`foldMaskNotice`), not from where each member is in the group, so the
layout stays empty here. -/
def linkFoldShape (S : LinkShape) : FoldShape :=
  { ioppFoldShape S.firstStage {} with maskLeafClass := S.leafClass }

/-- What the link's one message with oracle messages holds, in order: the first table's folded row,
the copy's, and, if masks are sent ahead, the fresh mask of the test's first fold. -/
def linkMessage (S : LinkShape) (samples : Nat) : Array OracleNotice :=
  #[⟨(S.side false samples).u, S.leafClass⟩, ⟨(S.side true samples).u, S.leafClass⟩] ++
    (if S.masksAhead then #[foldMaskNotice (linkFoldShape S)] else #[])

/-! ## The equality row -/

/-- The row that says that the two folded rows agree before the cut:
< eq(phi, .) on the entries before the cut, the first row's message - the copy's > = 0.
The row stops at the cut: pads and random tails of two tables are drawn independently, so a row that
ran on would be false for honest tables. cut: linkStepsVerify passes S.cut; it is a parameter as in
link.h, where a test forms the row with another cut. -/
def linkEqualityRow (S : LinkShape) (phi : List E) (first further : FoldedRow) (cut : Nat) :
    Option Row := do
  if phi.length != S.entryBits then none
  let plus ← tensorBelow (Tensor.eq phi oneE) 0 S.entryBits cut
  let minus ← tensorBelow (Tensor.eq phi (negE oneE)) 0 S.entryBits cut
  pure (further.addAll (first.addAll {} plus) minus)

/-! ## The block -/

/-- What the steps before the proximity test leave for it. -/
structure LinkRun where
  gamma : List E := []
  phi : List E := []
  first : FoldedRow := {}
  further : FoldedRow := {}
  group : Nat := noId
  /-- the mask of the first fold of the test, if it went out with the folded rows -/
  mask : Option Nat := none

/-- The target of row number i of a group, for a note. -/
def groupTarget (g i : Nat) : Blk E := do
  pure (((← Blk.group g).rows[i]?.map (·.target)).getD zeroE)

/-- The link's steps before the proximity test. first, further: the two tables as the chain's
statement must hold them, the first table in item 0 and the copy in item 1. That it holds them, with
these records, and which item a key names (TableKey.item) is the caller's word: not tested here. -/
def linkStepsVerify (S : LinkShape) (first further : TableKey) : Blk LinkRun := do
  let samples ← Blk.samples
  Blk.must (linkOk (← Blk.statement).codes S samples)
  let sideFirst := S.side false samples
  let sideFurther := S.side true samples
  foldeqRequire first sideFirst
  foldeqRequire further sideFurther
  let gamma ← drawPoint "LINK point" S.table.v
  let eqGamma := foldeqWeights gamma
  let group ← Blk.newGroup S.code S.maskCode
  let ids ← sendVerify (linkMessage S samples)
  let mask ← if S.masksAhead then (do pure (some (← Blk.get ids[2]?))) else pure none
  let u0 ← foldeqJoined sideFirst first eqGamma (← Blk.get ids[0]?) group
  let u1 ← foldeqJoined sideFurther further eqGamma (← Blk.get ids[1]?) group
  Blk.note "LINK: the target of the first table's record's first row" (← groupTarget group 0)
  Blk.note "LINK: the target of the further table's record's first row"
    (← groupTarget group S.table.answers)
  let drawn ← Blk.closePositions "LINK" S.table.code.logN
  Blk.must (drawn.2.isEmpty && drawn.1.draws.size == S.columnsFirst + S.columnsFurther)
  let rowsBefore := (← Blk.group group).rows.size
  foldeqColumnsVerify first sideFirst eqGamma drawn.1 0 u0 group
  foldeqColumnsVerify further sideFurther eqGamma drawn.1 S.columnsFirst u1 group
  Blk.note "LINK: the fold of the first table's column at its first draw"
    (← groupTarget group rowsBefore)
  Blk.note "LINK: the fold of the further table's column at its first draw"
    (← groupTarget group (rowsBefore + S.columnsFirst))
  let phi ← drawPoint "LINK phi" S.entryBits
  Blk.addRow group (← Blk.get (linkEqualityRow S phi u0 u1 S.cut))
  Blk.note "LINK: the equality row's coefficient at entry 0 of the first table's folded row"
    (phi.foldl (fun s x => mulE s (subE oneE x)) oneE)
  pure { gamma := gamma, phi := phi, first := u0, further := u1, group := group, mask := mask }

/-- The link's proximity test. -/
def linkTestVerify (S : LinkShape) (x : LinkRun) : Blk Unit :=
  ioppVerify x.group S.test S.choice x.mask

/-- The whole block of a link's chain. It fails at its end unless `Blk.requireAllTested` holds. -/
def linkVerify (S : LinkShape) (first further : TableKey) : Blk Unit := do
  let x ← linkStepsVerify S first further
  linkTestVerify S x
  Blk.requireAllTested

end OnBytes
