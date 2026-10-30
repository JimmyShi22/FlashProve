-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Fold.lean: the three tests in front of a fold, as a named part of the description.

A fold replaces the 2^k rows of a group of oracle messages by one row, and the 2^h rows of its masks
by one. Before it hears anything, the verifier tests: that the shape of the fold fits the codes and
the messages; that the message named as the fresh mask is one; that the row to be folded has the
sizes of the group's tables.

  `foldShapeFits S F`: the shape F fits the statement S.
  `foldMaskFits S F fresh`: the oracle message number fresh can be the fold's fresh mask.
  `foldRowFits S F row`: the row has the sizes of the group's tables.
A mark [n] behind a line numbers the clause.

WHAT THEY READ. Numbers, sizes and marks of the statement, the shape and the row, WITH ONE
EXCEPTION: `formFits` (Johnson/Desc/Own/Shapes.lean; called by `foldRowFits`) asks of each vector of
product form in a form that every written-out variable has the pair (1, 1): an equality of elements,
on the row's coefficients. Whence a row's coefficients come is not said here.

HOW FAR THE TEXT IS ITS OWN. It is `verify-on-bytes`'s foldShapeOk, foldMaskOk and foldRowOk
(OnBytes/Iop/Fold.lean) taken over token for token under new names. In `foldShapeFits` two small
helpers are written out (maskFits c zk as zk.logN ≤ c.logN; foldMaskColumns k h as 2 k + 1 - h);
GroupLayout.find is written as members.idxOf?; Form.fits is `formFits`. IT ADDS NO SECOND,
INDEPENDENT EYE ON WHAT THESE TESTS SHOULD ASK. Each is a drop-in at the same arguments. That each
says yes exactly where that program's does, at all arguments: FoldAgree.lean. What each checks, as a
proposition in plain terms: FoldMean.lean. Both lie beside this file; no block's text imports them.

Of `verify-on-bytes` this file names records (Statement, FoldShape, GroupRow and their fields) and
two functions that return numbers (ceilLog2, Statement.tableBits). By a walk by constants beneath
the three, two definitions of that verifier's files return a yes or no: the record's field
Oracle.sampled, and the equality of two elements (inside `formFits`). The walk counts by the result
type as written, in modules under OnBytes and Fmt alone.

Definitions with code; no theorem. Nothing on soundness, on an honest prover or on hiding.

-/
import OnBytes.Iop.Fold
import Johnson.Desc.Own.Shapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- **The shape of a fold fits the statement**: the two codes are there; the numbers of row
variables fit each other and the mask code; the layout's four lists have one length; each member is
there, has the fold's codes, and has a block where it has rows to fold, inside the cube; and some
member has a main row to fold. -/
def foldShapeFits (S : Statement) (F : FoldShape) : Bool :=
  let L := F.layout
  let n := L.members.size
  match S.codes.base[F.code]?, S.codes.mask[F.maskCode]? with                            -- [1] [2]
  | some c, some zk =>
    decide (1 ≤ L.k) &&                                                                  -- [3]
    decide (L.h ≤ L.k) &&                                                                -- [4]
    decide (zk.logN ≤ c.logN) &&                                                         -- [5]
    decide (2 * L.k + 1 - L.h ≤ zk.ell) &&                                               -- [6]
    L.kept.size == n && L.mainFirst.size == n && L.maskFirst.size == n &&                -- [7-9]
    ((List.range n).all fun i =>
      match S.oracles[L.members.getD i noId]? with
      | none => false                                                                    -- [10]
      | some x =>
        let o := x.shape
        let folded := decide (0 < o.mainRows) && !L.kept.getD i false
        (o.mainRows == 0 || o.code == F.code) &&                                         -- [11]
        (o.maskRows == 0 || o.maskCode == F.maskCode) &&                                 -- [12]
        (match L.mainFirst.getD i none with
          | some f => folded && decide (f + o.mainRows ≤ 2 ^ L.k)                        -- [13]
          | none => !folded) &&                                                          -- [14]
        (match L.maskFirst.getD i none with
          | some f => decide (0 < o.maskRows) && decide (f + o.maskRows ≤ 2 ^ L.h)       -- [15]
          | none => o.maskRows == 0)) &&                                                 -- [16]
    ((List.range n).any fun i =>
      match S.oracles[L.members.getD i noId]? with
      | none => false
      | some x => decide (0 < x.shape.mainRows) && !L.kept.getD i false)                 -- [17]
  | _, _ => false

/-- **The oracle message number fresh can be the fold's fresh mask**: it is there; it has no main
row and 2^h mask rows under the fold's mask code; it has no sample and is to have none; it is no
member of the group. -/
def foldMaskFits (S : Statement) (F : FoldShape) (fresh : Nat) : Bool :=
  match S.oracles[fresh]? with
  | none => false                                                                        -- [1]
  | some o =>
    o.shape.mainRows == 0 &&                                                             -- [2]
    o.shape.maskRows == 2 ^ F.layout.h &&                                                -- [3]
    o.shape.maskCode == F.maskCode &&                                                    -- [4]
    !o.sampled &&                                                                        -- [5]
    o.shape.answers == 0 &&                                                              -- [6]
    !F.layout.members.contains fresh                                                     -- [7]

/-- **The row has the sizes of the group's tables**: its form on the main table has the table's
index bits; its vector on the mask table has the table's length; each of its separate forms is on a
kept member of the layout and has the index bits of that member's own main table. -/
def foldRowFits (S : Statement) (F : FoldShape) (row : GroupRow) : Bool :=
  let c := S.codes.base.getD F.code default
  let zk := S.codes.mask.getD F.maskCode default
  formFits row.c (F.layout.k + ceilLog2 c.ell) &&                                        -- [1]
  row.d.size == zk.ell * 2 ^ F.layout.h &&                                               -- [2]
  row.kept.all fun f =>
    (match F.layout.members.idxOf? f.oracle with
      | some i => F.layout.kept.getD i false                                             -- [3]
      | none => false) &&                                                                -- [4]
    formFits f.c (S.tableBits f.oracle .main)                                            -- [5]

end VerifiableInference.Desc.Own
