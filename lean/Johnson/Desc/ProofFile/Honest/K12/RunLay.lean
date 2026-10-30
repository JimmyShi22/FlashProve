-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunLay.lean: the first stage of a proximity test (`KindName.K12`)
on a group of several oracle messages, as lists of words: each member's rows placed at its block
among the stage's rows, and each tree given as the members' rows that it holds. Definitions only. It
imports RunRows.lean alone; no Mathlib.

  `RowBlock`, `layRows`   a member's rows with the number of its block's first row and their count;
                 n rows, each taken from the first block that covers its number, zeros where none
                 does
  `MemShape`     a member's public numbers: first row and count of its main rows and of its mask
                 rows; whether its main rows are over the base field
  `Piece`, `selsOf`   a stretch of a tree's column: a member's main rows, a member's mask rows, or
                 the fresh table's rows; the same as a list of `Sel` (RunRows.lean)
  `layFirst`     the stage's four lists, from the members' shapes and rows
  `treesOf`      the trees, from their depths and pieces

Limits.
- Where a member's block begins and how many rows it has are the caller's statement. The verifier's
  own layout is not computed here; `ManyJob.layFits` (RunMany.lean) compares the two.
- A member that gives fewer rows than its count, or a shorter row or tail, leaves an empty or short
  list, which `normFirst` pads with 0, tails too (see RunRows.lean's limits). `firstSized` on the
  result of `layFirst` is false in that case, unless the row is covered by another block or lies
  beyond the stage's rows. It cannot tell where the count itself is too small: then the row counts
  as no member's and is all 0. Where `ManyJob.layFits` is true, the first rows and the counts are
  those of the verifier's own layout; that its blocks neither overlap nor run beyond the stage's
  rows is by reading `layBlocks` (OnBytes/Iop/Ground.lean): no lemma or test here says it.
- Where blocks overlap, the first in the list wins. Rows of a block beyond the stage's number of
  rows are dropped, and so are rows that a member gives beyond its count. A piece that names no
  member gives no row. None of these leaves a warning.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt.M1 (E Stage)
open Fmt.M1.Own (PSt)

/-- A member's rows, or their tails, with its block's first row and the number of rows. -/
structure RowBlock where
  first : Nat
  count : Nat
  rows : List (List E)

/-- **n rows.** Row b is row b - first of the first block that covers b; the empty list where that
block's member gives no such row. A row that no block covers is len zeros: by the layout such a row,
and its tail, is 0. So, where the blocks do not overlap and lie within the n rows, `firstSized`
(RunBy.lean) on the result is false where a member's row is missing or has another length than len,
and only there. At len = 0 a missing row, the empty list, has the length len and passes the check.
-/
def layRows (n len : Nat) (bs : List RowBlock) : List (List E) :=
  (List.range n).map fun b =>
    (bs.findSome? fun B =>
      if B.first ≤ b ∧ b < B.first + B.count then some (B.rows.getD (b - B.first) [])
      else none).getD (List.replicate len Fmt.Fld.zeroE)

/-- **A member's public numbers.** -/
structure MemShape where
  mainFirst : Nat := 0
  mainRows : Nat := 0
  maskFirst : Nat := 0
  maskRows : Nat := 0
  /-- its main rows are over the base field: a symbol is written as one word -/
  base : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- A stretch of a tree's column. The number: the member's, in the group's order. -/
inductive Piece where
  | main (t : Nat)
  | mask (t : Nat)
  | fresh
  deriving DecidableEq, Repr

/-- A piece as rows of the stage. -/
def selsOf (s : Stage) (ms : List MemShape) : Piece → List Sel
  | .main t =>
    match ms[t]? with
    | some m => (List.range m.mainRows).map fun r => ⟨.main, m.mainFirst + r, m.base⟩
    | none => []
  | .mask t =>
    match ms[t]? with
    | some m => (List.range m.maskRows).map fun r => ⟨.mask, m.maskFirst + r, false⟩
    | none => []
  | .fresh => (List.range (2 ^ s.h)).map fun r => ⟨.fresh, r, false⟩

/-- **The stage's four lists.** Each member: its shape; its main rows, their tails, its mask rows,
their tails (the first four fields; the two others are not read). -/
def layFirst (s : Stage) (ms : List (MemShape × PSt)) : PSt :=
  { M := layRows (2 ^ s.k) s.C.l (ms.map fun x => ⟨x.1.mainFirst, x.1.mainRows, x.2.M⟩)
    Rh := layRows (2 ^ s.k) s.C.r (ms.map fun x => ⟨x.1.mainFirst, x.1.mainRows, x.2.Rh⟩)
    W := layRows (2 ^ s.h) s.Z.l (ms.map fun x => ⟨x.1.maskFirst, x.1.maskRows, x.2.W⟩)
    Sg := layRows (2 ^ s.h) s.Z.r (ms.map fun x => ⟨x.1.maskFirst, x.1.maskRows, x.2.Sg⟩)
    P := [], Pi := [] }

/-- **The trees**: each tree's depth, and the rows that it holds in its column's order. -/
def treesOf (s : Stage) (ms : List MemShape) (ts : List (Nat × List Piece)) :
    List (Nat × List Sel) :=
  ts.map fun T => (T.1, T.2.flatMap (selsOf s ms))

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.RowBlock
#print axioms ProofFile.Honest.K12.Light.layRows
#print axioms ProofFile.Honest.K12.Light.MemShape
#print axioms ProofFile.Honest.K12.Light.Piece
#print axioms ProofFile.Honest.K12.Light.selsOf
#print axioms ProofFile.Honest.K12.Light.layFirst
#print axioms ProofFile.Honest.K12.Light.treesOf
