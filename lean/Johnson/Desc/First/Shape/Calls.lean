-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Calls.lean: THE SHAPES OF THE STATE OF THE CALLS OVER THE LINKS, OF A
LINK's CONTEXT AND OF THE BOOK OF TREES: what is left of these records of the first chain's state
when every field element and every digest is left out. Definitions alone: Lean structures, their
makers, and a way back for the calls' state. Three small theorems: two on the way back
(frameSh_blank, checkSh_blank), one on the two readers of the link's number (check_link).

What it is for. Johnson/Desc/First/Shape/Chain.lean lays the shapes of the state's records together.
The sendings, the code switches and the links' quiet steps read and write these three records.

THE FIELDS' TYPES, so that a reader can hold them against the records (OnBytes/Iop/Req.lean:252,
OnBytes/Model/ReqChain.lean:45, OnBytes/Model/Trees.lean:169, OnBytes/Iop/Ground.lean:461 and :481):
  `FrameSh`   of ReqFrame, each under its own name and type: shape : ReqShape,
              groups : Array ReqGroup, next : ReqNext, link moment group : Nat,
              keptBefore atStart own : Array Nat,
              mask : Option Nat; of plain : List E its length; rows : SingleSh (Single.lean).
  `CheckSh`   of ChainCheck: frame : FrameSh, rows : ReqRows, sent : Array Nat, inLink : Bool,
              moments : Nat.
  `LinkSh`    of LinkCtx: check : CheckSh, link : Nat, arrayOf : Array (Nat × String), list : Tail2,
              moments : Nat, handed done : Bool.
  `BTreeSh`   of Tree: shape : TreeShape, number : Nat, parts : Array Nat, oneList : Bool,
              lists : Nat; of src : Fmt.Src the constructor, and the number where it is "own":
              own : Option Nat. The two byte strings of "given" are left out.
  `BookSh`    of TreeBook: trees : Array BTreeSh, place : Array (Nat × Nat).
ReqShape, ReqGroup, ReqNext, ReqRows, Tail2 and TreeShape are the library's own records of numbers,
Bools, strings, lists, arrays and options of these; that they hold no field element and no digest is
a reading of their fields' types, not a theorem.

The makers lay no default: an Option stays an Option.
  `frameSh`, `checkSh`, `linkSh`, `bTreeSh`, `bookSh`.
  `FrameSh.blank`, `CheckSh.blank`: the way back: the same numbers, flags and lists; zeros for the
  plain scalars; the single rows' own way back. `frameSh_blank`, `checkSh_blank`: the
  shape of the way back is the shape. `CheckSh.link`, `.links`: the library's readers of that name,
  on shapes.

Limits. A number can still be made of a value: which numbers of these records are public given the
three public files, or counts, is argued elsewhere. Nothing on soundness, completeness or hiding.

-/
import OnBytes.Model.Trees
import OnBytes.Model.ReqChain
import Johnson.Desc.First.Shape.Single

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params

/-- The frame of the calls without its plain scalars and its rows' elements. -/
structure FrameSh where
  shape : ReqShape
  groups : Array ReqGroup
  next : ReqNext
  link : Nat
  moment : Nat
  group : Nat
  keptBefore : Array Nat
  atStart : Array Nat
  own : Array Nat
  /-- the number of plain scalars -/
  plain : Nat
  mask : Option Nat
  rows : SingleSh

def frameSh (f : ReqFrame) : FrameSh :=
  { shape := f.shape, groups := f.groups, next := f.next, link := f.link, moment := f.moment
    group := f.group, keptBefore := f.keptBefore, atStart := f.atStart, own := f.own
    plain := f.plain.length, mask := f.mask, rows := singleSh f.rows }

/-- The way back: zeros for the plain scalars and in the rows. -/
def FrameSh.blank (f : FrameSh) : ReqFrame :=
  { shape := f.shape, groups := f.groups, next := f.next, link := f.link, moment := f.moment
    group := f.group, keptBefore := f.keptBefore, atStart := f.atStart, own := f.own
    plain := List.replicate f.plain zeroE, mask := f.mask, rows := f.rows.blank }

theorem frameSh_blank (f : FrameSh) : frameSh f.blank = f := by
  cases f
  simp [frameSh, FrameSh.blank, singleSh_blank]

/-- The state of the calls over the links. -/
structure CheckSh where
  frame : FrameSh
  rows : ReqRows
  sent : Array Nat
  inLink : Bool
  moments : Nat

def checkSh (c : ChainCheck) : CheckSh :=
  { frame := frameSh c.frame, rows := c.rows, sent := c.sent, inLink := c.inLink
    moments := c.moments }

def CheckSh.blank (c : CheckSh) : ChainCheck :=
  { frame := c.frame.blank, rows := c.rows, sent := c.sent, inLink := c.inLink
    moments := c.moments }

theorem checkSh_blank (c : CheckSh) : checkSh c.blank = c := by
  cases c
  simp [checkSh, CheckSh.blank, frameSh_blank]

/-- The present link (ChainCheck.link). -/
def CheckSh.link (c : CheckSh) : Nat := c.frame.link

/-- The number of links (ChainCheck.links). -/
def CheckSh.links (c : CheckSh) : Nat := c.frame.shape.link.length

theorem check_link (c : ChainCheck) : (checkSh c).link = c.link ∧ (checkSh c).links = c.links :=
  ⟨rfl, rfl⟩

/-- A link's context. -/
structure LinkSh where
  check : CheckSh
  link : Nat
  arrayOf : Array (Nat × String)
  list : Tail2
  moments : Nat
  handed : Bool
  done : Bool

def linkSh (L : LinkCtx) : LinkSh :=
  { check := checkSh L.check, link := L.link, arrayOf := L.arrayOf, list := L.list
    moments := L.moments, handed := L.handed, done := L.done }

/-- A tree of the book without the byte strings of a given root. -/
structure BTreeSh where
  shape : TreeShape
  number : Nat
  /-- some n: the root is this chain's own, number n; none: it is given -/
  own : Option Nat
  parts : Array Nat
  oneList : Bool
  lists : Nat

def bTreeSh (t : Tree) : BTreeSh :=
  { shape := t.shape, number := t.number
    own := match t.src with
      | .own n => some n
      | .given _ _ => none
    parts := t.parts, oneList := t.oneList, lists := t.lists }

/-- The book of trees. -/
structure BookSh where
  trees : Array BTreeSh
  place : Array (Nat × Nat)

def bookSh (b : TreeBook) : BookSh := { trees := b.trees.map bTreeSh, place := b.place }

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.frameSh_blank
#print axioms VerifiableInference.Desc.First.Shape.checkSh_blank
#print axioms VerifiableInference.Desc.First.Shape.check_link
