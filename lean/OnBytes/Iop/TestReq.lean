-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/TestReq.lean: tests of OnBytes/Iop/Req.lean and OnBytes/Iop/ReqRows.lean.

The numbers of row variables, k and h, of the groups of a chain of three links are compared with a
known answer of the format page (docs/format/format-vectors.txt, R12.x; its two other
numbers, on a group's tree, are not computed in these files). The numbers of kept messages are
worked out by hand. The tensor of a laid block is compared, entry for entry, with the weights
computed element by element from the definition of a block. `laidOk` and `reqLayoutOk` are each
tried on a lawful layout and on layouts that differ from a lawful one in one thing. Not tried here:
`reqOk`, `laidForm`, `ReqRows.make`, `ReqRows.row`, and the frame's blocks. The program does not
import this file.
-/
import OnBytes.Iop.ReqRows

namespace OnBytes.TestReq

open Params (ReqMessage ReqLink ReqShape LaidBlock ReqArray)

/-! ## The groups of a chain of links -/

/-- An oracle message of a link over the base field, in class 0 and at moment 0, from its numbers of
main rows and mask rows and its life. -/
def message (mainRows maskRows life : Nat) : ReqMessage :=
  { shape := { code := 0, mainRows := mainRows, mainDeg := 1, maskRows := maskRows, maskCode := 0,
               answers := 1 }
    leafClass := 0, moment := 0, life := life }

/-- Three links: each sends a message with the link's mask row and a second message, which in the
first two links the next link reads. These are the three links of the known answer. -/
def three : ReqShape :=
  { code := 0, maskCode := 0
    link := [⟨0, [message 2 1 0, message 1 0 1]⟩, ⟨0, [message 1 1 0, message 1 0 1]⟩,
             ⟨0, [message 1 1 0, message 1 0 0]⟩]
    atStart := [], answers := 1
    last := [⟨0, 0, 1, 0⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 0, 0⟩], choice := ⟨true⟩ }

#guard (reqGroups three).toList.map (fun G => (G.k, G.h)) == [(1, 0), (2, 0), (3, 0), (1, 0)]
#guard (reqGroups three).toList.map (·.target.kept.size) == [0, 1, 1, 0]
#guard (reqGroups three).toList.map (·.born.toList) == [[], [(0, 1)], [(1, 1)], []]
#guard reqShapeOk three && three.link.map reqMoments == [1, 1, 1]
/-- The three links with no answer to a sample, in the request's number and in every message. -/
def noAnswers : ReqShape :=
  { three with
    answers := 0
    link := three.link.map fun l =>
      { l with
        messages := l.messages.map fun m => { m with shape := { m.shape with answers := 0 } } } }

-- no answer to a sample, in the request's number alone and in every message too
#guard !reqShapeOk { three with answers := 0 } && !reqShapeOk noAnswers
-- a message kept beyond the last link, with the last test's first stage fitted to the last group
#guard !reqShapeOk
  { three with
    link := three.link.dropLast ++ [⟨0, [message 1 1 0, message 1 0 1]⟩]
    last := [⟨0, 0, 2, 0⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 0, 0⟩] }
-- a kept message with mask rows; a message without rows
#guard !reqMessageOk (message 1 1 1) && reqMessageOk (message 1 0 1)
#guard !reqMessageOk (message 0 0 0)
-- a last test whose first stage is not the last group; a last test of one stage
#guard !reqShapeOk { three with last := [⟨0, 0, 2, 0⟩, ⟨1, 1, 1, 1⟩, ⟨2, 2, 0, 0⟩] }
#guard !reqShapeOk { three with last := [⟨0, 0, 1, 0⟩] }
-- a moment that is empty
#guard !reqLinkOk ⟨0, [message 1 1 0, { message 1 0 0 with moment := 2 }]⟩
#guard reqLinkOk ⟨0, [message 1 1 0, { message 1 0 0 with moment := 1 }]⟩

/-! ## A laid block's tensor -/

/-- A made-up element of the extension field. -/
def el (n : Nat) : E :=
  E.mk3 (UInt64.ofNat (1000003 * n + 17)) (UInt64.ofNat (n * n + 3)) (UInt64.ofNat (7 * n + 1))

/-- The weight of index i. -/
def weightAt (w : IndexWeights) (i : Nat) : E :=
  match w.values with
  | some v => v.getD i zeroE
  | none =>
    (List.range w.lo.size).foldl
      (fun s t => mulE s (if i / 2 ^ t % 2 == 1 then w.hi.getD t zeroE else w.lo.getD t zeroE)) oneE

/-- scalar * onI[i] * onC[c] on the block's elements, written out on the table, element by element
from the definition of a block. -/
def written (b : LaidBlock) (rowBits placeBits : Nat) (onI onC : IndexWeights) (scalar : E) :
    Array E :=
  (List.range (2 ^ b.bitsI)).foldl (fun out i =>
    (List.range (2 ^ b.bitsC)).foldl (fun out c =>
      let x := if b.iIsLow then c * 2 ^ b.bitsI + i else i * 2 ^ b.bitsC + c
      let row := b.firstRow + x / 2 ^ b.placeBits
      let place := b.firstPlace + x % 2 ^ b.placeBits
      out.setIfInBounds (row + 2 ^ rowBits * place)
        (mulE scalar (mulE (weightAt onI (b.firstI + i)) (weightAt onC (b.firstC + c))))) out)
    (Array.replicate (2 ^ (rowBits + placeBits)) zeroE)

/-- True if the block's tensor, written out, is the vector computed element by element. -/
def agrees (b : LaidBlock) (rowBits placeBits : Nat) (onI onC : IndexWeights) : Bool :=
  (laidTensor b rowBits placeBits onI onC (el 9)).map
      (fun t => (Form.ofTensor t).writeOut (rowBits + placeBits)) ==
    some (written b rowBits placeBits onI onC (el 9))

/-- A block of 2 rows and 4 columns of a matrix, in 2 rows of 4 places of a table. -/
def block (iIsLow : Bool) : LaidBlock :=
  { firstI := 2, firstC := 4, firstRow := 2, firstPlace := 4, bitsI := 1, bitsC := 2, rowBits := 1,
    placeBits := 2, iIsLow := iIsLow }

/-- Equality weights on three bits. -/
def onThree : IndexWeights := IndexWeights.eq #[el 1, el 2, el 3]
/-- Weights that are written out on eight indices. -/
def onEight : IndexWeights := IndexWeights.written ((Array.range 8).map fun i => el (20 + i))

-- what the two product forms give to an index
#guard (List.range 8).all fun i => weightAt (IndexWeights.powers (el 5) 3) i == powE (el 5) i
#guard (List.range 8).all fun i =>
  weightAt onThree i ==
    (List.range 3).foldl
      (fun s t => mulE s (if i / 2 ^ t % 2 == 1 then el (t + 1) else subE oneE (el (t + 1)))) oneE

#guard [true, false].all fun low =>
  agrees (block low) 2 3 onThree onThree && agrees (block low) 2 3 onEight onThree &&
  agrees (block low) 2 3 onThree onEight &&
  agrees (block low) 2 3 (IndexWeights.powers (el 5) 3) onEight
-- a block of one element: the written-out weight becomes a factor
#guard agrees { block true with bitsI := 0, bitsC := 0, rowBits := 0, placeBits := 0 } 2 3 onEight
  onThree
-- a block that fills one row; one that fills one place of eight rows
#guard agrees { firstI := 0, firstC := 0, firstRow := 3, firstPlace := 0, bitsI := 1, bitsC := 2,
                rowBits := 0, placeBits := 3, iIsLow := true } 2 3 onThree onEight
#guard agrees { firstI := 0, firstC := 0, firstRow := 0, firstPlace := 5, bitsI := 1, bitsC := 2,
                rowBits := 3, placeBits := 0, iIsLow := false } 3 3 onEight onThree
-- refused: both weights written out; a product form with too few bits; factors of unequal number;
-- a written-out vector that is too short; a block that leaves the table
#guard (laidTensor (block true) 2 3 onEight onEight oneE).isNone
#guard (laidTensor (block true) 2 3 (IndexWeights.eq #[el 1]) onEight oneE).isNone
#guard (laidTensor (block true) 2 3 { lo := #[el 1, el 2], hi := #[el 1] } onEight oneE).isNone
#guard (laidTensor (block true) 2 3 onThree (IndexWeights.written #[el 1, el 2]) oneE).isNone
#guard (laidTensor (block true) 1 3 onThree onEight oneE).isNone

/-! ## Layouts -/

/-- A matrix of 2 rows and 4 columns in one block. -/
def matrix (name : String) (firstRow : Nat) : ReqArray :=
  { name := name, message := 0, sizeI := 2, sizeC := 4
    blocks := [{ firstI := 0, firstC := 0, firstRow := firstRow, firstPlace := 0, bitsI := 1,
                 bitsC := 2, rowBits := 1, placeBits := 2, iIsLow := true }] }

#guard laidOk [matrix "a" 0, matrix "b" 2] 2 3
-- two matrices on the same entries; a matrix that its blocks do not cover; a block not aligned
#guard !laidOk [matrix "a" 0, matrix "b" 0] 2 3
#guard !laidOk [{ matrix "a" 0 with sizeC := 8 }] 2 3
#guard !laidOk [matrix "a" 1] 2 3
-- a block twice in one matrix, at two places of the table
#guard !laidOk
  [{ matrix "a" 0 with sizeI := 4, blocks := (matrix "a" 0).blocks ++ (matrix "a" 2).blocks }] 2 3
-- a block outside its matrix, which has as many elements; a block outside the table, twice
#guard !laidOk [{ matrix "a" 0 with sizeI := 1, sizeC := 8 }] 2 3
#guard !laidOk [matrix "a" 4] 2 3 && !laidOk [matrix "a" 0] 0 3
-- a block that is smaller in the table than in its matrix
#guard !laidOk
  [{ matrix "a" 0 with blocks := (matrix "a" 0).blocks.map fun b => { b with placeBits := 1 } }] 2 3

/-- Codes with messages of eight entries. -/
def codes : Codes := { base := #[⟨4, 8, 3⟩], mask := #[⟨4, 8, 3⟩] }

/-- A request of one link with one oracle message. Only its links are read here. -/
def oneLink (m : ReqMessage) : ReqShape := { three with link := [⟨0, [m]⟩] }

/-- An array of one element at one entry of the first message's table. -/
def cell (name : String) (row place : Nat) : ReqArray :=
  { name := name, message := 0, sizeI := 1, sizeC := 1
    blocks := [{ firstI := 0, firstC := 0, firstRow := row, firstPlace := place, bitsI := 0,
                 bitsC := 0, rowBits := 0, placeBits := 0, iIsLow := true }] }

/-- `reqLayoutOk` for one link with one message of so many main rows and no mask rows. The pad of
the message's sample is then in the last three places of its last row. -/
def lawful (mainRows : Nat) (arrays : List ReqArray) : Bool :=
  reqLayoutOk codes (oneLink (message mainRows 0 0)) ⟨[arrays]⟩

#guard lawful 2 [matrix "a" 0] && lawful 2 [cell "a" 0 0, cell "b" 0 1]
-- a block over the pad, and the entries beside the pad
#guard [5, 6, 7].all fun place => !lawful 2 [cell "a" 1 place] && lawful 2 [cell "a" 0 place]
#guard lawful 2 [cell "a" 1 4]
-- a block in rows that are not sent: three rows are sent, and the table has four
#guard lawful 3 [matrix "a" 0] && !lawful 3 [matrix "a" 2] && !lawful 3 [cell "a" 3 0]
-- a name twice; no name; a message that the link does not have; an array without blocks
#guard !lawful 2 [cell "a" 0 0, cell "a" 0 1] && !lawful 2 [cell "" 0 0]
#guard !lawful 2 [{ cell "a" 0 0 with message := 1 }]
#guard !lawful 2 [{ cell "a" 0 0 with blocks := [] }]
-- an array in a message without main rows; another number of links than the request's
#guard !reqLayoutOk codes (oneLink (message 0 1 0)) ⟨[[cell "a" 0 0]]⟩
#guard !reqLayoutOk codes (oneLink (message 2 0 0)) ⟨[]⟩
#guard reqLayoutOk codes (oneLink (message 2 0 0)) ⟨[[]]⟩

end OnBytes.TestReq
