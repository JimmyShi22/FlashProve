-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/TestGround.lean: tests of the blocks' common ground, run when the file compiles.

Most tests compare a function of Ground.lean, Send.lean, Bat.lean or Fold.lean, at arbitrary values,
with the function of Fmt/ that states the same rule for the product test or for the chain of links,
or with a number from the product test's description (docs/format/toys/1-product.md). The
other numbers are worked out by hand from the rule in the function's docstring. The test on BAT and
the first two on runs compare two functions of the program with each other. (That row number i gets
x^i is a theorem: combineRows_coefficient, OnBytes/Iop/RowLaws.lean.) The program does not import
this file.
-/
import OnBytes.Iop.Send
import OnBytes.Iop.Bat
import OnBytes.Iop.Fold
import Fmt.M1Send
import Fmt.M1Fold
import Fmt.M2Types

namespace OnBytes.TestGround

open Fmt (Fld)

/-- An arbitrary element of the extension field. -/
def el (n : Nat) : E := E.ofTriple (Fmt.M1.SendG.el .two n)

/-- count arbitrary elements: el s, el (s + 31), and so on. -/
def els (count s : Nat) : List E := (List.range count).map fun i => el (s + 31 * i)

/-- A list of elements as the functions of the directory Fmt/ take it. -/
def tr (l : List E) : List (UInt64 × UInt64 × UInt64) := l.map E.triple

/-! ## Codes -/

#guard [7, 8, 9, 14, 15].all fun a =>
  [0, 1, 2, 3, 5, 64, 77, 127].all fun x => codePoint a x == Fmt.M1.point a x
#guard [0, 1, 6, 100].all fun x =>
  (generatorMessage ⟨7, 16, 3⟩ x).toList == Fmt.M1.genM ⟨7, 16, 3⟩ x &&
    (generatorTail ⟨7, 16, 3⟩ x).toList == Fmt.M1.genT ⟨7, 16, 3⟩ x
#guard [0, 1, 6, 300].all fun x =>
  (generatorMessage ⟨9, 8, 5⟩ x).toList == Fmt.M1.genM ⟨9, 8, 5⟩ x &&
    (generatorTail ⟨9, 8, 5⟩ x).toList == Fmt.M1.genT ⟨9, 8, 5⟩ x
#guard [0, 1, 6, 300].all fun x =>
  (symbolAt ⟨9, 8, 5⟩ x (els 8 1).toArray (els 5 2).toArray).triple ==
    Fmt.M1.symE ⟨9, 8, 5⟩ x (tr (els 8 1)) (tr (els 5 2))
#guard (Code.ok ⟨7, 16, 3⟩) && !(Code.ok ⟨4, 16, 3⟩) && !(Code.ok ⟨0, 1, 0⟩)
#guard !(Code.ok ⟨61, 1, 0⟩)
#guard (List.range 9).map ceilLog2 == [0, 0, 1, 2, 2, 3, 3, 3, 3]

/-! ## Trees: the three trees of the product test, tiny size -/

/-- The codes of the product test at its tiny size. -/
def tiny : Codes := ⟨#[⟨7, 16, 3⟩, ⟨8, 8, 3⟩, ⟨9, 8, 5⟩], #[⟨7, 16, 3⟩, ⟨8, 32, 3⟩, ⟨9, 128, 5⟩]⟩

/-- The oracle message a, b, c: three main rows over the base field and one mask row. -/
def abc : OracleNotice := ⟨{ code := 0, mainRows := 3, maskRows := 1, maskCode := 0 }, 0⟩

/-- The widths of the columns of the trees that some oracle messages make: main symbols, mask
symbols. -/
def widths (sent : Array OracleNotice) : Option (Array (Nat × Nat)) :=
  (layTrees tiny sent).map fun l => l.shapes.map fun t => (t.mainWidth, t.maskWidth)

-- the description's widths 9, 18 and 12, in their parts
#guard widths #[abc, foldMaskNotice { maskCode := 0 }] == some #[(3, 6)]
#guard widths #[⟨{ code := 1, mainRows := 2, mainDeg := 3, maskRows := 2, maskCode := 1 }, 0⟩,
  foldMaskNotice { maskCode := 1, layout := { h := 1 } }] == some #[(6, 12)]
#guard widths #[⟨{ code := 2, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 2 }, 0⟩,
  ⟨{ code := 2, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 2, answers := 0 }, 0⟩] ==
    some #[(6, 6)]
-- another class of leaves makes another tree; a message of mask rows alone joins the first tree
-- of its class
#guard ((layTrees tiny #[abc, ⟨{ maskRows := 1, maskCode := 0 }, 1⟩, ⟨{ maskRows := 1 }, 0⟩]).map
  fun l => (l.tree, l.part)) == some (#[0, 1, 0], #[0, 0, 1])

/-! ## The layout of a group -/

#guard [[some 0, some 2, some 0, some 1], [some 1, none], [none], [some 0, some 0, some 3]].all
  fun (l : List (Option Nat)) =>
    let mine := layBlocks l.toArray
    (mine.1.toList, mine.2) == Fmt.M2.layBlocks l

/-! ## SEND -/

-- the product test's description: 7 coordinates at the tiny size; the pad is the mask table's last
-- index; without mask rows and over the base field it is the last three places of the last real
-- main row; the ledger of one mask row of 16 entries has 15 entries
#guard (Send.cube tiny abc.shape).bits == 7
#guard ((Send.pad tiny abc.shape).map fun l => l.map fun p => (p.part, p.index, p.answer)) ==
  some [(.mask, 15, 0)]
#guard ((Send.pad tiny { code := 0, mainRows := 3 }).map fun l => l.map fun p => (p.index, p.basis))
  == some [(2 + 4 * 13, E.mk3 1 0 0), (2 + 4 * 14, E.mk3 0 1 0), (2 + 4 * 15, E.mk3 0 0 1)]
#guard Send.freeMaskEntries 1 16 1 == 15
-- worked out by hand from the rule: with three rows the pad has the index 2 + 4 * 15 = 62, and of
-- the 62 indices below it 15 fall on the fourth row, which nobody sends
#guard Send.freeMaskEntries 3 16 1 == 47 && Send.maskRowsFor 16 16 1 == 2

/-- A statement that holds the oracle message a, b, c alone, in a group of its own. -/
def oneGroup : Statement :=
  { codes := tiny, oracles := #[{ shape := abc.shape, sampled := true, groups := [0] }],
    groups := #[{ code := 0, maskCode := 0, members := #[0], kept := #[false] }] }

/-- A row on the oracle message a, b, c, written out on the group's two tables. -/
def written (r : Row) : Option (Array E × Array E × E) := do
  let L ← oneGroup.layout 0
  let g ← addToGroupRow oneGroup L r oneE {}
  pure (g.c.writeOut (L.k + L.logEll), g.d, g.target)

-- the sample row is that of the first test protocol
#guard (do
  let r ← Send.form tiny abc.shape 0 ⟨els 7 3, el 99⟩ 0
  let w ← written { r with target := el 5 }
  pure (w.1.map E.triple, w.2.1.map E.triple, w.2.2.triple)) ==
  (let R := Fmt.M1.sampleRow .two 6 4 (tr (els 7 3)) (el 99).triple (el 5).triple
   some (R.c, R.d, R.t))

/-! ## A block's two readings, at SEND -/

/-- SEND of the oracle message a, b, c with a fold's mask; returns the sample row's target and the
next two free mask entries. -/
def sendBlock : Blk (E × List Nat) := do
  let ids ← sendVerify #[abc, foldMaskNotice { maskCode := 0 }]
  let x ← Blk.oracle (ids.getD 0 noId)
  pure (((x.sampleRows[0]?).map (·.target)).getD zeroE, ← Blk.takeMasks (ids.getD 0 noId) 2)

/-- The two entries of a plan for that block. -/
def sendEntries : List Fmt.Entry :=
  [{ name := "SEND seed", msg := 32, roots := 1, drawE := 8, drawNZ := 1 },
   { name := "SEND answer", msg := 24, answers := 1 }]

/-- What the block starts from under some entries. -/
def startWith (entries : List Fmt.Entry) : Start := { entries := entries, st := { codes := tiny } }

-- the dry run notes kinds and items, and opens nothing
#guard ((sendBlock.rounds (startWith sendEntries)).map fun l =>
    l.map fun x => (x.1.kind, x.1.items, x.1.opens.length, x.2.length)) ==
  some [(.seeds, [.root], 0, 0), (.nothing, [.answer], 0, 0)]
/-- The name under which the block's dry run fails under some entries; nothing if it does not. -/
def dryName (entries : List Fmt.Entry) : Option String :=
  match sendBlock.dryRunNamed (startWith entries) with
  | .error f => some f.name
  | .ok _ => none

-- the dry run fails: under another name; another number of coordinates; an entry too many; one too
-- few
#guard dryName sendEntries == none
#guard dryName (sendEntries.map fun e => { e with name := "BAT" }) == some "plan"
#guard dryName (sendEntries.map fun e => if e.drawE == 8 then { e with drawE := 9 } else e) ==
  some "refused"
#guard dryName (sendEntries ++ sendEntries) == some "plan"
#guard dryName (sendEntries.take 1) == some "plan"

/-- The rounds of a view for that block, with arbitrary values; beta is the seed's factor. -/
def sendRounds (beta : E) : List Fmt.RoundView :=
  [⟨[], ⟨tr (els 7 3 ++ [beta]), [], [], none⟩⟩, ⟨[.answer (el 5).triple], ⟨[], [], [], none⟩⟩]

-- the run on a view: the answer is the sample row's target; the ledger begins at entry 0
#guard (sendBlock.walk (startWith sendEntries) [] (sendRounds (el 99))).map (·.1) ==
  some (el 5, [0, 1])
-- refused: a factor 0; an element in the place of the answer; a round too few; an opened column
-- that nobody reads
#guard sendBlock.failureOn (startWith sendEntries) ⟨sendRounds (el 99), []⟩ == none
#guard sendBlock.failureOn (startWith sendEntries) ⟨sendRounds zeroE, []⟩ == some "refused"
#guard sendBlock.failureOn (startWith sendEntries)
  ⟨[⟨[], ⟨tr (els 7 3 ++ [el 99]), [], [], none⟩⟩, ⟨[.e (el 5).triple], ⟨[], [], [], none⟩⟩], []⟩ ==
    some "view-shape"
#guard sendBlock.failureOn (startWith sendEntries) ⟨(sendRounds (el 99)).take 1, []⟩ ==
  some "view-shape"
#guard sendBlock.failureOn (startWith sendEntries) ⟨sendRounds (el 99), [(0, 0, [1])]⟩ ==
  some "view-shape"

/-- SEND of an oracle message with three mask rows; returns its first five free mask entries. -/
def threeMaskRows : Blk (List Nat) := do
  let ids ← sendVerify #[⟨{ code := 0, mainRows := 3, maskRows := 3, maskCode := 0 }, 0⟩]
  Blk.takeMasks (ids.getD 0 noId) 5

-- worked out by hand from the rule: an entry's row is its number's low two bits, and the numbers on
-- the fourth row, which nobody sends, are passed over
#guard (threeMaskRows.walk (startWith sendEntries) [] (sendRounds (el 99))).map (·.1) ==
  some [0, 1, 2, 4, 5]

/-! ## BAT -/

-- to batch the rows and carry the sum to the group's tables gives what Bat.combine gives
#guard (do
  let a ← Send.form tiny abc.shape 0 ⟨els 7 3, el 99⟩ 0
  let b : Row := (({ target := el 8 } : Row).addUnit 0 .mask 3 (el 4)).add 0 .main
    ((Tensor.eq (els 4 50)).insertChoice 0 2 1)
  let L ← oneGroup.layout 0
  let g ← Bat.combine oneGroup 0 ⟨L, #[b, a, b]⟩ (el 7)
  let w ← written (Bat.combineRows #[b, a, b] (el 7))
  pure ((g.c.writeOut 6, g.d, g.target) == w)) == some true

-- a run over the base field gives the same coefficients as the run written over the extension field
#guard (
  let v : Array F := #[5, 6, 7, 8, 9]
  let short : Run := ⟨0, .mask, 2, 3, .stretch v 1 3⟩
  let long : Run := ⟨0, .mask, 2, 3, .own #[ofF 6, ofF 7, ofF 8]⟩
  let got (r : Run) : List E := (List.range 4).map r.coeffs.get
  got (short.scaled (el 3)) == got (long.scaled (el 3)) &&
    got ((long.scaled (el 2)).addScaled short (el 3)) ==
      got ((long.scaled (el 2)).addScaled long (el 3)) &&
    got ((short.scaled (el 2)).addScaled long (el 3)) ==
      [6, 7, 8].map (fun (n : Nat) => mulE (ofF n.toUInt64) (addE (el 2) (el 3))) ++ [zeroE])

/-! ## FOLD -/

#guard [(2, 0), (1, 1), (3, 1), (2, 2), (1, 0)].all fun kh =>
  (foldMaskWeights kh.1 kh.2 8 (els kh.1 11).toArray).map E.triple ==
    Fmt.M1.hideVec .two kh.1 kh.2 8 (tr (els kh.1 11))
#guard (foldClaimRound (el 1) (el 2) (el 3) (el 4)).triple ==
  Fmt.M1.nextClaim .two (el 1).triple ((el 2).triple, (el 3).triple) (el 4).triple
#guard (foldLow (els 8 1).toArray (els 2 40)).map E.triple ==
  Fmt.M1.foldLow .two (tr (els 2 40)) (tr (els 8 1)).toArray
#guard (inner (els 5 1).toArray (els 5 9).toArray).triple ==
  Fmt.M1.dot .two (tr (els 5 1)).toArray (tr (els 5 9)).toArray

end OnBytes.TestGround
