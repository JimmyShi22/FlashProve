-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestStagesLinksMore.lean: further tests of OnBytes/Model/StagesLinks.lean.

A test that expects a refusal gives an input that meets every other condition of the function under
test, so that this one condition decides. An input that meets all of them is beside it or in
OnBytes/Model/TestStagesLinks.lean, whose records are used here. The exception is the test of
buildLinksH at the end: its input passes every step before the one that refuses and would fail later
steps too, and no #guard has an input that buildLinksH accepts. Each test is checked when the file
compiles. The program does not import this file.
-/
import OnBytes.Model.TestStagesLinks

namespace OnBytes.Model.Stages.TestLinksMore

open Params (ReqLink ReqMessage ReqArray LaidBlock ReqLayout)
open OnBytes.Model.Stages.Test

/-! ## The order and the declared arrays -/

-- the proof covers attention, which has another number of plans than there are groups
#guard why (listLinksH 1 true #[planG] #[] planG) == "plan-link"
-- an array that has a name already; a number outside the list
#guard (namesH #[(noLink, "")] 0 1 "M1").toOption == some #[(1, "M1")]
#guard why (namesH #[(0, "M0")] 0 1 "M1") == "plan-link"
#guard why (namesH #[] 0 1 "M1") == "plan-link"

/-- The link G0. -/
def linkG : LinkH := links.getD 0 (planG.link "" 0 0 0 true)

/-- The link H. -/
def linkH : LinkH := links.getD 1 (planG.link "" 0 0 0 true)

-- a number that arrayOf has and neither the list nor the plan
#guard why (own linkG 0 { arrayOf := Array.replicate 9 (noLink, ""), moment := #[#[]] } 8 "X") ==
  "plan-link"
-- declareOwn: each of the four conditions alone
#guard why (declareOwn linkG 0) == ""
#guard why (declareOwn
  { linkG with tl := { linkG.tl with pkMat := #[], ix := { linkG.tl.ix with PK := #[] } } } 0) ==
  "plan-link"
#guard why (declareOwn { linkG with tl := { linkG.tl with pkMat := #[0, 5] } } 0) == "plan-link"
#guard why (declareOwn { linkG with tl := { linkG.tl with pxMat := #[1, 5] } } 0) == "plan-link"
#guard why (declareOwn { linkG with tl := { linkG.tl with plFor := #[{}] } } 0) == "plan-link"
-- keptUpTo: no array of this name
#guard why (keptUpTo declaredG "M9" 1) == "plan-fold-source"
#guard why (keptUpTo declaredG "M1" 1) == ""

/-- The head's arrays before the foreign one has its name. -/
def beforeForeign : Array (Nat × String) := #[(1, "M0"), (noLink, ""), (1, "ZZ"), (1, "BZ")]

-- foreign: as it should be
#guard why (foreign links 1 false 1 linkH (beforeForeign, #[declaredG]) 1
  { owner := some 0, rootIndex := some 1 }) == ""
-- the owner's link is not an earlier one, and nothing else is wrong
#guard why (foreign links 1 false 0 linkH (beforeForeign, #[declaredG]) 1
  { owner := some 0, rootIndex := some 1 }) == "plan-fold-source"

/-- Three links: two groups of layers and the head. -/
def three : Array LinkH :=
  ((listLinksH 2 false #[planG, planG] #[] (planH (some 1) (some 1))).toOption).getD #[]

-- the owner is no group of layers by the number of groups, and nothing else is wrong
#guard why (foreign three 2 false 2 linkH (beforeForeign, #[declaredG, declaredG]) 1
  { owner := some 1, rootIndex := some 1 }) == ""
#guard why (foreign three 1 false 2 linkH (beforeForeign, #[declaredG, declaredG]) 1
  { owner := some 1, rootIndex := some 1 }) == "plan-fold-source"
-- the reader works with other rows and the same columns
#guard why (foreign links 1 false 1
  { linkH with Fp := { trees := #[tree 1 2, tree 4 8, tree 5 2, tree 1 32] } }
  (beforeForeign, #[declaredG]) 1 { owner := some 0, rootIndex := some 1 }) == "plan-fold-source"
-- the owner has declared nothing yet
#guard why (foreign links 1 false 1 linkH (beforeForeign, #[]) 1
  { owner := some 0, rootIndex := some 1 }) == "plan-fold-source"
-- the reader's list has no such array; the owner's plan has no array for the matrix
#guard why (foreign links 1 false 1 linkH (beforeForeign, #[declaredG]) 9
  { owner := some 0, rootIndex := some 1 }) == "plan-fold-source"
#guard why (foreign (links.modify 0 fun X => { X with tl := { X.tl with gtTree := #[0] } }) 1 false
  1 linkH (beforeForeign, #[declaredG]) 1 { owner := some 0, rootIndex := some 1 }) ==
  "plan-fold-source"

/-! ## The weight table -/

/-- A unit of nlw digits: two if none is given. -/
def unit (off rows : Nat) (nlw : Nat := 2) : WsUnit := { off := off, rows := rows, nlw := nlw }

#guard wfUnitsOk 8 8 [unit 0 4, unit 4 4]
-- no row; rows that are no multiple of the digits; more rows than are ranged
#guard !wfUnitsOk 8 8 [unit 0 0, unit 0 8]
#guard !wfUnitsOk 8 8 [unit 0 3, unit 3 5]
#guard !wfUnitsOk 16 8 [unit 0 10]
-- three digits
#guard !wfUnitsOk 12 12 [unit 0 12 3]
-- more ranged rows than rows; an odd number of ranged rows; 2^40 rows
#guard !wfUnitsOk 4 8 [unit 0 4, unit 4 4]
#guard !wfUnitsOk 9 9 [unit 0 4, unit 4 4]
#guard !wfUnitsOk (2 ^ 40) 8 [unit 0 4, unit 4 4]
#guard wfUnitsOk (2 ^ 40 - 1) 8 [unit 0 4, unit 4 4]
#guard !wfUnitsOk 8 8 []
-- a gap
#guard !wfUnitsOk 8 8 [unit 0 2, unit 4 4]

/-! ## A given link against its declaration -/

-- messageHeld: four of its seven conditions, each alone
#guard messageHeld false 3 (msg 1 1 0 2 0)
#guard !messageHeld false 3 (msg 0 1 0 2 0)
#guard !messageHeld false 3 (msg (2 ^ 32) 1 0 2 0)
#guard messageHeld false 3 (msg (2 ^ 32 - 1) 1 0 2 0)
#guard !messageHeld false 3 (msg 1 1 0 3 0)
#guard !messageHeld false 3 (msg 1 1 0 2 (2 ^ 20))
#guard messageHeld false 3 (msg 1 1 0 2 (2 ^ 20 - 1))

/-- A block with the four logarithms. -/
def blk4 (a b c d : Nat) : LaidBlock :=
  { firstI := 0, firstC := 0, firstRow := 0, firstPlace := 0, bitsI := a, bitsC := b, rowBits := c,
    placeBits := d, iIsLow := true }

#guard blockHeld (blk4 47 47 47 47)
#guard !blockHeld (blk4 48 0 0 0)
#guard !blockHeld (blk4 0 48 0 0)
#guard !blockHeld (blk4 0 0 48 0)
#guard !blockHeld (blk4 0 0 0 48)
-- arrayHeld: other rows alone; no block; a block that no file can spell
#guard arrayHeld givenG.messages arraysG 0 { name := "M0", rows := 2, columns := 4 }
#guard !arrayHeld givenG.messages arraysG 0 { name := "M0", rows := 3, columns := 4 }
#guard !arrayHeld givenG.messages [{ arr "M0" 0 2 4 with blocks := [] }] 0
  { name := "M0", rows := 2, columns := 4 }
#guard !arrayHeld givenG.messages [{ arr "M0" 0 2 4 with blocks := [blk4 48 0 0 0] }] 0
  { name := "M0", rows := 2, columns := 4 }
-- linkHeld: a moment fewer than declared, with every message and array in order
#guard !linkHeld { declaredG with moment := declaredG.moment.push #[] } givenG arraysG
-- an array twice: the number of arrays is wrong and every name is a declared one
#guard !linkHeld declaredG givenG (arr "M0" 0 2 4 :: arraysG)
-- a name that is declared twice, found once, beside an array that nobody declared
#guard !linkHeld { name := "X", moment := #[#[{ name := "M0", rows := 2, columns := 4 },
    { name := "M0", rows := 2, columns := 4 }]] } ⟨0, [msg 4 1 1 0 0]⟩
  [arr "M0" 0 2 4, arr "X" 0 1 1]
-- heldAgainst: a given link too many, with as many lists of arrays as there are declared links
#guard why (heldAgainst expected (first [givenG, givenH, givenH] [arraysG, arraysH] [1, 2] 2)) ==
  "plan-layout"
-- heldAgainst: a declared link too many
#guard why (heldAgainst (expected.push { name := "X" }) (first [givenG, givenH] [arraysG, arraysH]
  [1, 2] 2)) == "plan-layout"

/-! ## The other given numbers -/

/-- The layout of a weight table that fits the example's given numbers. -/
def fitting : WsLay := { m0 := kitFirst.lin.matrixRows, lk := kitFirst.lin.kCol }

#guard why (tableHeld fitting kitFirst) == ""
#guard why (tableHeld { fitting with m0 := fitting.m0 + 1 } kitFirst) == "parameters-not-admitted"
#guard why (tableHeld { fitting with lk := fitting.lk + 1 } kitFirst) == "parameters-not-admitted"

/-- The example's given numbers with so many bytes for a listed position and one code of length
2^logN. -/
def listing (posB logN : Nat) : Params.First :=
  { kitFirst with
    given := { kitFirst.given with plan := { kitFirst.given.plan with posB := posB } }
    codes := { base := #[{ logN := logN, ell := 1, r := 0 }], mask := #[] } }

#guard why (listedFits (listing 0 60)) == ""
#guard why (listedFits (listing 2 16)) == ""
#guard why (listedFits (listing 2 17)) == "parameters-not-admitted"
#guard why (listedFits (listing 8 70)) == ""

/-! ## One plan, one placement -/

#guard samePlan linkG linkG.Fp linkG.Tp
#guard !samePlan linkG { trees := linkG.Fp.trees.set! 1 (tree 4 8) } linkG.Tp
#guard !samePlan linkG { trees := linkG.Fp.trees.set! 1 (tree 3 9) } linkG.Tp
#guard !samePlan linkG linkG.Fp { linkG.Tp with nt := linkG.Tp.nt.push {} }
#guard placedAlike (some (arr "M0" 0 2 4)) (some (arr "M9" 0 2 4))
#guard !placedAlike (some (arr "M0" 0 2 4)) (some (arr "M0" 1 2 4))
#guard !placedAlike (some (arr "M0" 0 2 4)) (some (arr "M0" 0 3 4))
#guard !placedAlike (some (arr "M0" 0 2 4)) (some (arr "M0" 0 2 5))
#guard !placedAlike (some (arr "M0" 0 2 4)) (some { arr "M0" 0 2 4 with blocks := [] })
#guard !placedAlike none (some (arr "M0" 0 2 4))

-- a link for layers with fewer such arrays, each laid as the first link's
#guard !onePlacement (kitLinks.modify 2 fun X => { X with tl := { X.tl with pxMat := #[6] } })
  ⟨kitLayout⟩

/-! ## Room and life -/

/-- A shape whose one message at the start has so many mask rows under mask code 0. -/
def startShape (rows : Nat) : Params.ReqShape :=
  { kitFirst.shape with atStart := [⟨{ maskRows := rows, maskCode := 0, answers := 1 }, 1⟩] }

/-- Codes with one mask code, of this message length. -/
def maskOf (ell : Nat) : Codes := { base := #[], mask := #[⟨5, ell, 0⟩] }

-- two rows on the table and 1 + 2 * 3 entries for their batching: 9 of the 9 free entries
#guard why (indexMaskRoom links (maskOf 10) (startShape 1) 3) == ""
#guard why (indexMaskRoom links (maskOf 9) (startShape 1) 3) == "plan-mask-row"
#guard why (indexMaskRoom links { base := #[], mask := #[] } (startShape 1) 3) == "plan-mask-row"
#guard why (indexMaskRoom links (maskOf 10) { startShape 1 with atStart := [] } 3) ==
  "parameters-not-admitted"

/-- The example's links with the names of their arrays. -/
def kitNamed : Array LinkH := ((declareLinks kitLinks 2 true).toOption.map (·.1)).getD #[]

/-- The example's shape with the message of M7 of G0 kept for one link, where G1 is two links on. -/
def shortLife : Params.ReqShape :=
  { kitFirst.shape with
    link := kitFirst.shape.link.zipIdx.map fun L =>
      if L.2 == 0 then { L.1 with messages := L.1.messages.set 2 (msg 1 1 0 0 1) } else L.1 }

#guard why (linkLaid kitFirst.shape kitFirst.layout 8192 2 (kitNamed.getD 2 linkG)) == ""
#guard why (linkLaid shortLife kitFirst.layout 8192 2 (kitNamed.getD 2 linkG)) == "plan-layout"
#guard why (linkLaid kitFirst.shape ⟨[]⟩ 8192 2 (kitNamed.getD 2 linkG)) == "plan-layout"
#guard why (linksLaid kitNamed (maskOf 8192) kitFirst.shape kitFirst.layout) == ""
#guard why (linksLaid kitNamed (maskOf 8192) shortLife kitFirst.layout) == "plan-layout"
#guard why (linksLaid kitNamed { base := #[], mask := #[] } kitFirst.shape kitFirst.layout) ==
  "plan-mask-row"

/-- The example's given numbers with a table of eight rows. -/
def eightRows : Params.First := { kitFirst with lin := { kitFirst.lin with matrixRows := 8 } }

-- all that comes before is in order, and the shape is not lawful under the codes, of which there
-- are none
#guard why (buildLinksH kitLinks 2 true
  { m0 := 8, lk := eightRows.lin.kCol, U := #[unit 0 4, unit 4 4] } eightRows) ==
  "parameters-not-admitted"

end OnBytes.Model.Stages.TestLinksMore
