-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/LaidAt.lean: WHERE AN ELEMENT OF A LINK's ARRAY LIES IN ITS ORACLE MESSAGE. Definitions
with code. It imports OnBytes/Params/Items.lean alone, for the plain records of the plan's item
"layout" (`LaidBlock`, `ReqArray`, `ReqLayout`): no function of the programs' port is called.
NOTHING IS PROVED IN THIS FILE.

Why. The witness of the rule of composition holds a message a number: mask row or main row, row,
place ↦ an element (Johnson/Desc/Msg.lean). What a link's law speaks of are the link's arrays:
matrices, by row and column. The plan's item "layout" (layout.txt) says, for every array of every
link, which of the link's oracle messages holds it and in which rectangles of that message's table:
BLOCK BY BLOCK: an array's column may run along a row's places, wrap over rows, and lie in several
rectangles: (row, column) ↦ (row of the message, place) is no shift.
  `laidIn b i c`: where the block b holds the array's element (i, c): by the rule in `LaidBlock`'s
    docstring: the block is the elements (firstI + i', firstC + c') with i' < 2 ^ bitsI, c' < 2 ^
    bitsC; element number x (c' * 2 ^ bitsI + i' if iIsLow, else i' * 2 ^ bitsC + c') is in row
    firstRow + x / 2 ^ placeBits at place firstPlace + x % 2 ^ placeBits. Nothing outside the block.
  `laidAt a i c`: where the array a holds its element (i, c): by its first block that holds it.
  `arrayOf layout l name`: the array of that name among link l's.
  `seatIn layout num l name i c`: **THE SEAT OF AN ELEMENT**: num: A LETTER: the number, in the
    witness, of message k of link l (one number for all copies of a kept message). The message's
    number, its main row, its place.
  `isShift a`: the array lies in one block in which (i, c) ↦ (firstRow + i, firstPlace + c): a test
    for a run.
Limits. That an array's blocks tile it, lie inside their message's rows and places, miss the
sample's pad and overlap nobody is a test of the programs' port on the layout (`reqLayoutOk`,
OnBytes/Iop/ReqRows.lean): not said again here. An array that a later link borrows stands in its
OWNER's link's list: l is the owner's.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Params.Items

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes.Params (LaidBlock ReqArray ReqLayout)

/-- Where the block b holds the array's element (i, c): the message's main row and place. -/
def laidIn (b : LaidBlock) (i c : Nat) : Option (Nat × Nat) :=
  if b.firstI ≤ i ∧ i < b.firstI + 2 ^ b.bitsI ∧ b.firstC ≤ c ∧ c < b.firstC + 2 ^ b.bitsC then
    let x := if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
      else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)
    some (b.firstRow + x / 2 ^ b.placeBits, b.firstPlace + x % 2 ^ b.placeBits)
  else none

/-- Where the array a holds its element (i, c). -/
def laidAt (a : ReqArray) (i c : Nat) : Option (Nat × Nat) :=
  a.blocks.findSome? fun b => laidIn b i c

/-- The array of a name among link l's. -/
def arrayOf (layout : ReqLayout) (l : Nat) (name : String) : Option ReqArray :=
  (layout.link[l]?).bind fun as => as.find? fun a => a.name == name

/-- **The seat of an element**: the message's number in the witness, its main row, its place. -/
def seatIn (layout : ReqLayout) (num : Nat → Nat → Nat) (l : Nat) (name : String) (i c : Nat) :
    Option (Nat × Nat × Nat) :=
  (arrayOf layout l name).bind fun a => (laidAt a i c).map fun x => (num l a.message, x.1, x.2)

/-- The array lies in one block in which (i, c) ↦ (firstRow + i, firstPlace + c). -/
def isShift (a : ReqArray) : Bool :=
  match a.blocks with
  | [b] => !b.iIsLow && b.placeBits == b.bitsC && b.firstI == 0 && b.firstC == 0
  | _ => false

end VerifiableInference.Desc
