-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Lay.lean (kind K9): DEFINITIONS WITH CODE; NO THEOREM: HOW THE TERMS OF THE
ONE EQUATION BECOME A ROW ON THE SEGMENT's ORACLE MESSAGES, IN THE KIND's OWN WORDS. Every test
bears a name; no function of the program `verify-on-bytes` that can refuse is called.

The one equation speaks of arrays: matrices of committed entries, by name. A term is
scale * onRows[i] * onColumns[c] on the elements (i, c) of one array. A public layout cuts each
array into aligned blocks whose sides are powers of two and places each block in an aligned
rectangle of the main rows of one oracle message. So a term becomes, block by block, a vector of
product form on that message's table (a Tensor), and the sum of these a Form; a Row gathers a Form
for each message.
A BLOCK holds the elements (firstI + i, firstC + c), i below 2^bitsI, c below 2^bitsC. Element
number x of the block (c * 2^bitsI + i if iIsLow, else i * 2^bitsC + c) lies in row
firstRow + x / 2^placeBits of the table, at place firstPlace + x % 2^placeBits.
WEIGHTS ON AN INDEX (IndexWeights) are a product over the index's bits t of hi[t] or lo[t], or a
vector that is written out. At most one of a term's two weights is written out.

Main names:
  Ans, need, there     an answer or the name of the test that refused.
  everyBelow n p       p holds at every number below n.
  arrayLaid            the layout has an array of this name and size in that segment.
  rowFormFits X r      a virtual row's product form is well formed for the array X.
  messageNow f born m  which oracle message of the present segment holds the rows of message m of
                       segment born: itself, or what took its rows at the last switch.
  blockTensor          a term on one block. blocksForm: on all blocks of an array.
  termsRow             **the terms, added to a row.**

AGAINST `verify-on-bytes`: everyBelow = allBelow (OnBytes/Model/FormF.lean) · arrayLaid = laidAs ·
rowFormFits = rowFormOK (OnBytes/Model/Trees.lean) · messageNow = ReqFrame.whereIs
(OnBytes/Iop/Req.lean) · aligned, blockFits, aboveBlock, bitVar, bitVars, blockTensor, blocksForm,
termsRow = laidAligned, laidBlockOk, IndexWeights.above, LaidDraft.pushBit, pushBits, laidTensor,
laidForm, ReqRows.addTerms (OnBytes/Iop/ReqRows.lean) · tensorFits, noTwice = Tensor.ok,
distinctNats (OnBytes/Iop/Tensor.lean): the same tests and the same values. HOW THAT IS KNOWN: by
reading; a theorem of agreement is another file's. The records (Tensor, Form, Row, LaidDraft,
IndexWeights, ReqTerm, ReqFrame, Statement) and the functions on them that cannot refuse
(Tensor.push, insertChoice, scale, setValues, vars; Form.add; Row.addForm; Statement.rowBits,
placeBits; clog2) are the library's and are called by name.

-/
import OnBytes.Model.Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray ReqLayout)

/-- An answer, or the name of the test that refused. -/
abbrev Ans (α : Type) : Type := Except String α

/-- A test, under its name. -/
def need (name : String) (b : Bool) : Ans Unit := if b then .ok () else .error name

/-- A value that must be there, under the name of the test that it is. -/
def there {α : Type} (name : String) : Option α → Ans α
  | some x => .ok x
  | none => .error name

/-! ## Small tests -/

/-- p holds at i, i + 1, .., i + count - 1. It builds no list. -/
def everyFrom (p : Nat → Bool) : (count i : Nat) → Bool
  | 0, _ => true
  | count + 1, i => p i && everyFrom p count (i + 1)

/-- p holds at every number below n. -/
def everyBelow (n : Nat) (p : Nat → Bool) : Bool := everyFrom p n 0

/-- The layout has an array of this name in segment born, with R rows and K columns. -/
def arrayLaid (layout : ReqLayout) (born : Nat) (name : String) (R K : Nat) : Bool :=
  ((layout.link.getD born []).find? fun A => A.name == name).any fun A =>
    A.sizeI == R && A.sizeC == K

/-- A virtual row's product form is well formed for X. -/
def rowFormFits (X : HTree) (r : HRow) : Bool :=
  let bits := clog2 X.R
  let np := r.rowPoint.size
  let given := !r.rowLo.isEmpty || !r.rowHi.isEmpty
  decide (np ≤ bits) && !((r.rowOnes || given) && (np != 0 || r.rowFirst != 0)) &&
    r.rowFirst % 2 ^ np == 0 && decide (r.rowFirst < X.R) &&
    !(given && (r.rowOnes || r.rowLo.size != bits || r.rowHi.size != bits))

/-- Which oracle message of the present segment holds the rows of the message that was sent as
number `message` of segment `born`. Nothing if no segment is under way, if the message's moment is
still to come, or if the present segment does not read it. -/
def messageNow (f : ReqFrame) (born message : Nat) : Option Nat :=
  if f.next != .laterOrClose then none
  else if born == f.link then f.own[message]?
  else ((f.groups.getD f.link {}).born.idxOf? (born, message)).bind fun i => f.keptBefore[i]?

/-! ## A term on one block -/

/-- `first` is below 2^48 and a multiple of 2^bits, with bits below 48. -/
def aligned (first bits : Nat) : Bool :=
  decide (bits < 48) && decide (first < 2 ^ 48) && first % 2 ^ bits == 0

/-- A block is as large in the table as in its matrix, each of its four first numbers is a multiple
of the block's side there, and it is inside a table of 2^tableRowBits rows of 2^tablePlaceBits
places. -/
def blockFits (b : LaidBlock) (tableRowBits tablePlaceBits : Nat) : Bool :=
  b.rowBits + b.placeBits == b.bitsI + b.bitsC &&
  decide (b.rowBits ≤ tableRowBits) && decide (b.placeBits ≤ tablePlaceBits) &&
  aligned b.firstI b.bitsI && aligned b.firstC b.bitsC &&
  aligned b.firstRow b.rowBits && aligned b.firstPlace b.placeBits &&
  decide (b.firstRow < 2 ^ tableRowBits) && decide (b.firstPlace < 2 ^ tablePlaceBits)

/-- The product of the weights' factors for the bits of `first` from `bits` on: above a block's side
an index's bits are those of the block's first element. 1 for a written-out vector. A product form
of fewer than 64 bits must have bits enough for the index. -/
def aboveBlock (w : IndexWeights) (first bits : Nat) : Ans E :=
  if w.values.isSome then pure oneE
  else do
    need "K9.weights-reach-the-index" !(decide (w.lo.size < 64) && first / 2 ^ w.lo.size != 0)
    pure (((List.range w.lo.size).drop bits).foldl
      (fun s i => mulE s (if first / 2 ^ i % 2 == 1 then w.hi.getD i zeroE else w.lo.getD i zeroE))
      oneE)

/-- One more variable: that which carries bit xBit of the element's number within the block. -/
def bitVar (d : LaidDraft) (b : LaidBlock) (onI onC : IndexWeights) (xBit : Nat) : Ans LaidDraft :=
  let lowBits := if b.iIsLow then b.bitsI else b.bitsC
  let ofI := decide (xBit < lowBits) == b.iIsLow
  let bit := if xBit < lowBits then xBit else xBit - lowBits
  let w := if ofI then onI else onC
  if w.values.isSome then
    pure { t := d.t.push oneE oneE, dense := d.dense ++ [(bit, d.t.vars)] }
  else
    match w.lo[bit]?, w.hi[bit]? with
    | some l, some h => pure { d with t := d.t.push l h }
    | _, _ => .error "K9.weights-have-the-bit"

/-- The variables of several bits, in their order. -/
def bitVars (d : LaidDraft) (b : LaidBlock) (onI onC : IndexWeights) : List Nat → Ans LaidDraft
  | [] => pure d
  | x :: xs => (bitVar d b onI onC x).bind fun e => bitVars e b onI onC xs

/-- No number stands twice in the list. -/
def noTwice : List Nat → Bool
  | [] => true
  | a :: l => !l.contains a && noTwice l

/-- A tensor has at most 63 variables; the written-out slice lies inside its vector; each dense
variable exists, has the pair (1, 1) and is named once. -/
def tensorFits (v : Tensor) : Bool :=
  decide (v.vars ≤ 63) &&
  (v.denseVars.isEmpty || decide (v.first + 2 ^ v.denseVars.length ≤ v.values.size)) &&
  (v.denseVars.all fun d => v.pairs[d]? == some (oneE, oneE)) &&
  noTwice v.denseVars

/-- scalar * onI[i] * onC[c] on the block's elements and 0 elsewhere, as a tensor on a table of
2^tableRowBits rows of 2^tablePlaceBits places. -/
def blockTensor (b : LaidBlock) (tableRowBits tablePlaceBits : Nat) (onI onC : IndexWeights)
    (scalar : E) : Ans Tensor := do
  need "K9.block-fits-the-table" (blockFits b tableRowBits tablePlaceBits)
  need "K9.one-vector-written-out" !(onI.values.isSome && onC.values.isSome)
  need "K9.weights-in-pairs" (onI.lo.size == onI.hi.size && onC.lo.size == onC.hi.size)
  -- the low row bits carry the high bits of the element's number
  let d ← bitVars { t := { scalar := scalar } } b onI onC
    ((List.range b.rowBits).map (· + b.placeBits))
  let d := { d with
    t := d.t.insertChoice d.t.vars (tableRowBits - b.rowBits) (b.firstRow / 2 ^ b.rowBits) }
  -- the low place bits carry the low bits of the element's number
  let d ← bitVars d b onI onC (List.range b.placeBits)
  let t := d.t.insertChoice d.t.vars (tablePlaceBits - b.placeBits)
    (b.firstPlace / 2 ^ b.placeBits)
  let aI ← aboveBlock onI b.firstI b.bitsI
  let aC ← aboveBlock onC b.firstC b.bitsC
  let t := (t.scale aI).scale aC
  let t ←
    match (if onI.values.isSome then onI.values else onC.values) with
    | none => pure t
    | some values =>
      let first := if onI.values.isSome then b.firstI else b.firstC
      if d.dense.isEmpty then (there "K9.written-value-there" values[first]?).map t.scale
      else
        let vars := (List.range d.dense.length).map fun i =>
          ((d.dense.find? fun x => x.1 == i).map (·.2)).getD 0
        pure ({ t with denseVars := vars }.setValues values first)
  need "K9.tensor-fits" (tensorFits t)
  pure t

/-- scalar * onI[i] * onC[c] on every element of a matrix: the sum over its blocks. -/
def blocksForm (blocks : List LaidBlock) (tableRowBits tablePlaceBits : Nat)
    (onI onC : IndexWeights) (scalar : E) : Ans Form :=
  blocks.foldlM
    (fun (f : Form) b => (blockTensor b tableRowBits tablePlaceBits onI onC scalar).map f.add) {}

/-! ## The terms as a row -/

/-- **The sum of an equation's terms as forms on oracle messages, added to a row.** -/
def termsRow (layout : ReqLayout) (f : ReqFrame) (S : Statement) : List ReqTerm → Row → Ans Row
  | [], row => pure row
  | t :: ts, row => do
    let a ← there "K9.array-in-the-layout"
      ((layout.link[t.born]?).bind fun arrays => arrays.find? fun a => a.name == t.array)
    let o ← there "K9.message-read-here" (messageNow f t.born a.message)
    let c ← blocksForm a.blocks (S.rowBits o .main) (S.placeBits o .main) t.onRows t.onColumns
      t.scale
    termsRow layout f S ts (row.addForm o c)

end VerifiableInference.Desc.K9
