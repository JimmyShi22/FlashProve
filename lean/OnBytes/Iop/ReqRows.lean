-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/ReqRows.lean: how the equation in which a sub-proof ends becomes a linear claim on the
oracle messages that hold its data.
C++ counterpart: blocks/iop/req_rows.h; for the first section, blocks/iop/laid.h.

Words. A request's proof is a chain of links; a link is a part of the computation with a sub-proof
of its own, and a link's group is the set of oracle messages whose rows the link's closing batches
and folds (OnBytes/Iop/Req.lean). A row (`Row`, OnBytes/Iop/Ground.lean) is a linear claim with a
public target on the messages of one group; the link's closing takes it in. Other words:
lean/GLOSSARY.md.

A sub-proof thinks in arrays: matrices of committed entries with names. A public layout cuts each
array into aligned blocks whose sides are powers of two, and places each block in an aligned
rectangle of the main rows of one of the link's oracle messages (docs/format/FORMAT.md,
R14.5). A sub-proof ends in one equation with a public target: a sum of terms, each with weights of
rank one on an array, scale * onRows[i] * onColumns[c], and coefficients on the first entries of the
link's mask row. An array may be one that an earlier link has sent and this link still reads.
`ReqRows.row` makes the row of the link's group from such an equation.

An element of an array is an entry of the table as it is committed. Where several cells are packed
into one entry, the array is the matrix of packed entries: no form here can weight a single cell of
a packed entry. Places of a table that no block covers get no coefficient here, so no equation reads
them. The out-of-domain sample of an oracle message (OnBytes/Iop/Send.lean) does read them: it has a
coefficient on every entry of its tables.

Main definitions: `IndexWeights`, `laidBlockOk`, `laidOk`, `laidTensor`, `laidForm`,
`reqLayoutOk`, `ReqTerm`, `ReqEquation`, `ReqRows`, `ReqRows.make`, `ReqRows.row`.

What is not claimed. That an equation's weights, coefficients and target are functions of the
chain's first query, of what was sent and of what was drawn is the duty of whoever makes the
equation. That the layout is the one in the chain's first query is the duty of whoever calls
`ReqRows.make`. No theorem is stated here.
-/
import OnBytes.Iop.Req

namespace OnBytes

open Params (LaidBlock ReqArray ReqLayout ReqShape ReqMessage)

/-! ## A matrix laid out in blocks

A block (`Params.LaidBlock`) holds the elements (firstI + i, firstC + c) of its matrix, for i below
2^bitsI and c below 2^bitsC. Element number x of the block, which is c * 2^bitsI + i if `iIsLow` and
i * 2^bitsC + c otherwise, is in row firstRow + x / 2^placeBits of the table, at place
firstPlace + x % 2^placeBits. -/

/-- True if `first` is below 2^48 and a multiple of 2^bits, with bits below 48. The two bounds are
those of laid.h, which computes in words of 64 bits. -/
def laidAligned (first bits : Nat) : Bool :=
  decide (bits < 48) && decide (first < 2 ^ 48) && first % 2 ^ bits == 0

/-- A block is as large in the table as in its matrix, each of its four first numbers is a multiple
of the block's side there, and it is inside a table of 2^tableRowBits rows of 2^tablePlaceBits
places. -/
def laidBlockOk (b : LaidBlock) (tableRowBits tablePlaceBits : Nat) : Bool :=
  b.rowBits + b.placeBits == b.bitsI + b.bitsC &&
  decide (b.rowBits ≤ tableRowBits) && decide (b.placeBits ≤ tablePlaceBits) &&
  laidAligned b.firstI b.bitsI && laidAligned b.firstC b.bitsC &&
  laidAligned b.firstRow b.rowBits && laidAligned b.firstPlace b.placeBits &&
  decide (b.firstRow < 2 ^ tableRowBits) && decide (b.firstPlace < 2 ^ tablePlaceBits)

/-- True if the stretches of 2^aBits from a and of 2^bBits from b have a number in common. -/
def laidMeet (a aBits b bBits : Nat) : Bool :=
  decide (a < b + 2 ^ bBits) && decide (b < a + 2 ^ aBits)

/-- True if no two members of the list are related by r. -/
def noPair {α : Type} (r : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => (l.all fun b => !r a b) && noPair r l

/-- One matrix is laid out lawfully by itself: every block is aligned and is inside the matrix and
the table, no two blocks share an element, and the blocks cover the matrix. For the cover the
elements are counted: the blocks are disjoint and inside, so the right number is full cover. -/
def laidMatrixOk (a : ReqArray) (tableRowBits tablePlaceBits : Nat) : Bool :=
  (a.blocks.all fun b =>
    laidBlockOk b tableRowBits tablePlaceBits &&
    decide (b.firstI + 2 ^ b.bitsI ≤ a.sizeI) && decide (b.firstC + 2 ^ b.bitsC ≤ a.sizeC)) &&
  noPair (fun (x y : LaidBlock) =>
    laidMeet x.firstI x.bitsI y.firstI y.bitsI && laidMeet x.firstC x.bitsC y.firstC y.bitsC)
    a.blocks &&
  (a.blocks.map fun b => 2 ^ (b.bitsI + b.bitsC)).foldl (· + ·) 0 == a.sizeI * a.sizeC

/-- The matrices are laid out lawfully in one table: each by itself, and no entry of the table holds
two elements. -/
def laidOk (matrices : List ReqArray) (tableRowBits tablePlaceBits : Nat) : Bool :=
  (matrices.all fun a => laidMatrixOk a tableRowBits tablePlaceBits) &&
  noPair (fun (x y : LaidBlock) =>
    laidMeet x.firstRow x.rowBits y.firstRow y.rowBits &&
    laidMeet x.firstPlace x.placeBits y.firstPlace y.placeBits)
    (matrices.flatMap (·.blocks))

/-- Weights on one index of a matrix: the product over the index's bits t of hi[t] or lo[t], as the
bit is 1 or 0; or, if `values` is there, a vector that is written out. With two product forms, or
with one product form and one written-out vector, the weights on a block are one `Tensor`
(OnBytes/Iop/Tensor.lean). Two written-out vectors are refused (`laidTensor`). -/
structure IndexWeights where
  /-- the factor of each bit that is 0, bit 0 first -/
  lo : Array E := #[]
  /-- the factor of each bit that is 1, bit 0 first -/
  hi : Array E := #[]
  /-- the written-out vector, if there is one -/
  values : Option (Array E) := none
  deriving Repr, Inhabited

namespace IndexWeights

/-- True if the weights are a written-out vector. -/
def writtenOut (w : IndexWeights) : Bool := w.values.isSome

/-- A product form has one factor of each kind for each bit. -/
def ok (w : IndexWeights) : Bool := w.lo.size == w.hi.size

/-- The equality weights at a point. Coordinate t belongs to bit t of the index. -/
def eq (point : Array E) : IndexWeights :=
  { lo := point.map fun z => subE oneE z, hi := point }

/-- The squares base, base^2, base^4, and so on: as many as `bits`. -/
def squares : Nat → E → List E
  | 0, _ => []
  | bits + 1, x => x :: squares bits (mulE x x)

/-- Index i gets base^i, for i below 2^bits. -/
def powers (base : E) (bits : Nat) : IndexWeights :=
  { lo := Array.replicate bits oneE, hi := (squares bits base).toArray }

/-- A vector that is written out. -/
def written (values : Array E) : IndexWeights := { values := some values }

/-- The product of the weights' factors for the bits of `first` from `bits` on: above a block's side
an index's bits are those of the block's first element. 1 for a written-out vector. Returns nothing
if the product form has too few bits for the index. As in laid.h, where an index is a word of 64
bits, that test is made only for a form of fewer than 64 bits. -/
def above (w : IndexWeights) (first bits : Nat) : Option E :=
  if w.writtenOut then some oneE
  else if w.lo.size < 64 && first / 2 ^ w.lo.size != 0 then none
  else
    some (((List.range w.lo.size).drop bits).foldl
      (fun s i => mulE s (if first / 2 ^ i % 2 == 1 then w.hi.getD i zeroE else w.lo.getD i zeroE))
      oneE)

end IndexWeights

/-- A tensor under construction, with the dense variables noted as (bit of the written-out
vector's index, variable). -/
structure LaidDraft where
  t : Tensor
  dense : List (Nat × Nat) := []

/-- Appends the variable that carries bit xBit of the element's number within the block. -/
def LaidDraft.pushBit (d : LaidDraft) (b : LaidBlock) (onI onC : IndexWeights) (xBit : Nat) :
    Option LaidDraft :=
  let lowBits := if b.iIsLow then b.bitsI else b.bitsC
  let ofI := decide (xBit < lowBits) == b.iIsLow
  let bit := if xBit < lowBits then xBit else xBit - lowBits
  let w := if ofI then onI else onC
  if w.writtenOut then some { t := d.t.push oneE oneE, dense := d.dense ++ [(bit, d.t.vars)] }
  else
    match w.lo[bit]?, w.hi[bit]? with
    | some l, some h => some { d with t := d.t.push l h }
    | _, _ => none

/-- Appends the variables of several bits, in their order. -/
def LaidDraft.pushBits (d : LaidDraft) (b : LaidBlock) (onI onC : IndexWeights) :
    List Nat → Option LaidDraft
  | [] => some d
  | x :: xs => (d.pushBit b onI onC x).bind fun e => e.pushBits b onI onC xs

/-- scalar * onI[i] * onC[c] on the block's elements and 0 elsewhere, as a tensor on a table of
2^tableRowBits rows of 2^tablePlaceBits places. Returns nothing if the block does not fit the table,
if both weights are written out, if the weights do not fit the block, or if the lists lo and hi of a
product form differ in length. -/
def laidTensor (b : LaidBlock) (tableRowBits tablePlaceBits : Nat) (onI onC : IndexWeights)
    (scalar : E) : Option Tensor := do
  if !laidBlockOk b tableRowBits tablePlaceBits || (onI.writtenOut && onC.writtenOut) ||
      !onI.ok || !onC.ok then none
  -- the low row bits carry the high bits of the element's number
  let d ← LaidDraft.pushBits { t := { scalar := scalar } } b onI onC
    ((List.range b.rowBits).map (· + b.placeBits))
  let d := { d with
    t := d.t.insertChoice d.t.vars (tableRowBits - b.rowBits) (b.firstRow / 2 ^ b.rowBits) }
  -- the low place bits carry the low bits of the element's number
  let d ← d.pushBits b onI onC (List.range b.placeBits)
  let t := d.t.insertChoice d.t.vars (tablePlaceBits - b.placeBits)
    (b.firstPlace / 2 ^ b.placeBits)
  let t := (t.scale (← onI.above b.firstI b.bitsI)).scale (← onC.above b.firstC b.bitsC)
  let t ←
    match (if onI.writtenOut then onI.values else onC.values) with
    | none => some t
    | some values =>
      let first := if onI.writtenOut then b.firstI else b.firstC
      if d.dense.isEmpty then (values[first]?).map t.scale
      else
        let vars := (List.range d.dense.length).map fun i =>
          ((d.dense.find? fun x => x.1 == i).map (·.2)).getD 0
        some ({ t with denseVars := vars }.setValues values first)
  if t.ok then some t else none

/-- scalar * onI[i] * onC[c] on every element of a matrix: the sum of `laidTensor` over its
blocks. -/
def laidForm (blocks : List LaidBlock) (tableRowBits tablePlaceBits : Nat)
    (onI onC : IndexWeights) (scalar : E) : Option Form :=
  blocks.foldlM
    (fun (f : Form) b => (laidTensor b tableRowBits tablePlaceBits onI onC scalar).map f.add) {}

/-! ## The layout of a request's arrays -/

/-- The array of a name among the arrays of link l. -/
def reqArray (layout : ReqLayout) (l : Nat) (name : String) : Option ReqArray :=
  (layout.link[l]?).bind fun arrays => arrays.find? fun a => a.name == name

/-- What an array shows by itself: a name, at least one element, fewer than 2^48 rows and columns,
at least one block, and blocks that are aligned and as large in the table as in the matrix. -/
def reqArrayOk (a : ReqArray) : Bool :=
  !a.name.isEmpty && a.sizeI != 0 && a.sizeC != 0 &&
  decide (a.sizeI < 2 ^ 48) && decide (a.sizeC < 2 ^ 48) && !a.blocks.isEmpty &&
  a.blocks.all fun b =>
    b.rowBits + b.placeBits == b.bitsI + b.bitsC &&
    laidAligned b.firstI b.bitsI && laidAligned b.firstC b.bitsC &&
    laidAligned b.firstRow b.rowBits && laidAligned b.firstPlace b.placeBits

/-- True if the block covers the entry `index` of a table with 2^rowBits rows. -/
def laidCovers (b : LaidBlock) (rowBits index : Nat) : Bool :=
  let row := index % 2 ^ rowBits
  let place := index / 2 ^ rowBits
  decide (b.firstRow ≤ row) && decide (row < b.firstRow + 2 ^ b.rowBits) &&
  decide (b.firstPlace ≤ place) && decide (place < b.firstPlace + 2 ^ b.placeBits)

/-- The arrays that are in one oracle message fit it: it has main rows; the blocks are aligned,
disjoint, inside the table and cover their arrays; no block is in rows that are not sent; none
covers the pad of the message's sample, since no claim may read a pad. -/
def reqMessageLayoutOk (codes : Codes) (o : OracleShape) (inIt : List ReqArray) : Bool :=
  inIt.isEmpty ||
  (o.mainRows != 0 &&
   match codes.base[o.code]?, Send.pad codes o with
   | some c, some pad =>
     let rowBits := ceilLog2 o.mainRows
     laidOk inIt rowBits c.logEll &&
     (inIt.flatMap (·.blocks)).all fun b =>
       decide (b.firstRow + 2 ^ b.rowBits ≤ o.mainRows) &&
       pad.all fun p => p.part != .main || !laidCovers b rowBits p.index
   | _, _ => false)

/-- The layout is lawful for the request's shape under the codes. A layout is input to a verifier:
this is the test that it must pass first. -/
def reqLayoutOk (codes : Codes) (s : ReqShape) (layout : ReqLayout) : Bool :=
  layout.link.length == s.link.length &&
  (zipT s.link layout.link).all fun x =>
    let messages := x.1.messages
    x.2.all reqArrayOk &&
    (x.2.all fun a => decide (a.message < messages.length)) &&
    noPair (fun (a b : ReqArray) => a.name == b.name) x.2 &&
    messages.zipIdx.all fun m =>
      reqMessageLayoutOk codes m.1.shape (x.2.filter fun a => a.message == m.2)

/-! ## A link's equation -/

/-- scale * onRows[i] * onColumns[c] on element (i, c) of an array. -/
structure ReqTerm where
  /-- the link that sent the array, counted from 0: the present one or an earlier one -/
  born : Nat := 0
  /-- the array's name in the layout -/
  array : String := ""
  /-- the factor before both weights -/
  scale : E := oneE
  /-- the weights on the array's rows; at most one of the two weights is written out -/
  onRows : IndexWeights := {}
  /-- the weights on the array's columns -/
  onColumns : IndexWeights := {}
  deriving Repr, Inhabited

/-- The one equation in which a link's sub-proof ends. -/
structure ReqEquation where
  /-- the weights on the committed arrays -/
  terms : Array ReqTerm := #[]
  /-- the coefficients on the first entries of the link's mask row -/
  onMasks : Array E := #[]
  /-- the public target -/
  target : E := zeroE
  deriving Repr, Inhabited

/-- A layout for `ReqRows.row`. `ReqRows.make` returns one that has passed `reqLayoutOk`. Lean does
not enforce that way: the constructor is open, and a caller that builds the structure itself skips
the test. (In req_rows.h the test is in the one constructor.) -/
structure ReqRows where
  layout : ReqLayout

/-- Compares the layout with the request's shape and the statement's codes (`reqLayoutOk`). Not
tested here: that the layout is the one in the chain's first query. -/
def ReqRows.make (shape : ReqShape) (layout : ReqLayout) : Blk ReqRows := do
  let S ← Blk.statement
  Blk.must (reqLayoutOk S.codes shape layout)
  pure ⟨layout⟩

/-- The sum of an equation's terms as forms on oracle messages, added to a row. -/
def ReqRows.addTerms (R : ReqRows) (f : ReqFrame) (S : Statement) : List ReqTerm → Row →
    Option Row
  | [], row => some row
  | t :: ts, row => do
    let a ← reqArray R.layout t.born t.array
    let o ← f.whereIs t.born a.message
    let c ← laidForm a.blocks (S.rowBits o .main) (S.placeBits o .main) t.onRows t.onColumns
      t.scale
    R.addTerms f S ts (row.addForm o c)

/-- The present link's equation as a row on its group. All oracle messages that it names have been
sent. If the equation has coefficients on masks, the link's mask row is the link's first oracle
message with mask rows, which must have exactly one. The mask entries that the equation names are
taken from that row's ledger here, all at once: a sub-proof that numbers its masks itself (entry i
masks its scalar number i) takes none from the ledger before, and the call fails if it has. -/
def ReqRows.row (R : ReqRows) (f : ReqFrame) (eq : ReqEquation) : Blk Row := do
  let S ← Blk.statement
  let row ← Blk.get (R.addTerms f S eq.terms.toList {})
  if eq.onMasks.isEmpty then pure { row with target := eq.target }
  else
    let messages := (f.shape.link[f.link]?.map (·.messages)).getD []
    let m ← Blk.get (messages.findIdx? fun x => x.shape.maskRows != 0)
    Blk.must ((messages[m]?.map (·.shape.maskRows)) == some 1)
    let o ← Blk.get (f.whereIs f.link m)
    let taken ← Blk.takeMasks o eq.onMasks.size
    Blk.must (taken.head? == some 0 && taken.getLast? == some (taken.length - 1))
    pure { row.addRun o .mask 0 1 (.own eq.onMasks) with target := eq.target }

end OnBytes
