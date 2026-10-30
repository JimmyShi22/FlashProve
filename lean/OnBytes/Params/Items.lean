-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Items.lean: the parameter items of the chains, as records, with their readers.

After the plan and the digest of the public files, a chain's parameter bytes hold named items: the
codes and the shapes of the protocol (the format pages, rules R12.x to R14.x;
docs/format/README.md has their index). An item's value is a sequence of words of eight bytes;
a list has the word of its length in front. The one exception is an array's name in the item
"layout": the word of its length, then that many bytes.
This file has one record for each kind of item, with the fields in the order of the bytes, and one
reader for each record. The fields have the names of the C++ structs (blocks/iop/), in Lean's
spelling. Two kinds of members of the C++ structs are not among the bytes and are no fields here:
the names that serve prints alone, and the distances of a stored table. The bytes are those that
the overload `public_bytes` beside each struct writes.

Two words have two meanings each. "The link" (`LinkShape`) is the item of the block LINK, which
compares a further stored table with the first one; a link of a request (`ReqLink`) is a part of
the computation with a sub-proof of its own. A row is a row of a table or of an oracle message;
in the item "pending rows" it is a linear claim on the matrix that the table stores.

The readers are strict. A word that says yes or no is 0 or 1. An element of the base field is
below the prime. A name's bytes lie in 0x20 to 0x7E. An oracle message's shape has one spelling.
Bytes that are left over are refused.
What a reader does not test: whether a shape's numbers fit each other or the codes. The C++ asks
the first in `public_fault` beside each struct, before a value is bound (blocks/chain/public.h),
and the second at the entry point that takes the shape and the codes. Here the block that uses a
shape tests both (`linOk`, `ioppOk`, `reqOk`, `linkOk` in OnBytes/Iop/).

The size of the matrix is no field of `WfPublic`. It is written once, in `LinShape`, the shape of
the test that takes over the claims which the ranges leave. Written in both records, the two
numbers could differ: ranges that count one row fewer than the test would leave that row without
a lookup, and every check would pass.

Main definitions: `IoppStage`, `IoppChoice`, `IndexShape`, `FoldeqShape`, `LinShape`, `LinkShape`,
`LinBindingShape`, `WfPublic`, `ReqShape`, `ReqLayout`, and `readCodes`, `readNotice`,
`readStages`, `readLin`, `readLink`, `readBinding`, `readRanges`, `readReq`, `readLayout`,
`readFlag`, `readWords`, `readWord`.
-/
import OnBytes.Chain.Lists
import OnBytes.Chain.Loops
import OnBytes.Iop.Ground

namespace OnBytes.Params

/-! ## The records -/

/-- A stage of a proximity test. -/
structure IoppStage where
  /-- the number of its code among the base codes -/
  code : Nat
  /-- the number of its mask code among the mask codes -/
  maskCode : Nat
  /-- it has 2 ^ k main rows -/
  k : Nat
  /-- it has 2 ^ h mask rows -/
  h : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The choices of a proximity test. How many answers the sample of a new stage's oracle message
gets is no choice here: that number is among the plan's eight words (`Fmt.Plan.samples`). -/
structure IoppChoice where
  /-- whether the masks of the stages from the second on are sent with the stage's oracle message,
  in the prover's message of the code switch (block CS) that makes the stage; if not, in the first
  message of their own block -/
  masksRide : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The shape of a stored table: a committed table whose tree is made once and read by many runs
(blocks/iop/foldeq.h). Its rows are over the base field. Two things are no fields. The number of
its tree is 0 for every stored table. The distances at which the table was tested, a member of
the C++ struct, are not among the bytes. -/
structure IndexShape where
  /-- the code of its rows. The last 3 * answers entries of a row's message are its pads, one
  element of the extension field for each stored answer; `code.ell` counts them -/
  code : Code
  /-- the table has 2 ^ v rows -/
  v : Nat
  /-- how many answers to the table's own out-of-domain sample are stored for each row. The
  stored answers of all rows are the table's record -/
  answers : Nat
  /-- the bytes of a leaf's salt -/
  saltBytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The shape of the step that folds a stored table's rows. -/
structure FoldeqShape where
  /-- the table -/
  index : IndexShape
  /-- the oracle message that holds the folded row -/
  u : OracleShape
  /-- how a vector lies in the main rows of `u`. True: a row holds consecutive entries, so the
  row's index is in the high bits of an entry's number. False: it is in the low bits -/
  rowsHigh : Bool
  /-- the class of leaves of `u` -/
  leafClass : Nat
  /-- how many columns of the table a proof draws; the plan has the same number -/
  columns : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The item "the test on the table": the shape of the block LIN, the test of linear claims of many
requests on one stored table with one fold of the table (blocks/iop/lin.h). -/
structure LinShape where
  fold : FoldeqShape
  /-- a row of the table holds 2 ^ kLo columns of the matrix M that the table stores, so M has
  2 ^ (kLo + fold.index.v) columns -/
  kLo : Nat
  /-- the number of rows of M -/
  matrixRows : Nat
  /-- the oracle message Omega: M times the equality vector of the batch's shared point, one entry
  for each row of M -/
  omega : OracleShape
  /-- the oracle message W of a request: the request's row weights times M, one entry for each
  column of M -/
  w : OracleShape
  omegaRowsHigh : Bool
  wRowsHigh : Bool
  /-- the mask message of the shared split: mask rows only. It is sent only where the codes of
  `fold.u` and `omega` differ. The bytes may spell it also where it is not sent (format page,
  R13.13) -/
  sharedSplit : OracleShape
  /-- the mask message of a request's split: mask rows only, sent only where the codes of `w` and
  `omega` differ -/
  ownSplit : OracleShape
  omegaLeafClass : Nat
  sharedSplitLeafClass : Nat
  wLeafClass : Nat
  ownSplitLeafClass : Nat
  /-- the mask code of the shared group -/
  sharedMaskCode : Nat
  /-- the mask code of a request's own group -/
  ownMaskCode : Nat
  /-- whether the fresh mask of a test's first fold is sent ahead: for `testU` with `fold.u`, for
  `testOwn` with `w`, in that message's tree -/
  masksAhead : Bool
  /-- the stages, all of them, of the test on the group of `fold.u`. Omega is in that group where
  the codes of `fold.u` and `omega` agree -/
  testU : List IoppStage
  /-- the test on Omega's own group, made only where the codes of `fold.u` and `omega` differ. A
  test that is not made is the empty list -/
  testOmega : List IoppStage
  /-- the test on a request's own group, which holds `w`. Omega is in that group where the codes
  of `w` and `omega` agree -/
  testOwn : List IoppStage
  /-- the test on a request's group around Omega, made only where the codes of `w` and `omega`
  differ; else the empty list -/
  testOwnOmega : List IoppStage
  choice : IoppChoice
  deriving DecidableEq, Repr, Inhabited

/-- The logarithm of the number of the matrix's columns. -/
def LinShape.kCol (S : LinShape) : Nat := S.kLo + S.fold.index.v

/-- The item "the link": the shape of the block LINK, which is meant to show that a further stored
table holds the same entries as the first (blocks/iop/link.h). -/
structure LinkShape where
  /-- the one shape of the first table and of all copies -/
  table : IndexShape
  /-- how many columns of the first table are drawn -/
  columnsFirst : Nat
  /-- how many columns of the further table are drawn -/
  columnsFurther : Nat
  /-- the number of the code of the one group, which holds the two tables' folded rows -/
  code : Nat
  /-- the number of the mask code of the group of the two folded rows -/
  maskCode : Nat
  /-- the main rows of an oracle message that holds a folded row -/
  rows : Nat
  rowsHigh : Bool
  leafClass : Nat
  masksAhead : Bool
  /-- the stages of the proximity test from the second on. The first is the group of the two
  folded rows and follows from `code`, `maskCode` and `rows` -/
  later : List IoppStage
  choice : IoppChoice
  deriving DecidableEq, Repr, Inhabited

/-- The item "binding tree": the shape of the tree over the seals of a batch's requests
(blocks/iop/lin.h). -/
structure LinBindingShape where
  /-- the depth of the tree; its leaves, the seals of the requests' first chains, are salted -/
  logLeaves : Nat
  /-- the bytes of a leaf's salt -/
  saltBytes : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A run of places of a lookup's part (blocks/iop/wf.h). A place stands for one key in each
column of the matrix; a key has one digit from each of the place's rows. `firstRow` is the
matrix's row of digit 0 of the run's first place. -/
structure WfRun where
  firstPlace : Nat
  firstRow : Nat
  places : Nat
  /-- from a digit's row to the next digit's -/
  stride : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A part of a lookup: 2 ^ logPlaces places and its runs, by rising places and without overlap.
A place in no run is padding. The reader tests neither the order nor the overlap. -/
structure WfPart where
  logPlaces : Nat
  runs : List WfRun
  deriving DecidableEq, Repr, Inhabited

/-- One lookup of the item "ranges". `firstBound` lists the variables that the first rounds of
the last key level bind, in that order, in every part; the others follow from the highest down.
The name in the C++ struct is for prints and is not among the bytes. -/
structure WfLookup where
  /-- the range table is 0 .. 2 ^ d - 1 -/
  d : Nat
  /-- a multiplicity is written in bits, one plane for each bit: there are 2 ^ mu plane slots -/
  mu : Nat
  /-- how many of the slots are real; 0: all -/
  live : Nat
  /-- one weight for each of a place's rows -/
  digitWeight : List F
  offset : F
  /-- what a place of padding holds -/
  paddingKey : F
  parts : List WfPart
  firstBound : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- The item "ranges": the lookups by which a key is meant to show that the table's entries are in
their ranges (blocks/iop/wf.h). The matrix's size is no field: see the head. -/
structure WfPublic where
  lookups : List WfLookup
  /-- the oracle message of the multiplicities and masks -/
  message : OracleNotice
  /-- its number among the oracle messages of its chain -/
  messageId : Nat
  /-- the block's own proximity test, all stages -/
  stages : List IoppStage
  choice : IoppChoice
  deriving DecidableEq, Repr, Inhabited

/-- An oracle message of a link. The bytes hold its rows and the degree of its main rows. Its
codes and its answers are the chain's, and the reader fills them in: the word for "no code" where
it has no rows of a kind. -/
structure ReqMessage where
  shape : OracleShape
  leafClass : Nat
  /-- in which of its link's prover's messages it is sent, counted from 0 -/
  moment : Nat
  /-- its main rows are kept for so many later links: the last link that reads them is this far
  on -/
  life : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A link of a request: a part of the computation with a sub-proof of its own (blocks/iop/req.h).
The record holds the number of its plain scalars and its oracle messages, by moment. -/
structure ReqLink where
  /-- how many plain scalars are sent in a round of their own right before the link's first
  prover's message: something public that the prover can name only then, such as the reply -/
  plain : Nat
  messages : List ReqMessage
  deriving DecidableEq, Repr, Inhabited

/-- A chain of links: the item "request's shape" of a proof, and the item "the chain of links" of
the toy run "links" (format page, R12.15). -/
structure ReqShape where
  /-- the number of the code of every link's group -/
  code : Nat
  /-- the number of their mask code -/
  maskCode : Nat
  link : List ReqLink
  /-- the oracle messages that are sent in the very first prover's message and belong to no link's
  group. They are read at other lists of positions than the links' messages, so their classes of
  leaves must differ from the links'; the reader does not test that -/
  atStart : List OracleNotice
  /-- the answers to the sample of a carrying oracle message: the message that encodes the fold of
  a link's group anew and is sent with the next link or, after the last link, before the last
  test. The plan's sixth word holds this number too; the reader does not compare the two -/
  answers : Nat
  /-- the stages of the last proximity test. The bytes hold them from the second on. The first is
  the group of the last carrying oracle message, under the chain's two codes, with k = 1 and
  h = 0; the reader puts it in front. -/
  last : List IoppStage
  choice : IoppChoice
  deriving DecidableEq, Repr, Inhabited

/-- A block of an array and the rectangle of an oracle message's table that holds it
(blocks/iop/laid.h). The block is the elements (firstI + i, firstC + c) with i < 2 ^ bitsI and
c < 2 ^ bitsC. Element number x, which is c * 2 ^ bitsI + i if `iIsLow` and i * 2 ^ bitsC + c if
not, is in row firstRow + x / 2 ^ placeBits at place firstPlace + x % 2 ^ placeBits. -/
structure LaidBlock where
  firstI : Nat
  firstC : Nat
  firstRow : Nat
  firstPlace : Nat
  bitsI : Nat
  bitsC : Nat
  rowBits : Nat
  placeBits : Nat
  /-- whether the array's row index i is in the low bits of an element's number -/
  iIsLow : Bool
  deriving DecidableEq, Repr, Inhabited

/-- An array of a link. -/
structure ReqArray where
  name : String
  /-- which of its link's oracle messages holds it, from 0 -/
  message : Nat
  /-- its rows -/
  sizeI : Nat
  /-- its columns -/
  sizeC : Nat
  blocks : List LaidBlock
  deriving DecidableEq, Repr, Inhabited

/-- The item "layout": the arrays of every link. -/
structure ReqLayout where
  link : List (List ReqArray)
  deriving DecidableEq, Repr, Inhabited

/-! ## Readers -/

/-- A reader of an item's bytes from an offset on: it gives a value and the offset after it, or
refuses. It is `Fmt.Rd` written as a monad, so that readers can be chained in `do` blocks. -/
abbrev Cut : Type → Type := ReaderT ByteArray (StateT Nat Option)

/-- A reader of Fmt/ as a `Cut`. -/
def cut {α : Type} (r : Fmt.Rd α) : Cut α := fun b i => r b i

/-- A `Cut` as a reader of Fmt/. -/
def Cut.rd {α : Type} (c : Cut α) : Fmt.Rd α := fun b i => c b i

/-- Refuses unless t is true. -/
def Cut.demand (t : Bool) : Cut Unit := fun _ i => if t then some ((), i) else none

/-- A word, as a number. -/
def word : Cut Nat := cut fun b i => (Fmt.rdWord b i).map fun x => (x.1.toNat, x.2)

/-- A word that is 0 or 1. -/
def flag : Cut Bool := cut Fmt.rdBool

/-- An element of the base field. -/
def elt : Cut F := cut (Fmt.rdElt .two)

/-- A list: the word of its length, then its members. -/
def listOf {α : Type} (c : Cut α) : Cut (List α) := cut (rdListT c.rd)

/-- The value that c reads from b. Nothing if bytes of b are left over. -/
def Cut.whole {α : Type} (c : Cut α) (b : ByteArray) : Option α := Fmt.whole c.rd b

/-- A code: three words. -/
def code : Cut Code := do
  let n ← word
  let l ← word
  let r ← word
  pure ⟨n, l, r⟩

/-- The codes: the list of the base codes, then the list of the mask codes. -/
def codes : Cut Codes := do
  let a ← listOf code
  let z ← listOf code
  pure ⟨a.toArray, z.toArray⟩

/-- An oracle message's shape: six words, namely code, mask code, main rows, their degree, mask
rows, answers. The degree is 1 or 3. Where it has no main rows the word of its code says "no code"
and the degree is 1. Where it has no mask rows the word of its mask code says "no code". Not
refused here: a shape without any rows, which spells a message that does not exist (format page,
R13.13), and rows whose code's word says "no code". `shapeFaultless` (OnBytes/Iop/Ground.lean) tests
both. -/
def oracleShape : Cut OracleShape := do
  let c ← word
  let z ← word
  let rows ← word
  let deg ← word
  let masks ← word
  let answers ← word
  Cut.demand ((deg == 1 || deg == 3) && (rows != 0 || (c == noId && deg == 1)) &&
    (masks != 0 || z == noId))
  pure { code := c, mainRows := rows, mainDeg := deg, maskRows := masks, maskCode := z,
         answers := answers }

/-- An oracle message's notice: its shape and its class of leaves. -/
def notice : Cut OracleNotice := do
  let s ← oracleShape
  let c ← word
  pure ⟨s, c⟩

/-- A stage: four words. -/
def stage : Cut IoppStage := do
  let c ← word
  let z ← word
  let k ← word
  let h ← word
  pure ⟨c, z, k, h⟩

/-- The choices of a proximity test: one word. -/
def choice : Cut IoppChoice := do
  let r ← flag
  pure ⟨r⟩

/-- A stored table's shape: six words. -/
def indexShape : Cut IndexShape := do
  let c ← code
  let v ← word
  let s ← word
  let y ← word
  pure ⟨c, v, s, y⟩

/-- The shape of the step that folds a table's rows. -/
def foldeqShape : Cut FoldeqShape := do
  let x ← indexShape
  let u ← oracleShape
  let hi ← flag
  let lc ← word
  let n ← word
  pure ⟨x, u, hi, lc, n⟩

/-- The item "the test on the table". -/
def linShape : Cut LinShape := do
  let fold ← foldeqShape
  let kLo ← word
  let matrixRows ← word
  let omega ← oracleShape
  let w ← oracleShape
  let omegaRowsHigh ← flag
  let wRowsHigh ← flag
  let sharedSplit ← oracleShape
  let ownSplit ← oracleShape
  let omegaLeafClass ← word
  let sharedSplitLeafClass ← word
  let wLeafClass ← word
  let ownSplitLeafClass ← word
  let sharedMaskCode ← word
  let ownMaskCode ← word
  let masksAhead ← flag
  let testU ← listOf stage
  let testOmega ← listOf stage
  let testOwn ← listOf stage
  let testOwnOmega ← listOf stage
  let choice ← choice
  pure { fold, kLo, matrixRows, omega, w, omegaRowsHigh, wRowsHigh, sharedSplit, ownSplit,
         omegaLeafClass, sharedSplitLeafClass, wLeafClass, ownSplitLeafClass, sharedMaskCode,
         ownMaskCode, masksAhead, testU, testOmega, testOwn, testOwnOmega, choice }

/-- The item "the link". -/
def linkShape : Cut LinkShape := do
  let table ← indexShape
  let columnsFirst ← word
  let columnsFurther ← word
  let code ← word
  let maskCode ← word
  let rows ← word
  let rowsHigh ← flag
  let leafClass ← word
  let masksAhead ← flag
  let later ← listOf stage
  let choice ← choice
  pure { table, columnsFirst, columnsFurther, code, maskCode, rows, rowsHigh, leafClass,
         masksAhead, later, choice }

/-- The item "binding tree": two words. -/
def bindingShape : Cut LinBindingShape := do
  let d ← word
  let y ← word
  pure ⟨d, y⟩

/-- A run: four words. -/
def wfRun : Cut WfRun := do
  let a ← word
  let b ← word
  let c ← word
  let d ← word
  pure ⟨a, b, c, d⟩

/-- A part: a word and the list of its runs. -/
def wfPart : Cut WfPart := do
  let l ← word
  let r ← listOf wfRun
  pure ⟨l, r⟩

/-- A lookup. -/
def wfLookup : Cut WfLookup := do
  let d ← word
  let mu ← word
  let live ← word
  let digitWeight ← listOf elt
  let offset ← elt
  let paddingKey ← elt
  let parts ← listOf wfPart
  let firstBound ← listOf word
  pure { d, mu, live, digitWeight, offset, paddingKey, parts, firstBound }

/-- The item "ranges". -/
def wfPublic : Cut WfPublic := do
  let lookups ← listOf wfLookup
  let message ← notice
  let messageId ← word
  let stages ← listOf stage
  let choice ← choice
  pure { lookups, message, messageId, stages, choice }

/-- The six words of an oracle message of a link: main rows, their degree, mask rows, class of
leaves, moment, life. Without main rows the word of the degree is 1. -/
def reqWords : Cut (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let rows ← word
  let deg ← word
  let masks ← word
  let lc ← word
  let moment ← word
  let life ← word
  Cut.demand ((deg == 1 || deg == 3) && (rows != 0 || deg == 1))
  pure (rows, deg, masks, lc, moment, life)

/-- An oracle message of a link from its six words, the chain's two codes and its answers. -/
def reqMessage (code maskCode answers : Nat) (x : Nat × Nat × Nat × Nat × Nat × Nat) :
    ReqMessage where
  shape :=
    { code := if x.1 == 0 then noId else code
      mainRows := x.1
      mainDeg := x.2.1
      maskRows := x.2.2.1
      maskCode := if x.2.2.1 == 0 then noId else maskCode
      answers := answers }
  leafClass := x.2.2.2.1
  moment := x.2.2.2.2.1
  life := x.2.2.2.2.2

/-- A chain of links. Refused: an oracle message that is kept beyond the last link. -/
def reqShape : Cut ReqShape := do
  let code ← word
  let maskCode ← word
  let links ← listOf do
    let p ← word
    let m ← listOf reqWords
    pure (p, m)
  let atStart ← listOf notice
  let answers ← word
  let later ← listOf stage
  let choice ← choice
  -- nothing is kept beyond the last link, so the last group holds only the carrying message: its
  -- two main rows give k = 1, and it has no mask rows, which gives h = 0
  Cut.demand (zipT (List.range links.length) links |>.all fun x =>
    x.2.2.all fun m => decide (x.1 + m.2.2.2.2.2 < links.length))
  pure { code, maskCode, atStart, answers, choice,
         link := links.map fun l => ⟨l.1, l.2.map (reqMessage code maskCode answers)⟩,
         last := ⟨code, maskCode, 1, 0⟩ :: later }

/-- A block of an array: nine words. -/
def laidBlock : Cut LaidBlock := do
  let firstI ← word
  let firstC ← word
  let firstRow ← word
  let firstPlace ← word
  let bitsI ← word
  let bitsC ← word
  let rowBits ← word
  let placeBits ← word
  let iIsLow ← flag
  pure { firstI, firstC, firstRow, firstPlace, bitsI, bitsC, rowBits, placeBits, iIsLow }

/-- An array: its name, three words and the list of its blocks. -/
def reqArray : Cut ReqArray := do
  let n ← cut Fmt.rdName
  let message ← word
  let sizeI ← word
  let sizeC ← word
  let blocks ← listOf laidBlock
  pure { name := Fmt.nameOf n, message, sizeI, sizeC, blocks }

/-- The item "layout". -/
def reqLayout : Cut ReqLayout := do
  let l ← listOf (listOf reqArray)
  pure ⟨l⟩

/-! ## The items by their names -/

/-- The item "codes". -/
def readCodes (value : ByteArray) : Option Codes := codes.whole value

/-- An item that is one notice: "index-mask message", "the oracle message a, b, c". -/
def readNotice (value : ByteArray) : Option OracleNotice := notice.whole value

/-- An item that is a list of stages: "the stages of the proximity test". -/
def readStages (value : ByteArray) : Option (List IoppStage) := (listOf stage).whole value

/-- An item that is one word of yes or no: "the choices of the proximity test". -/
def readFlag (value : ByteArray) : Option Bool := flag.whole value

/-- The item "the test on the table". -/
def readLin (value : ByteArray) : Option LinShape := linShape.whole value

/-- The item "the link". -/
def readLink (value : ByteArray) : Option LinkShape := linkShape.whole value

/-- The item "binding tree". -/
def readBinding (value : ByteArray) : Option LinBindingShape := bindingShape.whole value

/-- The item "ranges". -/
def readRanges (value : ByteArray) : Option WfPublic := wfPublic.whole value

/-- The items "request's shape" and "the chain of links". -/
def readReq (value : ByteArray) : Option ReqShape := reqShape.whole value

/-- The item "layout". -/
def readLayout (value : ByteArray) : Option ReqLayout := reqLayout.whole value

/-- An item that is a list of words: "links' identifiers". -/
def readWords (value : ByteArray) : Option (List Nat) := (listOf word).whole value

/-- An item that is one word: "pending rows". -/
def readWord (value : ByteArray) : Option Nat := word.whole value

end OnBytes.Params
