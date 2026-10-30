-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/Links.lean: the eleven public tests on the links of a request's chain, written anew
over a record of a link that holds numbers and names alone: no routine, no state of a check.
Definitions with code. No theorem.

Written after `verify-on-bytes`'s text (OnBytes/Model/StagesLinks.lean:159-515), test by test, in
its order; in front of the eleven a test of its own, listed, on what the program's lister lays. Each
test is a Bool; what the program makes on the way (the arrays' names; the declared arrays) is an
Option.

Main names:
  LinkD: a link: its name, identifier and kind; how many scalars it sends; whether it leaves a row
    on the weight table; the sizes of its arrays; which of them are over the extension field; where
    its symbol arrays, vectors and digits stand in its list; which arrays it reads of earlier links.
  TableD: the weight table's layout, as far as the tests read it.
  declare links NGr p4: the links with their arrays' names, and what each link declares.
  listed links NGr p4: the links are the listed ones, in their order.
  elevenL, elevenB: the eleven, each with its name; all.
  codesOk codes: every code's message length is a power of two.

THE TESTS. A row: number and name · `verify-on-bytes`'s line · what it reads.
  0 listed · :159-168 (listLinksH: there a maker, with one refusal, :161; here a test) · the links'
    names, identifiers, kinds and flags; NGr, p4
  1 headLast · :173-182 · the links' kinds and identifiers
  2 linksCount · :185-186 · their number
  3 declare · :289-301 (declareOwn :233-249, own :217-224, namesH :199-203, foreign :267-285,
    keptUpTo :253-258) · the links, NGr, p4
  4 heldAgainst · :400-405 (linkHeld :388-393, arrayHeld :374-383, messageHeld :359-363, blockHeld
    :366-368) · what is declared; the given shape and layout
  5 tableRows · :311-312 · the links' flags, NGr
  6 weightLimbs · :342-345 (:316-334) · the table's units
  7 tableHeld · :420-422 · the table's rows and column bits; the given shape of the test on it
  8 reqOk · :511 · BY `verify-on-bytes`'s NAME (OnBytes/Iop/Req.lean:222)
  9 listedFits · :427-431 · the plan's bytes of a position; the codes
  10 linksFit · :480-484 (indexMaskRoom :436-449, linksLaid :468-472, linkLaid :454-465); its first
    clause, reqLayoutOk, BY `verify-on-bytes`'s NAME (OnBytes/Iop/ReqRows.lean:247)
  11 numbersHeld · :412-416 · the given plain scalars, pending rows, identifiers
  codesOk · OnBytes/Iop/Ground.lean:67-68 (Codes.lengthsOk; powerOfTwo :53), which every run of
    `verify-on-bytes` asks in front (:915) · the message lengths of all the record's codes

Written anew from other files: momentsOf (OnBytes/Iop/Req.lean:144-147), the array of a name
(OnBytes/Iop/ReqRows.lean:210-211), freeEntries (OnBytes/Iop/Send.lean:116-118), masksTaken (:351;
OnBytes/Iop/Batt.lean:58).

Limits. The given numbers are still read off `verify-on-bytes`'s records of the plan (Params.First
and what it holds), and two tests are still its routines, by name: these are parts for which this
text waits. Who makes the LinkD's and the TableD from the sub-proofs' plans is not said here: in the
harness they are read off `verify-on-bytes`'s links. A LinkD does not hold the number of a
sub-proof's claims on the weights, nor of an array's entry in the list more than its field: later
tests of `verify-on-bytes` read both (:579, :549). No test here hears a word of the proof file. That
these tests say what the program's say has been held by runs alone. Nothing on soundness or hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Iop.ReqRows
import OnBytes.Params.Chains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ok.Links
open OnBytes
open OnBytes.Params (ReqShape ReqLayout ReqLink ReqMessage ReqArray LaidBlock)

/-- A link of the chain, as numbers and names. -/
structure LinkD where
  /-- G0, A0, .., H -/
  name : String := ""
  /-- the sub-proof's public identifier -/
  gid : Nat := 0
  /-- 0 layers, 1 attention, 2 the head -/
  kind : Nat := 0
  /-- the number of scalars that the sub-proof sends -/
  ns : Nat := 0
  /-- the sub-proof leaves a row on the weight table -/
  fv : Bool := false
  /-- rows and columns of each array of the planned state -/
  sizes : Array (Nat × Nat) := #[]
  /-- for each array of the sub-proof's list: its elements are in the extension field -/
  overE : Array Bool := #[]
  /-- the symbol arrays that no other sub-proof reads: their numbers in the list; their matrices -/
  own : List Nat := []
  ownMat : List Nat := []
  /-- the symbol arrays that another sub-proof reads -/
  lent : List Nat := []
  lentMat : List Nat := []
  /-- the arrays of earlier sub-proofs that this one reads: their numbers in the list; for each the
  owner among the layers' sub-proofs and the place among the owner's symbol arrays -/
  borrowed : List Nat := []
  from_ : List (Option Nat × Option Nat) := []
  /-- the vectors U1 to U4 -/
  vectors : List (Option Nat) := []
  /-- the digits of the smallness test and their multiplicities -/
  digits : Nat := 0
  counts : Nat := 0
  /-- for each matrix: the number of its symbol array in the list -/
  arrayOfMatrix : Array Nat := #[]
  /-- for each array of the list: the link that commits to it, and its name there -/
  arrayOf : Array (Nat × String) := #[]
  deriving Repr, Inhabited

/-- A unit of the weight table: its kind, its digits, its rows, its first row. -/
structure UnitD where
  kind : Nat
  digits : Nat
  rows : Nat
  first : Nat
  deriving Repr, Inhabited

/-- The weight table's layout. -/
structure TableD where
  columnBits : Nat
  rows : Nat
  units : List UnitD
  deriving Repr, Inhabited

/-- An array that a sub-proof commits to, as it declares it. -/
structure ArrayD where
  name : String
  rows : Nat
  columns : Nat
  overE : Bool
  /-- the last link that reads it is this many links after its own -/
  life : Nat := 0
  deriving Repr, Inhabited

/-- A link's declared arrays, moment by moment. -/
abbrev Moments : Type := Array (Array ArrayD)

def distinct : List Nat → Bool
  | [] => true
  | x :: t => !t.contains x && distinct t

/-! ### 0 -/

/-- What `verify-on-bytes`'s routine that lists the links lays: for each group g of layers the link
G_g, directly followed by A_g if the proof covers attention; last the head H: name, identifier,
kind, the flag of a row on the weight table. -/
def listOf (NGr : Nat) (p4 : Bool) : List (String × Nat × Nat × Bool) :=
  ((List.range NGr).flatMap fun g =>
    ("G" ++ toString g, 1 + g, 0, true) ::
      (if p4 then [("A" ++ toString g, 2 + NGr + g, 1, false)] else [])) ++
    [("H", 1 + NGr, 2, true)]

/-- **The links are the listed ones, in their order.** -/
def listed (links : Array LinkD) (NGr : Nat) (p4 : Bool) : Bool :=
  links.toList.map (fun X => (X.name, X.gid, X.kind, X.fv)) == listOf NGr p4

/-! ### 1, 2 -/

/-- There is exactly one head link, and it is the last; the identifiers are pairwise different. -/
def headLast (links : Array LinkD) : Bool :=
  (links.toList.zipIdx.all fun x => x.1.kind != 2 || x.2 + 1 == links.size) &&
    (links.toList.filter (·.kind == 2)).length == 1 && distinct (links.toList.map (·.gid))

def linksCount (links : Array LinkD) : Bool := decide (2 ≤ links.size) && decide (links.size ≤ 64)

/-! ### 3 -/

/-- The number of the link that checks the layers of group g. -/
def layersLink (p4 : Bool) (g : Nat) : Nat := if p4 then 2 * g else g

def matrixName (mu : Nat) : String := "M" ++ toString mu

/-- Link born committed to array number tree, under name: the number is in the list, and the array
has no name yet. -/
def named (arrayOf : Array (Nat × String)) (tree born : Nat) (name : String) :
    Option (Array (Nat × String)) :=
  (arrayOf[tree]?).bind fun a => if a.2.isEmpty then some (arrayOf.set! tree (born, name)) else none

/-- Array number tree of link l is declared under name, at the moment that was opened last. -/
def declareOne (X : LinkD) (l : Nat) (d : Array (Nat × String) × Moments) (tree : Nat)
    (name : String) : Option (Array (Nat × String) × Moments) := do
  let arrayOf ← named d.1 tree l name
  let size ← X.sizes[tree]?
  let e ← X.overE[tree]?
  pure (arrayOf, d.2.modify (d.2.size - 1) (·.push ⟨name, size.1, size.2, e, 0⟩))

/-- What link l commits to: first its symbol arrays; then a moment for each vector that it has; last
the digits and their multiplicities. -/
def declareOwn (X : LinkD) (l : Nat) : Option (Array (Nat × String) × Moments) :=
  if X.ownMat.isEmpty || X.own.length != X.ownMat.length || X.lent.length != X.lentMat.length ||
      X.borrowed.length != X.from_.length then none
  else do
    let d₀ : Array (Nat × String) × Moments :=
      (Array.replicate X.overE.size (2 ^ 64 - 1, ""), #[#[]])
    let d₁ ← (X.own.zip X.ownMat ++ X.lent.zip X.lentMat).foldlM
      (fun d x => declareOne X l d x.1 (matrixName x.2)) d₀
    let d₂ ← ((X.vectors.take 4).zipIdx).foldlM
      (fun d x => match x.1 with
        | some tree => declareOne X l (d.1, d.2.push #[]) tree ("U" ++ toString (x.2 + 1))
        | none => some d) d₁
    let d₃ ← declareOne X l (d₂.1, d₂.2.push #[]) X.digits "ZZ"
    declareOne X l d₃ X.counts "BZ"

/-- The array name of the first moment is still read life links later. -/
def kept (D : Moments) (name : String) (life : Nat) : Option Moments :=
  let first := D.getD 0 #[]
  if first.any (·.name == name) then
    some (D.set! 0
      (first.map fun a => if a.name == name then { a with life := max a.life life } else a))
  else none

/-- An array that link l reads and an earlier layers' link has committed to. -/
def borrow (links : Array LinkD) (NGr : Nat) (p4 : Bool) (l : Nat) (X : LinkD)
    (s : Array (Nat × String) × Array Moments) (tree : Nat) (pl : Option Nat × Option Nat) :
    Option (Array (Nat × String) × Array Moments) := do
  let owner ← pl.1
  let born := layersLink p4 owner
  if owner ≥ NGr || born ≥ l then none
  let Y ← links[born]?
  let place ← pl.2
  if place < Y.ownMat.length || place ≥ Y.ownMat.length + Y.lentMat.length then none
  let mu ← Y.lentMat[place - Y.ownMat.length]?
  let mine ← X.sizes[tree]?
  let theirs ← (Y.arrayOfMatrix[mu]?).bind fun t => Y.sizes[t]?
  if mine != theirs then none
  let arrayOf ← named s.1 tree born (matrixName mu)
  let D ← s.2[born]?
  let D ← kept D (matrixName mu) (l - born)
  pure (arrayOf, s.2.set! born D)

/-- **The declarations of all links**: the links with their arrays' names, and each link's arrays.
Every array of every list has got a name. -/
def declare (links : Array LinkD) (NGr : Nat) (p4 : Bool) : Option (Array LinkD × Array Moments) :=
  links.toList.zipIdx.foldlM
    (fun (acc : Array LinkD × Array Moments) x => do
      let d ← declareOwn x.1 x.2
      let s ← (x.1.borrowed.zip x.1.from_).foldlM
        (fun s y => borrow links NGr p4 x.2 x.1 s y.1 y.2) (d.1, acc.2)
      if s.1.any (·.2.isEmpty) then none
      pure (acc.1.push { x.1 with arrayOf := s.1 }, s.2.push d.2))
    (#[], #[])

/-! ### 4 -/

def messageHeld (first : Bool) (moments : Nat) (m : ReqMessage) : Bool :=
  m.shape.mainRows != 0 && decide (m.shape.mainRows < 2 ^ 32) &&
    m.shape.maskRows == (if first then 1 else 0) && decide (m.moment < moments) &&
    decide (m.life < 2 ^ 20) && (m.life == 0 || (m.shape.mainDeg == 1 && !first)) &&
    m.leafClass == 0

def blockHeld (b : LaidBlock) : Bool :=
  decide (b.bitsI < 48) && decide (b.bitsC < 48) && decide (b.rowBits < 48) &&
    decide (b.placeBits < 48)

/-- The declared array a of moment t is laid out as declared, in a message of that moment, over its
field, kept as long as its last reader needs. -/
def arrayHeld (messages : List ReqMessage) (arrays : List ReqArray) (t : Nat) (a : ArrayD) : Bool :=
  match arrays.find? fun A => A.name == a.name with
  | none => false
  | some A =>
    A.sizeI == a.rows && A.sizeC == a.columns && !A.blocks.isEmpty && A.blocks.all blockHeld &&
      match messages[A.message]? with
      | none => false
      | some m => m.moment == t && (m.shape.mainDeg == 3) == a.overE && decide (a.life ≤ m.life)

/-- The number of a given link's moments. -/
def momentsOf (L : ReqLink) : Nat := (L.messages.getLast?.map (·.moment + 1)).getD 0

def linkHeld (D : Moments) (L : ReqLink) (arrays : List ReqArray) : Bool :=
  let here := D.toList.flatMap (·.toList)
  momentsOf L == D.size &&
    (L.messages.zipIdx.all fun m => messageHeld (m.2 == 0) D.size m.1) &&
    (D.toList.zipIdx.all fun M => M.1.all fun a => arrayHeld L.messages arrays M.2 a) &&
    arrays.length == here.length && arrays.all fun A => here.any fun a => a.name == A.name

/-- The given shape and layout agree with what is declared: one given link and one list of arrays
for each link; each link's moments, messages and arrays (linkHeld). Not compared, as in
`verify-on-bytes` (:41-43): how many oracle messages a moment has, their rows, which of them holds
an array, the array's blocks. -/
def heldAgainst (declared : Array Moments) (p : Params.First) : Bool :=
  declared.size == p.shape.link.length && declared.size == p.layout.link.length &&
    (declared.toList.zip (p.shape.link.zip p.layout.link)).all fun x => linkHeld x.1 x.2.1 x.2.2

/-! ### 5, 6, 7 -/

def onTable (links : Array LinkD) : Nat := (links.toList.filter (·.fv)).length

def tableRows (links : Array LinkD) (NGr : Nat) : Bool := onTable links == NGr + 1

/-- The units follow one another without a gap from row next on; each has two or four digits and the
same number of rows for each digit. -/
def unitsInTurn (rows : Nat) : Nat → List UnitD → Bool
  | _, [] => true
  | next, u :: us =>
    (u.digits == 2 || u.digits == 4) && u.rows != 0 && u.rows % u.digits == 0 &&
      decide (u.rows ≤ rows) && decide (u.first ≤ rows - u.rows) && u.first == next &&
      unitsInTurn rows (u.first + u.rows) us

/-- Only the embedding, kind 12, has four digits; the units are in order. -/
def weightLimbs (Y : TableD) : Bool :=
  !(Y.units.any fun u => u.digits == 4 && u.kind != 12) &&
    (!Y.units.isEmpty && Y.rows % 2 == 0 && decide (Y.rows < 2 ^ 40) &&
      unitsInTurn Y.rows 0 Y.units)

def tableHeld (Y : TableD) (p : Params.First) : Bool :=
  p.lin.matrixRows == Y.rows && p.lin.kCol == Y.columnBits

/-! ### 9, 10, 11 -/

def listedFits (p : Params.First) : Bool :=
  let listed := p.given.plan.posB
  let longest := ((p.codes.base ++ p.codes.mask).map (·.logN)).foldl max p.lin.fold.index.code.logN
  !(listed != 0 && decide (listed < 8) && decide (longest > 8 * listed))

/-- How many entries the ledger of a sampled message's mask rows gives out. -/
def freeEntries (maskRows ell answers : Nat) : Nat :=
  if maskRows == 0 || ell < answers then 0 else maskRows * (ell - answers) + (maskRows - 1)

/-- The mask entries that the request's rows on the weight table take: one for each row, and those
of the batching if there is more than one row. -/
def masksTaken (rows kCol : Nat) : Nat := rows + (if rows > 1 then 1 + 2 * kCol else 0)

/-- The one message at the chain's start has a free entry for each row and for their batching. -/
def indexMaskRoom (links : Array LinkD) (codes : Codes) (shape : ReqShape) (kCol : Nat) : Bool :=
  match shape.atStart with
  | [n] =>
    let s := n.shape
    match codes.mask[s.maskCode]? with
    | none => false
    | some zk =>
      !(s.maskRows == 0 || decide (zk.ell < s.answers) ||
        decide (freeEntries s.maskRows zk.ell s.answers < masksTaken (onTable links) kCol))
  | _ => false

/-- Link l's scalars and the answers' pads have room in its mask row; every array that it reads is
laid out and, if an earlier link has sent it, still kept. -/
def linkLaid (shape : ReqShape) (layout : ReqLayout) (maskRow l : Nat) (X : LinkD) : Bool :=
  decide (X.ns + shape.answers ≤ maskRow) &&
    X.arrayOf.all fun a =>
      let life : Option Nat := do
        let arrays ← layout.link[a.1]?
        let A ← arrays.find? fun A => A.name == a.2
        let L ← shape.link[a.1]?
        let m ← L.messages[A.message]?
        pure m.life
      life.any fun life => decide (l ≤ a.1 + life)

def linksLaid (links : Array LinkD) (codes : Codes) (shape : ReqShape) (layout : ReqLayout) :
    Bool :=
  (codes.mask[shape.maskCode]?).any fun zk =>
    links.toList.zipIdx.all fun x => linkLaid shape layout zk.ell x.2 x.1

def linksFit (links : Array LinkD) (codes : Codes) (shape : ReqShape) (layout : ReqLayout)
    (kCol : Nat) : Bool :=
  reqLayoutOk codes shape layout && indexMaskRoom links codes shape kCol &&
    linksLaid links codes shape layout

def numbersHeld (links : Array LinkD) (p : Params.First) : Bool :=
  p.shape.link.map (·.plain) == List.replicate (links.size - 1) 0 ++ [1] &&
    p.pendingRows == onTable links && p.identifiers == links.toList.map (·.gid)

/-! ### The codes -/

/-- True if n is a power of two. -/
def powerOfTwo (n : Nat) : Bool := n != 0 && 2 ^ n.log2 == n

/-- **Every code's message length is a power of two**: of all the record's codes, whether a stage
names them or not. -/
def codesOk (codes : Codes) : Bool :=
  (codes.base.all fun c => powerOfTwo c.ell) && codes.mask.all fun c => powerOfTwo c.ell

/-! ### All eleven -/

/-- The eleven, each with its name, in `verify-on-bytes`'s order. Where the declaring fails, the
four tests that are handed what it makes say no. -/
def elevenL (links : Array LinkD) (NGr : Nat) (p4 : Bool) (Y : TableD) (p : Params.First) :
    List (String × Bool) :=
  let d := declare links NGr p4
  [("headLast", headLast links), ("linksCount", linksCount links), ("declareLinks", d.isSome),
   ("heldAgainst", d.any fun x => heldAgainst x.2 p),
   ("tableRows", d.any fun x => tableRows x.1 NGr),
   ("weightLimbs", weightLimbs Y), ("tableHeld", tableHeld Y p),
   ("reqOk", reqOk p.codes p.shape), ("listedFits", listedFits p),
   ("linksFit", d.any fun x => linksFit x.1 p.codes p.shape p.layout p.lin.kCol),
   ("numbersHeld", d.any fun x => numbersHeld x.1 p)]

/-- **All eleven say yes.** -/
def elevenB (links : Array LinkD) (NGr : Nat) (p4 : Bool) (Y : TableD) (p : Params.First) : Bool :=
  (elevenL links NGr p4 Y p).all (·.2)

end VerifiableInference.Desc.Ok.Links
