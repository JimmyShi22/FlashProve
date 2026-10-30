-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/StagesLinks.lean: the links of a request's chain.

A request's proof is a chain of links, and each link holds one sub-proof. The order is G0, A0, G1,
A1, and so on, then H. G_g checks the layers of group g, A_g their attention, H the output head. A
link commits several times, and each time is called a moment. Commitments, samples, positions and
proximity tests belong to the chain (OnBytes/Model/ReqChain.lean). What a sub-proof claims belongs
to the sub-proof. This file joins the two. It mirrors verifier/src/vf_segments.inc of the C++
verifier. Where that file names a routine, the definition here has its name (names is namesH here).

Words. The weight table is the committed matrix of weights. A row on it is a linear claim on that
matrix that a sub-proof leaves to be tested later (OnBytes/Model/Pending.lean). Mask row is
explained at Fork in OnBytes/Model/Hide.lean, symbol and smallness test at t2AddP in
OnBytes/Model/Trees.lean, dry run and view in OnBytes/Iop/Ground.lean.

   LinkH, SubPlanH           one link: the plan of its sub-proof, and the sub-proof's check
   FrameArray, FrameLink     the arrays that a link commits to, as the sub-proof declares them
   listLinksH                the links in their order, with their names and identifiers
   declareLinks              what every link declares
   heldAgainst, numbersHeld  compare the given shape, layout and numbers with the sub-proofs'
   tableHeld                 compares the given shape of the test on the weight table
   linksFit                  tests that the links fit the sized shape and the layout
   buildLinksH               the public tests on the links, before a byte of a proof is read
   pendingRowH, indexMasksH  parts of a link's run
   runLinkH, runLinksH       the links of one proof, on the proof's first chain
   placedAlike, onePlacement a condition on the layout that the result of a call reads
   linksNames                the names of this file's refusals

Where this file differs from the C++ file. The C++ routine makes the shape of the request's links
and the layout of their arrays from the declared arrays and a layout file. From these it makes the
codes and the plan of every round, and hashes the result. Here these steps are the caller's
(OnBytes/Model/VerifyChains.lean). It takes the declared arrays from declareLinks, reads the layout
file, has the planner make the codes and then the plans, runs linksFit between these two steps, and
writes out the parameter bytes of the first chain. buildLinksH takes what has been read back from
these bytes (Params.First), which are the bytes that the chain's first hash call takes in. Below,
"given" means: read back from these bytes. So no shape, layout, code or plan is made in this file,
and no layout file is read. The given shape and layout are compared with what the sub-proofs
declare, number by number. The purpose is that a public number does not have two descriptions that
differ. heldAgainst, numbersHeld and tableHeld list what is compared. What a layout file is free to
choose is not compared: how many oracle messages a moment has, their rows, which of them holds an
array, and the array's blocks.

The public tests return nothing, or the name under which the C++ verifier refuses. Where the C++
verifier sets a number and this file compares it, the name is "plan-layout" for a number of the
layout file and "parameters-not-admitted" for any other. A block that runs on a proof fails with the
name under which the C++ verifier refuses, where its test has a counterpart there. A test without a
counterpart fails as plan-link, or without a name.

What this file does not claim. No theorem is stated here. The sizes of codes, the numbers of
positions and the plan's rounds are taken from the bytes. The C++ routine ends with a call that also
puts the public files through a gate (OnBytes/Params/Gate.lean). This file does not run that gate.
The planner runs it, with the range checks of the links' smallness tests, which
OnBytes/Model/VerifyHiding.lean lists. The C++ routine's mode that only prints the list of arrays,
and its printed lines, have no counterpart. Nor have two C++ guards: that the format and the
commitment were identified before the links run, and that every sub-proof has set its flag. That a
link's check has closed the link is tested here as there (runLinkH; runLinksH).
-/
import OnBytes.Model.Tail
import OnBytes.Model.Pending
import OnBytes.Proof.File

namespace OnBytes.Model.Stages

open Params (ReqShape ReqLayout ReqLink ReqMessage ReqArray LaidBlock)

/-- The names with which the definitions of this file refuse. Names that come up from a definition
of another file (the row on the weight table) are in that file's list. -/
def linksNames : List String :=
  ["plan-head", "plan-link", "plan-shape", "plan-fold-source", "plan-layout", "plan-mask-row",
   "internal-weight-limbs", "parameters-not-admitted"]

/-! ## A link, and the arrays that it declares -/

/-- One link of the chain: a sub-proof. The fields tl, Fp and Tp are the sub-proof's plan, made from
public numbers. The C++ member for the sub-proof's rounds is not a field here: its counterpart is
linkRounds in OnBytes/Model/VerifySubproofs.lean. -/
structure LinkH where
  /-- the link's name: G0, A0, .., H -/
  name : String := ""
  /-- the sub-proof's public identifier -/
  gid : Nat := 0
  /-- 0 layers, 1 attention, 2 the head -/
  kind : Nat := 0
  /-- the group of layers; 0 for the head. As in the C++ record; no definition of this library reads
  it -/
  g : Nat := 0
  /-- the plan of the sub-proof's closing part -/
  tl : HTailF2 := {}
  /-- the planned state of the sub-proof's check: its arrays have their sizes. run is started from
  it, and sets up its own state from these arrays. -/
  Fp : Fork := {}
  /-- the sub-proof's list of arrays -/
  Tp : Tail2 := {}
  /-- the number of scalars that the sub-proof sends; as many entries of the link's mask row are
  used -/
  ns : Nat := 0
  /-- the sub-proof leaves a row on the weight table -/
  fv : Bool := false
  /-- the number of the sub-proof's claims on the weights by its plan; 0 where fv is false -/
  NCL : Nat := 0
  /-- for each array of the sub-proof's list: the link that commits to it, and its name there.
  declareLinks fills it. -/
  arrayOf : Array (Nat × String) := #[]
  /-- the check of the sub-proof. If fv is true it returns what its claims on the weights leave. -/
  run : LinkM (Option WsForkOut)

/-- An array that a sub-proof commits to, as the sub-proof declares it. C++: blk::FrameArray. -/
structure FrameArray where
  /-- the array's name in its link -/
  name : String := ""
  /-- its rows -/
  rows : Nat := 1
  /-- its columns -/
  columns : Nat := 1
  /-- its elements are in the extension field, so it lies in rows over that field -/
  overE : Bool := false
  /-- the last link that reads it is this many links after its own; 0 if only its own link reads it
  -/
  life : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The arrays of one link. C++: blk::FrameLink. -/
structure FrameLink where
  /-- the link's name. As in the C++ record; no definition of this library reads it -/
  name : String := ""
  /-- the arrays of each moment, in the order in which a layout file numbers them -/
  moment : Array (Array FrameArray) := #[]
  deriving DecidableEq, Repr, Inhabited

/-! ## The order of the links -/

/-- What the plan of one sub-proof gives to its link. The fields are those of LinkH. -/
structure SubPlanH where
  /-- the plan of the sub-proof's closing part -/
  tl : HTailF2 := {}
  /-- the planned state of the sub-proof's check -/
  Fp : Fork := {}
  /-- the sub-proof's list of arrays -/
  Tp : Tail2 := {}
  /-- the number of scalars that the sub-proof sends -/
  ns : Nat := 0
  /-- the number of its claims on the weights; 0 for attention -/
  NCL : Nat := 0
  /-- the check of the sub-proof -/
  run : LinkM (Option WsForkOut)

/-- A link from its sub-proof's plan. -/
def SubPlanH.link (s : SubPlanH) (name : String) (gid kind g : Nat) (fv : Bool) : LinkH :=
  { name := name, gid := gid, kind := kind, g := g, tl := s.tl, Fp := s.Fp, Tp := s.Tp, ns := s.ns,
    fv := fv, NCL := s.NCL, run := s.run }

/-- The links of the chain in their order: for each group g of layers the link G_g, directly
followed by A_g if the proof covers attention (p4); last the head H. The identifiers are 1 + g for
G_g, 1 + NGr for H and 2 + NGr + g for A_g. G, A: the plans of the sub-proofs for layers and for
attention, one for each group. Refused: G, or A if p4 is true, has another number of plans than NGr.
-/
def listLinksH (NGr : Nat) (p4 : Bool) (G A : Array SubPlanH) (H : SubPlanH) :
    Except String (Array LinkH) := do
  if G.size != NGr || (p4 && A.size != NGr) then throw "plan-link"
  let mut links : Array LinkH := #[]
  for (s, g) in G.toList.zipIdx do
    links := links.push (s.link ("G" ++ toString g) (1 + g) 0 g true)
    if p4 then
      if let some a := A[g]? then
        links := links.push (a.link ("A" ++ toString g) (2 + NGr + g) 1 g false)
  pure (links.push (H.link "H" (1 + NGr) 2 0 true))

/-- Tests that there is exactly one head link, and that it is the last link: the reply goes out
before the last link's first message. Also tests that the identifiers of all sub-proofs are pairwise
different. -/
def headLast (links : Array LinkH) : Except String Unit := do
  let mut heads := 0
  let mut gids : List Nat := []
  for (X, i) in links.toList.zipIdx do
    if X.kind == 2 then
      heads := heads + 1
      if i + 1 != links.size then throw "plan-head"
    if gids.contains X.gid then throw "plan-link"
    gids := X.gid :: gids
  if heads != 1 then throw "plan-head"

/-- Tests that a chain has at least 2 and at most 64 links. -/
def linksCount (links : Array LinkH) : Except String Unit :=
  if links.size < 2 || links.size > 64 then throw "plan-shape" else pure ()

/-- The number of the link that checks the layers of group g. p4: the proof covers attention, so
that each such link is followed by a link for its attention. -/
def layersLink (p4 : Bool) (g : Nat) : Nat := if p4 then 2 * g else g

/-! ## The declared arrays -/

/-- Stands for "no link" in arrayOf until an array has its name. -/
def noLink : Nat := 2 ^ 64 - 1

/-- Records that link `born` committed to array number `tree` of a sub-proof's list, under `name`.
Refused: a number outside the list, or an array that already has a name. C++: names. -/
def namesH (arrayOf : Array (Nat × String)) (tree born : Nat) (name : String) :
    Except String (Array (Nat × String)) :=
  match arrayOf[tree]? with
  | some a => if a.2.isEmpty then pure (arrayOf.set! tree (born, name)) else throw "plan-link"
  | none => throw "plan-link"

/-- What is known of a link's arrays while they are declared. -/
structure Declaring where
  /-- as in LinkH -/
  arrayOf : Array (Nat × String)
  /-- as in FrameLink; an array joins the last moment -/
  moment : Array (Array FrameArray)

/-- Opens the link's next moment. -/
def Declaring.nextMoment (d : Declaring) : Declaring := { d with moment := d.moment.push #[] }

/-- Declares array number `tree` of the list of X (link `l`) under `name`, at the moment that was
opened last. Rows and columns are those of the sub-proof's plan. -/
def own (X : LinkH) (l : Nat) (d : Declaring) (tree : Nat) (name : String) :
    Except String Declaring := do
  let arrayOf ← namesH d.arrayOf tree l name
  match X.Fp.trees[tree]?, X.Tp.nt[tree]? with
  | some t, some n =>
    let a : FrameArray := { name := name, rows := t.R, columns := t.K, overE := n.ec == 3 }
    pure { arrayOf := arrayOf, moment := d.moment.modify (d.moment.size - 1) (·.push a) }
  | _, _ => throw "plan-link"

/-- The name of the symbol array of matrix number mu of a sub-proof's list of matrices. -/
def matrixName (mu : Nat) : String := "M" ++ toString mu

/-- The arrays that link l, which is X, commits to, moment by moment. First moment: the symbol
arrays, first those that no other sub-proof reads, then those that one does. Then one moment for
each vector U1 to U4 that the sub-proof has. Last: ZZ and BZ, the digits of the smallness test and
their multiplicities. -/
def declareOwn (X : LinkH) (l : Nat) : Except String Declaring := do
  let tl := X.tl
  if tl.pkMat.isEmpty || tl.ix.PK.size != tl.pkMat.size || tl.ix.TX.size != tl.pxMat.size ||
      tl.ix.FT.size != tl.plFor.size then
    throw "plan-link"
  let mut d : Declaring :=
    { arrayOf := Array.replicate X.Tp.nt.size (noLink, ""), moment := #[#[]] }
  for (tree, mu) in zipT tl.ix.PK.toList tl.pkMat.toList do
    d ← own X l d tree (matrixName mu)
  for (tree, mu) in zipT tl.ix.TX.toList tl.pxMat.toList do
    d ← own X l d tree (matrixName mu)
  for (u, n) in (tl.ix.U.toList.take 4).zipIdx do
    if let some tree := u then
      d ← own X l d.nextMoment tree ("U" ++ toString (n + 1))
  d ← own X l d.nextMoment tl.ix.ZZ "ZZ"
  d ← own X l d tl.ix.BZ "BZ"
  pure d

/-- Records that the array `name` of the first moment of D is still read `life` links later.
Refused: D declares no such array. -/
def keptUpTo (D : FrameLink) (name : String) (life : Nat) : Except String FrameLink :=
  let first := D.moment.getD 0 #[]
  if first.any (fun a => a.name == name) then
    let kept := first.map fun a => if a.name == name then { a with life := max a.life life } else a
    pure { D with moment := D.moment.set! 0 kept }
  else throw "plan-fold-source"

/-- A matrix that link l, which is X, reads and an earlier sub-proof has committed to. tree: its
number in the list of X. pl: the reader's record, which says who the owner is among the layer
sub-proofs and where the matrix lies among the owner's symbol arrays. Only a matrix that its owner
lists as read by others can be meant, and its size must be the one that the reader works with. The
sub-proofs' plans have compared the reader's record with the owner's own. The owner's array is then
declared as kept at least up to this reader. s: the arrayOf of X, and the earlier links'
declarations. -/
def foreign (links : Array LinkH) (NGr : Nat) (p4 : Bool) (l : Nat) (X : LinkH)
    (s : Array (Nat × String) × Array FrameLink) (tree : Nat) (pl : PlaceF) :
    Except String (Array (Nat × String) × Array FrameLink) := do
  let some owner := pl.owner | throw "plan-fold-source"
  if owner ≥ NGr || layersLink p4 owner ≥ l then throw "plan-fold-source"
  let born := layersLink p4 owner
  let some Y := links[born]? | throw "plan-fold-source"
  let O := Y.tl
  let some rootIndex := pl.rootIndex | throw "plan-fold-source"
  if rootIndex < O.pkMat.size || rootIndex ≥ O.pkMat.size + O.pxMat.size then
    throw "plan-fold-source"
  let some mu := O.pxMat[rootIndex - O.pkMat.size]? | throw "plan-fold-source"
  let some mine := X.Fp.trees[tree]? | throw "plan-fold-source"
  let some theirs := (O.gtTree[mu]?).bind (fun t => Y.Fp.trees[t]?) | throw "plan-fold-source"
  if mine.R != theirs.R || mine.K != theirs.K then throw "plan-fold-source"
  let arrayOf ← namesH s.1 tree born (matrixName mu)
  let some D := s.2[born]? | throw "plan-fold-source"
  let D ← keptUpTo D (matrixName mu) (l - born)
  pure (arrayOf, s.2.set! born D)

/-- The declarations of all links. Returns the links with arrayOf filled, and for each link its
arrays. Every array of every sub-proof's list must have got a name. -/
def declareLinks (links : Array LinkH) (NGr : Nat) (p4 : Bool) :
    Except String (Array LinkH × Array FrameLink) := do
  let mut named : Array LinkH := #[]
  let mut declared : Array FrameLink := #[]
  for (X, l) in links.toList.zipIdx do
    let d ← declareOwn X l
    let mut s := (d.arrayOf, declared)
    for (tree, pl) in zipT X.tl.ix.FT.toList X.tl.plFor.toList do
      s ← foreign links NGr p4 l X s tree pl
    if s.1.any (fun a => a.2.isEmpty) then throw "plan-link"
    named := named.push { X with arrayOf := s.1 }
    declared := s.2.push { name := X.name, moment := d.moment }
  pure (named, declared)

/-! ## The weight table -/

/-- The number of sub-proofs that leave a row on the weight table. -/
def onTable (links : Array LinkH) : Nat := (links.toList.filter (·.fv)).length

/-- Tests that NGr + 1 sub-proofs leave a row on the weight table: as many as there are groups of
layers, and one for the head. Only the number is tested, as in the C++ routine. `listLinksH` sets
the flag fv for exactly these links. -/
def tableRows (links : Array LinkH) (NGr : Nat) : Except String Unit :=
  if onTable links != NGr + 1 then throw "plan-link" else pure ()

/-- True if the units follow one another without a gap, starting at row `next`, within the first
`rangedRows` rows. Each has two or four digits and the same number of rows for each digit. -/
def wfUnitsInTurn (rangedRows : Nat) : (next : Nat) → List WsUnit → Bool
  | _, [] => true
  | next, u :: us =>
    (u.nlw == 2 || u.nlw == 4) && u.rows != 0 && u.rows % u.nlw == 0 &&
      decide (u.rows ≤ rangedRows) && decide (u.off ≤ rangedRows - u.rows) && u.off == next &&
      wfUnitsInTurn rangedRows (u.off + u.rows) us

/-- True if these are the units of a table of matrixRows rows, of which the first rangedRows are in
a key's proof of the ranges. There is a unit. The ranged rows are an even number and no more than
the table has. The table has fewer than 2^40 rows. The units follow one another from row 0 on. C++:
blk::wf_units_fault, which returns what is wrong. The same conditions as Plan.unitsOk
(OnBytes/Plan/Units.lean), which shapesWith tests (OnBytes/Model/VerifySubproofs.lean). -/
def wfUnitsOk (matrixRows rangedRows : Nat) (units : List WsUnit) : Bool :=
  !units.isEmpty && decide (rangedRows ≤ matrixRows) && rangedRows % 2 == 0 &&
    decide (matrixRows < 2 ^ 40) && wfUnitsInTurn rangedRows 0 units

/-- `wfUnitsOk` for a layout of the weight table, all of whose rows are ranged. C++:
blk::wf_layout_fault. -/
def wfLayoutOk (Y : WsLay) : Bool := wfUnitsOk Y.m0 Y.m0 Y.U.toList

/-- Two tests on the layout of the weight table. Only the embedding, kind 12, has four digits: of a
unit with four digits a key's range proof covers nothing beyond its bytes. The units are in order
(`wfLayoutOk`). It is not shown here that a key's proof of the ranges then covers what a request's
conditions assume of every weight.

-/
def weightLimbs (wsLay : WsLay) : Except String Unit :=
  if wsLay.U.any (fun u => u.nlw == 4 && u.X != 12) then throw "internal-weight-limbs"
  else if !wfLayoutOk wsLay then throw "internal-weight-limbs"
  else pure ()

/-! ## The given shape and layout against the declared arrays -/

/-- The number of mask entries that the request's rows on the weight table take from the index-mask
message: one for each row, and those of the batching if there is more than one row. -/
def indexMasksTaken (rows kCol : Nat) : Nat := rows + (if rows > 1 then Batt.masksOf kCol else 0)

/-- True if m is an oracle message of a link as a layout file can ask for it. first: it is the first
of its link. moments: the number of the link's declared moments, and the message belongs to one of
them. It has main rows, fewer than 2^32. The link's first message holds the link's one mask row, and
no other message has a mask row. Only rows over the base field are kept for later links, never those
of the link's first message, and for fewer than 2^20 links. All messages of all links are in the
class of leaves 0. -/
def messageHeld (first : Bool) (moments : Nat) (m : ReqMessage) : Bool :=
  m.shape.mainRows != 0 && decide (m.shape.mainRows < 2 ^ 32) &&
    m.shape.maskRows == (if first then 1 else 0) && decide (m.moment < moments) &&
    decide (m.life < 2 ^ 20) && (m.life == 0 || (m.shape.mainDeg == 1 && !first)) &&
    m.leafClass == 0

/-- A block as a layout file can describe it: each of its four logarithms is below 48. -/
def blockHeld (b : LaidBlock) : Bool :=
  decide (b.bitsI < 48) && decide (b.bitsC < 48) && decide (b.rowBits < 48) &&
    decide (b.placeBits < 48)

/-- Compares the declared array a of moment t of a link with the given arrays and messages of that
link. The layout has an array of this name with the declared rows and columns and at least one
block. It lies in an oracle message of the declared moment, over the field of its elements, that is
kept at least as long as the array's last reader needs. -/
def arrayHeld (messages : List ReqMessage) (arrays : List ReqArray) (t : Nat) (a : FrameArray) :
    Bool :=
  match arrays.find? fun A => A.name == a.name with
  | none => false
  | some A =>
    A.sizeI == a.rows && A.sizeC == a.columns && !A.blocks.isEmpty && A.blocks.all blockHeld &&
      match messages[A.message]? with
      | none => false
      | some m =>
        m.moment == t && (m.shape.mainDeg == 3) == a.overE && decide (a.life ≤ m.life)

/-- Compares one link's given messages and arrays with its declaration. The link has the declared
number of moments. Every message passes messageHeld. Every declared array is laid out as declared,
and the layout has no other array. -/
def linkHeld (D : FrameLink) (L : ReqLink) (arrays : List ReqArray) : Bool :=
  let here := D.moment.toList.flatMap (·.toList)
  reqMoments L == D.moment.size &&
    (L.messages.zipIdx.all fun m => messageHeld (m.2 == 0) D.moment.size m.1) &&
    (D.moment.toList.zipIdx.all fun M => M.1.all fun a => arrayHeld L.messages arrays M.2 a) &&
    arrays.length == here.length && arrays.all fun A => here.any fun a => a.name == A.name

/-- Compares the given shape and layout with what the sub-proofs' plans declare. It takes the place
of the step in which the C++ verifier makes both from the declarations and the layout file. What is
compared:
 - there is one given link and one given list of arrays for each declared link;
 - each link's moments, messages and arrays (linkHeld). -/
def heldAgainst (declared : Array FrameLink) (p : Params.First) : Except String Unit :=
  if declared.size == p.shape.link.length && declared.size == p.layout.link.length &&
      ((zipT declared.toList (zipT p.shape.link p.layout.link)).all fun x =>
        linkHeld x.1 x.2.1 x.2.2) then
    pure ()
  else throw "plan-layout"

/-- Compares the other given numbers of the first chain with the links. It takes the place of the
step in which the C++ verifier hands its own numbers over to be hashed. What is compared:
 - the head's link alone has a plain scalar, and it has one: the reply;
 - the number of rows that the links leave on the weight table;
 - the identifiers are the sub-proofs', in the links' order. -/
def numbersHeld (links : Array LinkH) (p : Params.First) : Except String Unit :=
  if p.shape.link.map (·.plain) == List.replicate (links.size - 1) 0 ++ [1] &&
      p.pendingRows == onTable links && p.identifiers == links.toList.map (·.gid) then
    pure ()
  else throw "parameters-not-admitted"

/-- Compares the given shape of the test on the weight table with the layout of the table from which
the sub-proofs make their rows. Both must have the same number of rows and of column bits. -/
def tableHeld (wsLay : WsLay) (p : Params.First) : Except String Unit :=
  if p.lin.matrixRows != wsLay.m0 || p.lin.kCol != wsLay.lk then throw "parameters-not-admitted"
  else pure ()

/-- A proof that lists its drawn positions gives each of them posB bytes, a number of the plan.
Every position of the weight table's code and of every code of the proof must fit in that many
bytes. -/
def listedFits (p : Params.First) : Except String Unit :=
  let listed := p.given.plan.posB
  let longest := ((p.codes.base ++ p.codes.mask).map (·.logN)).foldl max p.lin.fold.index.code.logN
  if listed != 0 && listed < 8 && longest > 8 * listed then throw "parameters-not-admitted"
  else pure ()

/-- Tests that the request's index-mask message, which is the one message at the start of the chain,
has a free entry for each sub-proof with claims on the weights and for the batching of their rows.
The free entries are counted as the sampling of the message counts them (Send.freeMaskEntries). -/
def indexMaskRoom (links : Array LinkH) (codes : Codes) (shape : ReqShape) (kCol : Nat) :
    Except String Unit :=
  match shape.atStart with
  | [n] =>
    let s := n.shape
    match codes.mask[s.maskCode]? with
    | none => throw "plan-mask-row"
    | some zk =>
      if s.maskRows == 0 || zk.ell < s.answers ||
          Send.freeMaskEntries s.maskRows zk.ell s.answers <
            indexMasksTaken (onTable links) kCol then
        throw "plan-mask-row"
      else pure ()
  | _ => throw "parameters-not-admitted"

/-- Tests that link l, which is X, fits the shape and the layout. Its scalars and the answers' pads
have room in the link's mask row of maskRow entries. Every array that it reads is laid out and, if
an earlier link has sent it, still kept. -/
def linkLaid (shape : ReqShape) (layout : ReqLayout) (maskRow l : Nat) (X : LinkH) :
    Except String Unit := do
  if X.ns + shape.answers > maskRow then throw "plan-mask-row"
  for a in X.arrayOf do
    let life : Option Nat := do
      let A ← reqArray layout a.1 a.2
      let L ← shape.link[a.1]?
      let m ← L.messages[A.message]?
      pure m.life
    match life with
    | some life => if a.1 + life < l then throw "plan-layout"
    | none => throw "plan-layout"

/-- linkLaid for every link. -/
def linksLaid (links : Array LinkH) (codes : Codes) (shape : ReqShape)
    (layout : ReqLayout) : Except String Unit := do
  let some zk := codes.mask[shape.maskCode]? | throw "plan-mask-row"
  for (X, l) in links.toList.zipIdx do
    linkLaid shape layout zk.ell l X

/-- The tests that the C++ routine makes after the sizing of the codes and before it makes the plan
of any round, in its order, but for the first of them, on listed positions (listedFits; the planner
has it at the end of its sizing). The layout fits the sized shape. The index-mask message has room.
Every link fits shape and layout. links: with arrayOf filled. kCol: the column bits of the weight
table. A caller that makes the plans itself runs these tests between the two steps, so that a file
with two faults is refused with the name that the C++ verifier gives. -/
def linksFit (links : Array LinkH) (codes : Codes) (shape : ReqShape) (layout : ReqLayout)
    (kCol : Nat) : Except String Unit := do
  if !reqLayoutOk codes shape layout then throw "plan-layout"
  indexMaskRoom links codes shape kCol
  linksLaid links codes shape layout

/-! ## All public tests -/

/-- What buildLinksH returns. -/
structure LinksH where
  /-- the links, with arrayOf filled -/
  links : Array LinkH

/-- The public tests on the links of a request's chain, in the order of the C++ routine. links: one
record for each sub-proof, in the chain's order, made from the sub-proofs' plans. NGr: the number of
groups of layers. p4: the proof covers attention. wsLay: the layout of the weight table. p: what the
parameter bytes of the first chain hold. One test is made elsewhere, where the plan of the links'
rounds is made (OnBytes/Params/SubRounds.lean): that every sub-proof's smallness test has the number
of random combinations that the plan's setting requires. In the program all of these tests except
heldAgainst, tableRows, tableHeld and numbersHeld have already passed in chainsOf
(OnBytes/Model/VerifyChains.lean), on the values from which the bytes were made. Here they run on
the values read back. -/
def buildLinksH (links : Array LinkH) (NGr : Nat) (p4 : Bool) (wsLay : WsLay)
    (p : Params.First) : Except String LinksH := do
  headLast links
  linksCount links
  let (links, declared) ← declareLinks links NGr p4
  heldAgainst declared p
  tableRows links NGr
  weightLimbs wsLay
  tableHeld wsLay p
  if !reqOk p.codes p.shape then throw "parameters-not-admitted"
  listedFits p
  linksFit links p.codes p.shape p.layout p.lin.kCol
  numbersHeld links p
  pure { links := links }

/-! ## The links of one proof -/

/-- The row that a sub-proof with claims on the weights leaves on the weight table, under the next
free entry of the index-mask message. Every refusal of wsPending is about sizes and numbers of
units, which are public, so a failure here is the same in the dry run and on a view. -/
def pendingRowH (wsLay : WsLay) (indexMasks : Nat) (o : WsForkOut) (claims : Nat)
    (S : Params.LinShape) : Blk TensorRow :=
  match wsPending wsLay o claims S with
  | .error name => refuse name
  | .ok p => do
    let c ← Blk.takeMask indexMasks
    pure (memberPendingRow p.g p.psi ⟨indexMasks, c⟩ p.beta p.target)

/-- Runs after the first link's first call. Tests that there is one oracle message at the start of
the chain, the index-mask message, and that its ledger has an entry for each sub-proof with claims
on the weights and for the batching of their rows. That number follows from the public files alone,
and indexMaskRoom has tested it on the shape. Returns the message's number. -/
def indexMasksH (links : Array LinkH) (p : Params.First) (check : ChainCheck) : Blk Nat := do
  mustAs "plan-link" (check.atStart.size == 1)
  let some indexMasks := check.atStart[0]? | refuse "plan-link"
  let x ← Blk.oracle indexMasks
  let ledger ← Blk.get x.ledger
  let left := if ledger.closed then 0 else ledger.left
  mustAs "plan-mask-row" (decide (indexMasksTaken (onTable links) p.lin.kCol ≤ left))
  pure indexMasks

/-- True if the check of a sub-proof has worked on the plan that X holds: the same list of arrays,
and for each array of the list the same rows and columns. F, list: the state and the list with which
the check has ended. The declared arrays, and with them the tie to the given layout, were made from
X. The check is a value of its own, and this test ties the two. In the C++ verifier both read one
object. -/
def samePlan (X : LinkH) (F : Fork) (list : Tail2) : Bool :=
  list.nt == X.Tp.nt &&
    (List.range X.Tp.nt.size).all fun t =>
      match F.trees[t]?, X.Fp.trees[t]? with
      | some a, some b => a.R == b.R && a.K == b.K
      | _, _ => false

/-- One link of a proof. l: its number. X: its record. The chain's first call for the link; the
reply, if this is the head's link; the check of the sub-proof, which calls the chain at its later
commitments and at its end; the row that the sub-proof leaves on the weight table. -/
def runLinkH (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (l : Nat) (X : LinkH)
    (check : ChainCheck) (out : Proof.LinksResult) : Blk (ChainCheck × Proof.LinksResult) := do
  let check ← check.first
  let out ←
    if l == 0 then do
      let indexMasks ← indexMasksH links p check
      pure { out with indexMasks := indexMasks }
    else pure out
  mustAs "plan-head" (check.plain.size == (if X.kind == 2 then 1 else 0))
  let out := if X.kind == 2 then { out with reply := check.plain[0]? } else out
  -- The record X was made for link l of the list. The walk must be at that link.
  Blk.must (check.link == l)
  let C : LinkCtx := { check := check, link := l, arrayOf := X.arrayOf, list := X.Tp }
  -- A failure inside the sub-proof's check gets the sub-proof's name as its place.
  let ((o, C), F) ← Blk.inPlace X.name (StateT.run (StateT.run X.run C) X.Fp)
  -- A routine that has returned without closing its link is refused.
  mustAs "plan-link" (C.handed && C.done)
  mustAs "plan-link" (samePlan X F C.list)
  if X.fv then
    -- The record says that this sub-proof leaves a row, so its check must return what is needed.
    let some o := o | refuse "plan-link"
    let row ← pendingRowH wsLay out.indexMasks o X.NCL p.lin
    pure (C.check, { out with pending := out.pending ++ [row] })
  else pure (C.check, out)

/-- The links that are still to come. l: the number of the first of them. -/
def runLinksFrom (links : Array LinkH) (p : Params.First) (wsLay : WsLay) :
    List LinkH → (l : Nat) → ChainCheck → Proof.LinksResult →
    Blk (ChainCheck × Proof.LinksResult)
  | [], _, check, out => pure (check, out)
  | X :: rest, l, check, out => do
    let (check, out) ← runLinkH links p wsLay l X check out
    runLinksFrom links p wsLay rest (l + 1) check out

/-- The links of one proof, on the proof's first chain: from the first link's first message to the
end of the links' last proximity test. links: as buildLinksH has returned them.

The caller's duty. p must be what Params.First.read has made of the parameter bytes that the chain's
first hash call takes in, and the same p that buildLinksH was given. Proof.check takes these bytes,
the codes and the plan's entries from its argument c, so the block to pass to it is runLinksH links
c.first wsLay. Shape, layout, codes and plan then have one source: these bytes. -/
def runLinksH (links : Array LinkH) (p : Params.First) (wsLay : WsLay) :
    Blk Proof.LinksResult := do
  let check ← ChainCheck.start p.shape p.layout
  let (check, out) ← runLinksFrom links p wsLay links.toList 0 check {}
  check.finish
  pure out

/-! ## A condition of the standard parameter form -/

/-- True if two arrays are placed in the same way: the same oracle message of their links, the same
rows and columns, and the same blocks in every number. False if one of them is missing. -/
def placedAlike : Option ReqArray → Option ReqArray → Bool
  | some a, some b =>
    a.message == b.message && a.sizeI == b.sizeI && a.sizeC == b.sizeC && a.blocks == b.blocks
  | _, _ => false

/-- True if the arrays that later sub-proofs read are placed in the same way in all links for
layers. The first link is the one for the first group of layers. -/
def onePlacement (links : Array LinkH) (layout : ReqLayout) : Bool :=
  let first := ((links[0]?).map fun X => X.tl.pxMat).getD #[]
  links.toList.zipIdx.all fun x =>
    x.1.kind != 0 ||
      (x.1.tl.pxMat.size == first.size &&
        (zipT x.1.tl.pxMat.toList first.toList).all fun m =>
          placedAlike (reqArray layout x.2 (matrixName m.1)) (reqArray layout 0 (matrixName m.2)))

end OnBytes.Model.Stages
