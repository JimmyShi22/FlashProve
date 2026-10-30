-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Rows.lean

The data of the main rows of the oracle message that holds the vector of reads U3, at every segment
of a proof file's first chain, as a value of the structure RowData
(Johnson/Desc/ProofFile/Honest/RowData.lean). Definitions with code. No theorem.

Each segment has one array of the name "U3", laid in an oracle message's main rows: one row of
elements of the extension field, at the segment's moment 1 (docs/format/11-1-machinery.md, "The
arrays of a segment's smallness test").
Entry n of the vector is a sum of cells of one matrix under public weights; the weights are made of
values that the verifier has sampled in front of the sending. So the vector is a function of the
cells, of the challenges heard, and of public data, the request among them. Of the readers it reads
the cells alone: no coin and no committed weight.

NO ENTRY's RULE IS TYPED HERE. One number is typed a second time, for a test: a part's number of
entries ("partsFit"). Called by name:
* the rule of an entry, given the list of parts: "readAt" (Johnson/Desc/K8/Honest/Arrays.lean),
  written "readAtP" in this file: its one local notation, for
  VerifiableInference.Desc.First.K8.Honest.readAt; at an attention segment "u3Of"
  (Johnson/Desc/K5/Honest/U3.lean);
* the lists of parts: at a group of layers the verifier's "Layer.layTables" and "Layer.funsOf"; at
  the output head the description's "K8.ReadsQuiet.tables"; at an attention segment the
  description's "tablesP";
* the sampled values under the verifier's names, of the list of challenges: at the layers "ptsOf"
  and "namedPts" (Johnson/Desc/K4/Honest/Front.lean); at the head "headHeardWholeAt"
  (Johnson/Desc/ProofFile/Honest/K6/HeardWhole.lean); at attention "ptsOf"
  (Johnson/Desc/K5/Honest/Points.lean); what the lookup in front has sampled: "k4LookOf"
  (Johnson/Desc/ProofFile/Honest/K4/Look.lean);
* the cells by a matrix's number in the segment's list: "cellsAtOf"
  (Johnson/Desc/ProofFile/Honest/K8/Part.lean) at "matsOwn"
  (Johnson/Desc/ProofFile/Honest/K3/WitOwner.lean): a matrix to which an earlier segment has
  committed is read under that segment's number and name;
* where an entry lies in the message's main rows: "laidData"
  (Johnson/Desc/ProofFile/Honest/LaidData.lean); which message that is, and behind how many rounds:
  Johnson/HonestTrace/SeatOf.lean.

TWO STOREYS.
THE VALUES go by the segment's number and the vector's own index; they read no place of a table and
no seat:
* "layersAt", "headAt": the vector at letters; the list of parts stands in front of the function of
  the cells.
* "SegVals": what a segment's maker returns where it accepts the public data: the number of reads;
  the number of the round of the chain from which on nothing more is read; and, of the challenges,
  a rejection or the vector as a function of the cells.
* "layersVals", "attVals", "headVals", "valsAt": the makers.
* "u3Vals Z G cov": THE VALUES AS THE LAYING TAKES THEM: a value of the structure ArrayVals
  (Johnson/Desc/ProofFile/Honest/LaidData.lean).
THE LAYING is "laidData" of that file, at the seats of Johnson/HonestTrace/SeatOf.lean:
* "seatAsks": the tests that hold a seat against a segment's values.
* "u3FitsWhy", "u3Fits": THE TEST ON PUBLIC DATA AT A SEAT. "u3AllFit": at all seats, and every
  segment has one.
* "heardWhy", "u3Why": why the data is not ready, at a list of challenges; nothing if it is.
* "u3Rows Z G cov": THE VALUE OF RowData. "u3Seats", "u3Mine".
* "covOf", "covWhy", "u3ValsOf Z G", "u3RowsOf Z G": the same as functions of the public instance.
No theorem of this file holds the vectors of "layersAt" and "headAt" against the law of the reads
("Fo.ReadsAll"; Johnson/HonestTrace/Reads.lean has it of "readAt" at any list of tables).

THE COVERED POSITIONS. The head's list reads which positions have a cost: that follows from two
words of the request. The structure Readers holds no request, so "cov" is an argument of its own:
"u3Rows Z G cov" IS THE DATA AT THE REQUEST OF WHICH cov IS MADE. No definition here reads G.cov:
the built data that a description's lots are handed are those of a request of zeros
("ProofFile.blankBy"). NO TEST HERE CAN SEE A cov OF ANOTHER REQUEST: three of the head's tables (hf under
phiZ: a part for each matrix of hf; hr under phiC; hr under rhoC) may then have other weights.

A TEST FOR EACH FILLER, BUT FOR THOSE THAT THE LIMITS NAME. The functions that are called fall back
on a filler (0, the empty array, the empty list, the first match) at shapes that they are not meant
for. Such a shape is rejected by a test with code: "u3Fits" where it hangs on public data,
"heardWhy" where it hangs on the challenges. The field "ready" of "u3Rows" asks both at the seat of
the address. IT DOES NOT ASK "u3AllFit": a segment without a seat has no address here, and at an
address that is no seat's "RowData.ask" accepts and nothing is laid. A caller asks "u3AllFit" too.
"RowData.at_" and "ArrayVals.val" ask neither: a caller that can reject reads through "RowData.ask".
"u3Fits" REJECTS: what "seatFits" rejects; a layout that has not one list of arrays for each segment
of the shape ("layFits"); what the plan's own test on a message's arrays ("msgFits") rejects; the
table of steps has a word that is not known; the segment's built data, or its plan, lacks; its sort
is none of the three; the built data's group is not the segment's; a place of the kinds K3, K4, K5
or K6, or its first step, lacks; the declared rounds from the lookup's first on, or from the
first of the segment's own rounds on, are not the entries of that sub-protocol's own table of
rounds; a reader of challenges counts other rounds than that table has; the lookup's rounds do not
end where the segment's own begin; at the layers: the plan is none for which their own rounds are
written, a product level of the gated products has fewer than nine variables, the tables are laid by
other rows or columns than the plan's, the laying returns nothing, the laid length is not the plan's
number of reads; that number is 0; the list of the matrices' names has not the length of the plan's
list, has an empty name, or names a later segment; the list by which the names are made has other
rows or columns than the plan's; a matrix of an earlier segment has no owner, or not its owner's
rows, or more columns than its owner has from its first on; at the head: the covered positions are
not as many as the positions; at the seat: the segment's own rounds do not end where the sending
begins, the array has not one row or not that number of columns, the message's main rows are not
over the extension field.
"ready" (the field of "u3Rows") REJECTS: what "u3Fits" rejects at the seat of the address; the
challenges are not as many as the rounds in front of the sending; a challenge has not the form that
its round declares ("drawsFit"); a maker of weights returns nothing; a part names a matrix beyond
the list, has a length that is 0 or does not divide the matrix's rows, or has not as many weights as
its length; the parts do not follow one another from entry 0 to the number of reads. THE FIELD
"ready" OF "u3Vals" ASKS NO TEST ON A SEAT: a caller that hands these values to "laidData" asks
"u3Fits" at the seat.

Limits. No theorem here ties the sampled values made here to those of a run of the verifier. The
tests hold the declared rounds against each sub-protocol's own table of rounds; that a reader takes
no more elements of a round than the table samples there is by reading. Z and G are two arguments:
nothing asks that G is made of Z. "Pub.roundsBefore?" takes the first step
of a name. Where a stage of the lookup is not in its list of stages, its reader takes rounds that
are not the lookup's: no test here sees that. The places' numbers of rounds are read off the public
table of steps, not off a description's list of sub-protocols. "RowData.at_" and "laidData" apply
all arguments at each call. In the text of "ArrayVals.val" here the list of parts stands behind the
first four arguments, in front of the function of row and column; in Lean's evaluator binding these
four was measured to save nothing: a caller that wants many entries binds the result of
"SegVals.vec". "ArrayVals.ready" goes by the
segment: this value holds one array a segment. These are definitions for small sizes. A value of
"readAt" is laid into the library's field by "Slice.toE": whether its three words are below the
prime is not asked. Nothing on any property of the protocol.

Not claimed: that a prover's program sends these entries; that a verifier accepts them; completeness
of the protocol; anything on what the entries reveal.
-/
import Johnson.HonestTrace.RowOfArray
import Johnson.HonestTrace.Reads
import Johnson.Desc.First.K4.Block
import Johnson.Desc.First.Look.Via.Rounds
import Johnson.Desc.First.Att.K5AttentionKind
import Johnson.Desc.Kinds.HeadKind
import Johnson.Desc.ProofFile.Honest.K4.Look
import Johnson.Desc.ProofFile.Honest.K3.WitOwner
import Johnson.Desc.ProofFile.Honest.K6.HeardWhole
import Johnson.Desc.ProofFile.Honest.K6.Part
import Johnson.Desc.K5.Honest.U3
import Johnson.Desc.First.Att.SeatC
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3

open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Honest (MsgAddr RowData RowDataOf ArrayVals Cells drawsFit msgFits layFits)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.K3 (matsOwn tlOf linkG linkA)
open ProofFile.Honest.K4 (k4LookOf k4LookRounds)
open ProofFile.Honest.K6 (headHeardWholeAt headParAt headInFront)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In ptsOf namedPts)
open OnBytes.Model.Layer (Lay TableAsk layTables tableAsks funsOf)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.First.K8.Honest (CellsAt)

local notation "readAtP" => VerifiableInference.Desc.First.K8.Honest.readAt

/-! ## Rejections under a name -/

/-- A value that is there, or a rejection under a name. -/
def have_ {α : Type} (name : String) : Option α → Except String α
  | some a => .ok a
  | none => .error name

/-- A test, or a rejection under a name. -/
def ask (name : String) (b : Bool) : Except String Unit := if b then .ok () else .error name

/-- The rejection, if any. -/
def errOf {α : Type} : Except String α → Option String
  | .error e => some e
  | .ok _ => none

/-! ## The vector at letters -/

/-- The tests on a list of parts: each by its matrix's number, its length, the number of its
weights and its first entry. sizes: the matrices' rows and columns. n: the number of reads. -/
def partsFit (sizes : Array (Nat × Nat)) (parts : List (Nat × Nat × Nat × Nat)) (n : Nat) :
    Except String Unit := do
  ask "U3: a part names a matrix beyond the list" (parts.all fun f => decide (f.1 < sizes.size))
  ask "U3: a part's length is 0 or does not divide its matrix's rows"
    (parts.all fun f => f.2.1 != 0 && (sizes.getD f.1 (0, 0)).1 % f.2.1 == 0)
  ask "U3: a part has not as many weights as its length" (parts.all fun f => f.2.2.1 == f.2.1)
  ask "U3: the parts do not follow one another from entry 0 to the number of reads"
    ((parts.foldl (fun (s : Option Nat) f =>
      s.bind fun p =>
        if f.2.2.2 == p then
          some (p + (sizes.getD f.1 (0, 0)).2 * ((sizes.getD f.1 (0, 0)).1 / f.2.1))
        else none) (some 0)) == some n)

/-- The rows and columns of a list of matrices. -/
def sizesOf (mats : Array TMat) : Array (Nat × Nat) := mats.map fun M => (M.m, M.k)

/-- A list of parts as "partsFit" reads it. -/
def partsOf (funs : Array HFun) : List (Nat × Nat × Nat × Nat) :=
  funs.toList.map fun f => (f.mat, f.len, f.phi.size, f.start)

/-- **The vector of reads of a group of layers**, of the cells; a rejection where the verifier's
maker of the weights returns nothing or its list does not pass "partsFit". n: the number of
reads. Of the vector, as at zzOf (Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is the array
before encoding: which part sends it, with which coins, is not said here." -/
def layersAt (mats : Array TMat) (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E))
    (laid : List (TableAsk × List (Nat × Nat))) (n : Nat) : Except String (CellsAt → Nat → E) :=
  match funsOf y fo pt laid with
  | none => .error "U3: the maker of the layers' weights returns nothing"
  | some funs =>
    match partsFit (sizesOf mats) (partsOf funs) n with
    | .error e => .error e
    | .ok _ => .ok fun cell => readAtP (parOfMats mats) funs.toList cell

/-- **The vector of reads of the output head**, of the cells. Of the vector, as at zzOf
(Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is the array before encoding: which part sends
it, with which coins, is not said here." -/
def headAt (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (x : Head.Heard) : Except String (CellsAt → Nat → E) :=
  match ReadsQuiet.tables h L hp cov x with
  | .error e => .error e
  | .ok t =>
    match partsFit (sizesOf hp.tl.mats) (partsOf t.funs) (hp.nU.getD 2 0) with
    | .error e => .error e
    | .ok _ => .ok fun cell => readAtP (parOfMats hp.tl.mats) t.funs.toList cell

/-! ## The values, by segment -/

/-- **What a segment's maker returns where it accepts the public data.** -/
structure SegVals where
  /-- PUBLIC: the number of reads: the vector's length -/
  n : Nat
  /-- PUBLIC: how many rounds of the first chain the vector's challenges span: the segment's own
  rounds end in front of round number front -/
  front : Nat
  /-- of the first front challenges of the chain: a rejection, or the vector, of the cells. Of the
  vector, as at zzOf (Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is the array before
  encoding: which part sends it, with which coins, is not said here." -/
  vec : List Fmt.Drawn → Except String (Cells → Nat → E)

/-- The segment's first place of a kind, and the number of the first chain's rounds in front of
it. -/
def placeIn (Z : Pub) (sps : List Spot) (seg : Nat) (k : KindName) :
    Except String (Spot × Nat) := do
  let sp ← have_ "U3: the segment has no place of a kind that is read"
    (sps.find? fun sp => sp.place.link == some seg && sp.place.kind == k)
  let c ← have_ "U3: a place has no step" sp.cuts.head?
  let n ← have_ "U3: the table of steps lacks a place's first step" (Z.roundsBefore? c.look)
  pure (sp, n)

/-- The entries of the n rounds that the public part declares from round number first on. -/
def declared (Z : Pub) (first n : Nat) : List Fmt.Entry :=
  ((Z.D.1.drop first).take n).map (·.entry)

/-- Every matrix of the segment's list to which an earlier segment has committed has an owner's
entry, with the same rows, and lies inside that entry's columns. -/
def borrowedFit (X : Verify.Public) (seg : Nat) : Bool :=
  (tlOf X seg).mats.all fun M =>
    M.kind != 1 || (decide (256 ≤ M.aId) &&
      match (tlOf X (linkG X (M.aId / 256 - 1))).mats[M.aId % 256]? with
      | some O => M.m == O.m && decide (M.ttOff + M.k ≤ O.k)
      | none => false)

/-- The tests on public data that all three makers ask. h: the lookup's shape; look0: its first
round; own0: the first of the segment's own rounds; n: the number of reads; mats: the plan's list of
matrices. -/
def fitsSeg (Z : Pub) (G : Ground) (seg : Nat) (h : Forest.Shape) (look0 own0 n : Nat)
    (mats : Array TMat) : Except String Unit := do
  ask "U3: the declared rounds are not the entries of the lookup's own table of rounds"
    (VerifiableInference.Desc.K3.entriesFit (VerifiableInference.Desc.K3.faceOf h)
      (declared Z look0 (k4LookRounds h)))
  ask "U3: the lookup's rounds do not end where the segment's own rounds begin"
    (look0 + k4LookRounds h == own0)
  ask "U3: the plan's number of reads is 0" (n != 0)
  ask "U3: the list of the matrices' names has not the length of the plan's list"
    ((matsOwn G.W seg).length == mats.size)
  ask "U3: a matrix has an empty name" ((matsOwn G.W seg).all fun m => m.2.1 != "")
  ask "U3: a matrix is read under a later segment" ((matsOwn G.W seg).all fun m => m.1 ≤ seg)
  ask "U3: the list by which the names are made has other rows or columns than the plan's"
    (sizesOf (tlOf G.W seg).mats == sizesOf mats)
  ask "U3: a matrix of an earlier segment does not lie inside its owner's" (borrowedFit G.W seg)

/-- **The values at the segment of group g of layers.** -/
def layersVals (Z : Pub) (G : Ground) (sps : List Spot) (seg g : Nat) : Except String SegVals := do
  let hp ← have_ "U3: the group of layers has no plan" G.W.G[g]?
  let k4 ← placeIn Z sps seg .K4
  let k3 ← placeIn Z sps seg .K3
  let P := G.W.layers
  let Q : K4Pub := { P, hp, g, link := seg, piece := k4.1.place.piece, r0 := k4.2, seg }
  ask "U3: the layers' own rounds are not written for this plan" (OnBytes.Desc.First.K4.covers P)
  ask "U3: a product level of the gated products has fewer than nine variables"
    (decide (9 ≤ P.rd.muH) && decide (9 ≤ P.rd.muH2))
  let own := OnBytes.Desc.First.K4.entries P hp g
  ask "U3: the declared rounds are not the entries of the layers' own table of rounds"
    (declared Z k4.2 own.length == own)
  ask "U3: the tables are laid by other rows or columns than the plan's"
    (OnBytes.Desc.First.K4.Honest.matsOf Q == sizesOf hp.tl.mats)
  let x ← have_ "U3: the laying of the layers' tables returns nothing"
    (layTables (OnBytes.Desc.First.K4.Honest.matsOf Q) (tableAsks P.y P.rd g) 0)
  ask "U3: the laid length is not the plan's number of reads" (x.2.2 == hp.nU.getD 2 0)
  fitsSeg Z G seg P.y.fo k3.2 k4.2 x.2.2 hp.tl.mats
  pure
    { n := x.2.2, front := k4.2 + own.length
      vec := fun heard =>
        -- STAND-INS: cell, w and tokv are 0, 0 and the empty array. By its text "ptsOf"
        -- (Johnson/Desc/K4/Honest/Front.lean) reads of this record the field look alone.
        let w : K4In :=
          { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := #[], look := k4LookOf P.y.fo k3.2 }
        let p := ptsOf Q w heard
        (layersAt hp.tl.mats P.y p.fo (namedPts Q p) x.2.1 x.2.2).map fun v C =>
          v (cellsAtOf C (matsOwn G.W seg)) }

/-- **The values at the attention segment of group g.** -/
def attVals (Z : Pub) (G : Ground) (sps : List Spot) (seg g : Nat) : Except String SegVals := do
  let A ← have_ "U3: the group's attention has no plan" G.W.A[g]?
  let k5 ← placeIn Z sps seg .K5
  let k3 ← placeIn Z sps seg .K3
  let own := (VerifiableInference.Desc.First.Att.P.rounds
    { link := seg, piece := k5.1.place.piece, own := A.own, before := []
      work := (OnBytes.Params.settingOf G.W.P.frame).workOf .field .request }).map (·.entry)
  ask "U3: the declared rounds are not the entries of attention's own table of rounds"
    (declared Z k5.2 own.length == own)
  ask "U3: the reader of attention's challenges counts other rounds than the table has"
    ((H2K5.Honest.cut A.own).sum == own.length)
  fitsSeg Z G seg A.fs k3.2 k5.2 A.nW A.mats
  pure
    { n := A.nW, front := k5.2 + own.length
      vec := fun heard => do
        let fo := k4LookOf A.fs k3.2 heard
        let P : H2K5.Honest.Pub5 := ⟨A.S, A.own⟩
        let t ← have_ "U3: the maker of attention's tables returns nothing"
          ((H2K5.Honest.ptsOf P ⟨fo.zk, heard.drop k5.2⟩).bind fun p =>
            VerifiableInference.Desc.First.Att.P.tablesP P.g (sizesOf A.mats) A.nW
              (VerifiableInference.Desc.First.Att.P.lookOf A.S.cf.lmb fo) p)
        partsFit (sizesOf A.mats) (t.funs.toList.map fun f => (f.mat, f.len, f.phi.size, f.start))
          A.nW
        pure fun C =>
          H2K5.Honest.u3Of (sizesOf A.mats)
            (fun a r c => ofInt (cellsAtOf C (matsOwn G.W seg) a r c)) t.funs }

/-- **The values at the output head's segment.** cov: the covered positions OF THE REQUEST AT HAND.
The request and the token that are handed to "headHeardWholeAt" are stand-ins: the maker of the
head's tables reads no field that is made of them ("tables_nine", "tables_fields",
Johnson/Desc/ProofFile/Honest/K6/HeardWhole.lean). -/
def headVals (Z : Pub) (G : Ground) (cov : Head.Covered) (sps : List Spot) (seg : Nat) :
    Except String SegVals := do
  let k6 ← placeIn Z sps seg .K6
  let k3 ← placeIn Z sps seg .K3
  let X := G.W
  let own := (headParAt G).rounds.map (·.entry)
  ask "U3: the declared rounds are not the entries of the head's own table of rounds"
    (declared Z k6.2 own.length == own)
  ask "U3: the reader of the head's challenges counts other rounds than the table has"
    (headInFront (headParAt G) 8 == own.length)
  ask "U3: the covered positions are not as many as the positions" (cov.sized X.hS.T)
  fitsSeg Z G seg X.HLy.fs k3.2 k6.2 (X.H.nU.getD 2 0) X.H.tl.mats
  pure
    { n := X.H.nU.getD 2 0, front := k6.2 + own.length
      vec := fun heard => do
        let x ← headHeardWholeAt (headParAt G)
          (VerifiableInference.Desc.Kinds.Head.requestOf Z.s₀) 0 (k4LookOf X.HLy.fs k3.2 heard)
          k6.2 heard
        let v ← headAt X.hS X.HLy X.H cov x
        pure fun C => v (cellsAtOf C (matsOwn X seg)) }

/-- **The values at a segment**, by its sort. -/
def valsAt (Z : Pub) (G : Ground) (cov : Head.Covered) (seg : Nat) : Except String SegVals := do
  let sps ← have_ "U3: the table of steps has a word that is not known" (spotsOf Z.cuts)
  let Y ← have_ "U3: the segment's built data lacks" G.built[seg]?
  ask "U3: the built data's group is not the segment's"
    (Y.kind != 0 || linkG G.W Y.g == seg)
  ask "U3: the built data's group is not the segment's"
    (Y.kind != 1 || linkA G.W Y.g == seg)
  if Y.kind == 0 then layersVals Z G sps seg Y.g
  else if Y.kind == 1 then attVals Z G sps seg Y.g
  else if Y.kind == 2 then headVals Z G cov sps seg
  else .error "U3: the segment's sort is none of the three"

/-- **Why the values are not ready at a list of challenges**; nothing if they are. heard: the
challenges in front of the sending. -/
def heardWhy (Z : Pub) (V : SegVals) (heard : List Fmt.Drawn) : Option String :=
  errOf (do
    ask "U3: the challenges are not as many as the rounds in front of the sending"
      (heard.length == V.front)
    ask "U3: a challenge has not the form that its round declares"
      (drawsFit (Z.D.1.take V.front) heard)
    let _ ← V.vec heard
    pure ())

/-! ## The laying -/

/-- The seats of U3's messages. -/
def u3Seats (Z : Pub) (G : Ground) : List Seat := seatsOf Z G "U3"

/-- The addresses of U3's messages. -/
def u3Mine (Z : Pub) (G : Ground) : MsgAddr → Bool := mineOf (u3Seats Z G)

/-- The tests that hold a seat against its segment's values. -/
def seatAsks (s : Seat) (V : SegVals) : Except String Unit := do
  ask "U3: the segment's own rounds do not end where the sending begins" (V.front == s.heard)
  ask "U3: the array has not one row" (s.array.sizeI == 1)
  ask "U3: the array's columns are not the plan's number of reads" (s.array.sizeC == V.n)
  ask "U3: the message's main rows are not over the extension field" (s.shape.mainDeg == 3)

/-- A seat's values, where the seat and the public data pass all tests. -/
def seated (Z : Pub) (G : Ground) (cov : Head.Covered) (s : Seat) : Except String SegVals := do
  match seatWhy s with
  | some e => .error e
  | none =>
    ask "U3: the layout has not one list of arrays for each segment of the shape"
      (layFits G.first.shape G.first.layout)
    ask "U3: the message's arrays do not pass the plan's own test on a message"
      (msgFits G.first.codes G.first.shape G.first.layout s.seg s.array.message)
    let V ← valsAt Z G cov s.seg
    seatAsks s V
    pure V

/-- **Why a seat does not fit, on public data**; nothing if it does. -/
def u3FitsWhy (Z : Pub) (G : Ground) (cov : Head.Covered) (s : Seat) : Option String :=
  errOf (seated Z G cov s)

/-- **THE TEST ON PUBLIC DATA AT A SEAT.** -/
def u3Fits (Z : Pub) (G : Ground) (cov : Head.Covered) (s : Seat) : Bool :=
  (u3FitsWhy Z G cov s).isNone

/-- Every segment has a seat, no two seats have one address, and every seat fits. -/
def u3AllFit (Z : Pub) (G : Ground) (cov : Head.Covered) : Bool :=
  allSeated G.first.shape.link.length (u3Seats Z G) &&
    pairwise (fun s t => s.addr != t.addr) (u3Seats Z G) && (u3Seats Z G).all (u3Fits Z G cov)

/-- **Why the data is not ready at a seat, at the challenges heard in front of its sending**;
nothing if it is. A seat that does not fit on public data is not ready. At a seat of "u3Seats Z G",
the first of its address, the field "ready" of "u3Rows" accepts just where this returns nothing. -/
def u3Why (Z : Pub) (G : Ground) (cov : Head.Covered) (s : Seat) (heard : List Fmt.Drawn) :
    Option String :=
  match seated Z G cov s with
  | .error e => some e
  | .ok V => heardWhy Z V heard

/-- **U3's VALUES, AS THE LAYING TAKES THEM**: one array of the name "U3" at each segment of the
request's shape. cov: the covered positions of the request at hand. Of the readers it reads the
cells alone. Where a maker rejects the public data the segment has no array here: "u3AllFit" rejects
that. "ready" goes by the segment alone: IT ASKS NO TEST ON A SEAT. Whoever lays these values asks
"u3Fits" at the seat. Of the vector, as at zzOf (Johnson/Desc/ProofFile/Honest/K8/Digits.lean):
"This is the array before encoding: which part sends it, with which coins, is not said here." -/
def u3Vals (Z : Pub) (G : Ground) (cov : Head.Covered) : ArrayVals :=
  let made : List (Nat × Except String SegVals) :=
    (List.range G.first.shape.link.length).map fun l => (l, valsAt Z G cov l)
  let at_ (l : Nat) : Option SegVals := (made.lookup l).bind (·.toOption)
  { size := fun l name => if name == "U3" then (at_ l).map fun V => (1, V.n) else none
    val := fun R heard l _ =>
      match (at_ l).bind fun V => (V.vec heard).toOption with
      | some v =>
        let u := v R.cells
        fun _ c => .inr (OnBytes.Slice.toE (u c).triple)
      | none => fun _ _ => .inr (OnBytes.Slice.toE (0, 0, 0))
    ready := fun heard l =>
      match at_ l with
      | some V => (heardWhy Z V heard).isNone
      | none => false }

/-- **THE DATA OF U3's MESSAGES**: the values, laid at the seats. At a seat's address its field
"ready" also asks "u3Fits" at that seat (of two seats of one address: at the first). At an address
that is no seat's nothing turns: it accepts there, and nothing is laid. These are the rows' data
before encoding: with which coins they are encoded is not said here; the address is the seat's
(Johnson/HonestTrace/SeatOf.lean). -/
def u3Rows (Z : Pub) (G : Ground) (cov : Head.Covered) : RowData :=
  let seats := u3Seats Z G
  let fit := seats.map fun s => (s.addr, u3Fits Z G cov s)
  let D := laidRows G seats (u3Vals Z G cov)
  { D with ready := fun h a => D.ready h a && (fit.find? fun x => x.1 == a).all (·.2) }

/-! ## Of the public instance -/

/-- The covered positions of an instance's request, by the description's own function on the first
state with the request's words laid in. The token 0 is a stand-in for the reply: which positions
have a cost does not hang on it. A rejection where that function rejects the request's words. -/
def covOf (Z : Pub) (G : Ground) (x : ProofFile.Inst) : Except String Head.Covered :=
  (Z.s₀.withReq (Verify.words32 x.pub.request)).coveredAt G.W.T G.W.P.h.V 0

/-- Why "covOf" rejects an instance's request; nothing if it accepts. -/
def covWhy (Z : Pub) (G : Ground) (x : ProofFile.Inst) : Option String := errOf (covOf Z G x)

/-- **U3's VALUES, OF THE PUBLIC INSTANCE.** Of the instance it reads the request's words. Where
"covOf" rejects them the covered positions are empty: at a plan with a position "headVals" then
rejects: the head's segment has no array, and is not ready. The other segments' values do not hang
on the request: they stay. "covWhy" has covOf's own reason. Of the vector, as at zzOf
(Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is the array before encoding: which part sends
it, with which coins, is not said here." -/
def u3ValsOf (Z : Pub) (G : Ground) (x : ProofFile.Inst) : ArrayVals :=
  u3Vals Z G ((covOf Z G x).toOption.getD default)

/-- **THE DATA OF U3's MESSAGES, OF THE PUBLIC INSTANCE**: as "u3ValsOf": where "covOf" rejects the
request's words nothing is laid at the head's segment, and its message is not ready. These are the
rows' data before encoding: with which coins they are encoded is not said here; the address is the
seat's (Johnson/HonestTrace/SeatOf.lean). -/
def u3RowsOf (Z : Pub) (G : Ground) : RowDataOf ProofFile.Inst := fun x =>
  u3Rows Z G ((covOf Z G x).toOption.getD default)

end OnBytes.HonestTrace.U3
