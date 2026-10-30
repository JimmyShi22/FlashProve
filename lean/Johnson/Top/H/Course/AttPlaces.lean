-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Course/AttPlaces.lean: the nine places of an attention link of a proof file's first
chain as relations on what the verifier holds: for each place the success of its routine, and then
of the calls behind it that take no round.

No soundness: a test. This module serves a tool that runs, step by step, the verifier program of
OnBytes/Iop, OnBytes/Model and OnBytes/Proof (written by hand after the C++ source); it states
nothing on soundness.

Definitions alone, in the form of Johnson/Top/H/Course/LayPlaces.lean.
Johnson/Top/H/Course/AttCourse.lean [not in this library] shows that a run of the verifier's routine
for a link is these relations behind each other.

Which cut of a link: as in LayPlaces.lean: ONE CALL of runLinkH (OnBytes/Model/StagesLinks.lean):
the code switch first, the link's closing last. It is the cut of AttBorders
(OnBytes/Tie/Pv/Att/AttBorders.lean).

What the verifier holds. AttLoc lists the values that the text of runLinksFrom, runLinkH,
Attention.run, Attention.hear and HTailF2.transcriptF holds under local names. TWO OF THEM ARE THE
WALK's, check and out: runLinkH takes them and returns them. The other ten die with the link. A
value that is not yet made stands in the record as whatever stood there: no relation reads it
before the relation that writes it. So the record is a product, and no value is made up.

Where an attention link parts from a layers' link:
  the smallness test's record (tl) is made behind place 1, by Seam.start;
  behind the lookup on the calls there is no test;
  place 3 is three routines in a row, each of which takes rounds: scores, divide, attain;
  the list of the reads' arrays is public;
  behind place 4 a block runs that takes no round and may turn the context (Attention.tables);
  the batching draw stands at the next free slot as read anew behind the setting of the plan's
    number of claims;
  the claims are one routine;
  behind place 9 a routine runs (Attention.countsHeld), and the link leaves no row on the table.

Main names:
  AttLoc: the local values. AttLoc.walk: the walk's two. AttLink: the public letters of one link.
  heardAt P a: the record that the claims are handed.
  AFirstCall, AFirstQuiet; ALookCall; AOwnCall; AReadsCall, AReadsQuiet; ADrawCall; ADigitsCall;
    ADigitsLook, ADigitsQuiet; ABatchCall, ABatchQuiet; ADoorCall, ADoorQuiet.
  callA D i, quietA D i, placeA D i: the families; place i + 1 of the link has the number i.

BEYOND THE NUMBER 8 callA, quietA AND placeA HOLD OF ALL STATES. They are set to hold there, not to
fail: of a relation that never holds, every law would hold emptily. No statement is meant at these
numbers.

An attention link is never the first of a chain at the program's own lists: the clause of the calls
behind the first routine that speaks of link 0 is idle there. It stands as the text has it.

What is not claimed. Nothing is proved here. Nothing here asks that the field failed of the context
is none: a named test on values (Blk.check, Blk.checkOnView) that has failed earlier in the run
shows there alone. Nothing says that X.kind is 1 or that X.run is Attention.run P, returning none:
the relations are written for such a link. What the routines do to the values is not said: a
relation is the routines' own equations. The nine places are written by hand off the program's text:
no theorem of this library ties them to a run of the program's routine
(Johnson/Top/H/Course/AttCourse.lean [not in this library] does), nothing ties them to the list of a
proof file's rounds, and no lemma ties them to the library's own cut of the link (AttBorders).

-/
import Johnson.Top.H.Course.LocRel
import OnBytes.Model.StagesLinks
import OnBytes.Model.Attention

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- What the verifier's text holds under local names between two places of an attention link. The
first two fields are the walk's: they live from link to link. The other ten are the link's. -/
structure AttLoc where
  /-- the walk's: the state of the calls over the links -/
  check : ChainCheck
  /-- the walk's: what the links have returned so far -/
  out : Proof.LinksResult
  /-- the link's state -/
  L : LinkCtx
  /-- the sub-proof's state; the ledger of claims lies in it -/
  F : Fork
  /-- the smallness test's record -/
  tl : HTailF2
  /-- what the lookup on the calls has returned -/
  g : Forest.Heard
  /-- the plane claims -/
  planes : Array Attention.PlaneClaim
  /-- the units of the scores -/
  scores : Array Attention.Score
  /-- the division and the value product -/
  d : Attention.Divide
  /-- the maximum and the index's bits -/
  x : Attention.Attain
  /-- the tables and their weights -/
  t : Attention.Tables
  /-- the next free slot in front of the draw of the matrix -/
  slotA : Nat

/-- The walk's two values. -/
def AttLoc.walk (a : AttLoc) : ChainCheck × Proof.LinksResult := (a.check, a.out)

/-- The public letters of one attention link: the arguments of runLinkH but for the two that it
hands on, and the sub-proof's plan. -/
structure AttLink where
  /-- all links -/
  links : Array LinkH
  /-- the first chain's parameters -/
  p : Params.First
  /-- the layout of the weights -/
  wsLay : WsLay
  /-- the link's number -/
  l : Nat
  /-- the link's record -/
  X : LinkH
  /-- the sub-proof's plan -/
  P : Attention.Plan

/-- The record that Attention.run hands to its claims. -/
def heardAt (P : Attention.Plan) (a : AttLoc) : Attention.Heard :=
  { S := P.S, g := a.g, planes := a.planes, scores := a.scores, d := a.d, x := a.x, t := a.t,
    iU3 := P.iU3 }

section Places
variable (D : AttLink) (a : AttLoc) (x : Ctx) (a' : AttLoc) (x' : Ctx)

/-- Place 1, the routine: the chain's first call for the link. -/
structure AFirstCall : Prop where
  first : a.check.first x = .ok (a'.check, x')
  same : a' = { a with check := a'.check }

/-- Place 1, behind the routine: the tests of runLinkH, the link's first state, and the start of
the sub-proof's routine, which makes the smallness test's record. -/
structure AFirstQuiet : Prop where
  masks : (D.l == 0) = true → indexMasksH D.links D.p a.check x = .ok (a'.out.indexMasks, x)
  masks' : ¬(D.l == 0) = true → a'.out.indexMasks = a.out.indexMasks
  noPlain : (a.check.plain.size == 0) = true
  atLink : (a.check.link == D.l) = true
  ctx : x' = x
  same : a' = { a with
    out := { a.out with indexMasks := a'.out.indexMasks }
    L := { check := a.check, link := D.l, arrayOf := D.X.arrayOf, list := D.X.Tp }
    F := D.X.Fp.fillL.slots D.P.ns
    tl := { D.P.seam.tl with funClosed := false, foldDrawn := 0 } }

/-- Place 2: the lookup on the calls. -/
structure ALookCall : Prop where
  pad : Forest.pad (D.P.S.calls.map (·.call)) D.P.fs.pub D.P.lid a.F x = .ok ((a'.g, a'.F), x')
  same : a' = { a with g := a'.g, F := a'.F }

/-- Place 3 at the states and contexts between its three routines. -/
structure AOwnCallAt (G₁ G₂ : Fork) (y₁ y₂ : Ctx) : Prop where
  scores : Attention.scores D.P.S a.g.zk a.F x = .ok (((a'.planes, a'.scores), G₁), y₁)
  divide : Attention.divide D.P.S a.g.zk G₁ y₁ = .ok ((a'.d, G₂), y₂)
  attain : Attention.attain D.P.S G₂ y₂ = .ok ((a'.x, a'.F), x')
  same : a' = { a with planes := a'.planes, scores := a'.scores, d := a'.d, x := a'.x, F := a'.F }

/-- Place 3: the sub-proof's own rounds: three routines in a row. -/
def AOwnCall : Prop := ∃ G₁ G₂ y₁ y₂, AOwnCallAt D a x a' x' G₁ G₂ y₁ y₂

/-- Place 4, the routine: the sending of the reads. -/
structure AReadsCall : Prop where
  root : rootInH [D.P.iU3] a.L a.F x = .ok ((((), a'.L), a'.F), x')
  same : a' = { a with L := a'.L, F := a'.F }

/-- Place 4, behind the routine: the list of tables is open; the tables and their weights, by a
block that takes no round; the list is closed; then the head of HTailF2.transcriptF: two public
tests, the next free slot, and the test on the order on which the draw of the matrix relies. The
last three tests are said of the state behind. -/
structure AReadsQuiet : Prop where
  funOpen : a.tl.funOpen = true
  tables : Attention.tables D.P.S D.P.mats D.P.nW a.g a.planes a.scores a.d a.x x = .ok (a'.t, x')
  closed : a.tl.closeFuns a'.t.funs = some a'.tl
  funClosed : a'.tl.funClosed = true
  map : (a'.tl.shp.size == a'.tl.NM) = true
  order : (a'.L.check.link == a'.L.link && decide (a'.L.link < a'.L.check.links) &&
      a'.tl.gtTree.size == a'.tl.NM && a'.tl.gtTree.all (HTailF2.arrayFixed a'.L x'.st) &&
    (List.range 4).all fun n =>
      Option.all (HTailF2.arrayFixed a'.L x'.st) (a'.tl.ix.U.getD n none)) = true
  same : a' = { a with t := a'.t, tl := a'.tl, slotA := a.F.next }

/-- Place 5: the draw of the matrix. -/
structure ADrawCall : Prop where
  draw : a.tl.drawMatrixF a.F x = .ok ((a'.tl, a'.F), x')
  same : a' = { a with tl := a'.tl, F := a'.F }

/-- Place 6: the sending of the digits. -/
structure ADigitsCall : Prop where
  root : rootInH [a.tl.ix.ZZ, a.tl.ix.BZ] a.L a.F x = .ok ((((), a'.L), a'.F), x')
  same : a' = { a with L := a'.L, F := a'.F }

/-- Place 7, the routine, at what it returns. What it returns is written into the record. -/
structure ADigitsLookAt (gz : Forest.Heard) : Prop where
  pad : Forest.pad #[a.tl.z1.call, a.tl.z2.call] a.tl.f9.pub a.tl.lidb a.F x =
    .ok ((gz, a'.F), x')
  same : a' = { a with
    F := a'.F
    tl := { a.tl with
      foldDrawn := a.tl.foldDrawn + 1, slotA := a.slotA, slotB := a'.F.next, heard := some gz } }

/-- Place 7, the routine: the lookup on the digits. -/
def ADigitsLook : Prop := ∃ gz, ADigitsLookAt a x a' x' gz

/-- Place 7, behind the routine: the slots are counted and the plan's number of claims is set. -/
structure ADigitsQuiet : Prop where
  slots : (a.F.next == D.P.nMsg) = true
  setPlan : SubM.setPlanClaims D.P.nLin a.F x = .ok (((), a'.F), x')
  same : a' = { a with F := a'.F }

/-- Place 8, the routine: the batching draw, at the next free slot. -/
structure ABatchCall : Prop where
  batch : t2Batch a.F.next a.L a.F x = .ok ((((), a'.L), a'.F), x')
  same : a' = { a with L := a'.L, F := a'.F }

/-- Place 8, behind the routine, at the states and contexts between its parts. -/
structure ABatchQuietAt (G₁ G₂ G₃ G₄ G₅ : Fork) (y₁ y₂ y₃ y₄ y₅ : Ctx) : Prop where
  claims : Attention.claims D.P (heardAt D.P a) a.F x = .ok (((), G₁), y₁)
  objects : a.tl.objectsF a.t.funs G₁ y₁ = .ok ((a'.tl, G₂), y₂)
  noFree : Attention.noFreeSlot D.P.nMsg G₂ y₂ = .ok (((), G₃), y₃)
  held : a'.tl.funsHeld a.t.funs = true
  selfTest : a'.tl.selfTestF D.P.seam.nU G₃ y₃ = .ok (((), G₄), y₄)
  coefficients : a'.tl.coefficientsF G₄ y₄ = .ok (((), G₅), y₅)
  tile : a'.tl.tileSelfTestF G₅ y₅ = .ok (((), a'.F), x')
  same : a' = { a with F := a'.F, tl := a'.tl }

/-- Place 8, behind the routine: the claims and the tests on them. -/
def ABatchQuiet : Prop :=
  ∃ G₁ G₂ G₃ G₄ G₅ y₁ y₂ y₃ y₄ y₅, ABatchQuietAt D a x a' x' G₁ G₂ G₃ G₄ G₅ y₁ y₂ y₃ y₄ y₅

/-- Place 9, the routine, at the number of equations laid. -/
structure ADoorCallAt (laid : Nat) : Prop where
  laidIs : a.tl.equationsLaidF = some laid
  door : doorH laid a.L a.F x = .ok ((((), a'.L), a'.F), x')
  same : a' = { a with L := a'.L, F := a'.F }

/-- Place 9, the routine: the closing of the link. -/
def ADoorCall : Prop := ∃ laid, ADoorCallAt a x a' x' laid

/-- Place 9, behind the routine: the routine's last counts, the two tests of runLinkH, and what
runLinkH returns: the walk's two values. The link leaves no row on the table. -/
structure ADoorQuiet : Prop where
  counts : Attention.countsHeld D.P a.tl a.F x = .ok (((), a'.F), x')
  closed : (a.L.handed && a.L.done) = true
  plan : samePlan D.X a'.F a.L.list = true
  noRow : ¬D.X.fv = true
  same : a' = { a with check := a.L.check, F := a'.F }

end Places

/-- The nine routines. Beyond the number 8 the relation holds of all states. -/
def callA (D : AttLink) : Nat → LocRel AttLoc
  | 0 => AFirstCall
  | 1 => ALookCall D
  | 2 => AOwnCall D
  | 3 => AReadsCall D
  | 4 => ADrawCall
  | 5 => ADigitsCall
  | 6 => ADigitsLook
  | 7 => ABatchCall
  | 8 => ADoorCall
  | _ => fun _ _ _ _ => True

/-- The calls behind the nine routines. Beyond the number 8 the relation holds of all states. -/
def quietA (D : AttLink) : Nat → LocRel AttLoc
  | 0 => AFirstQuiet D
  | 1 => LocRel.still
  | 2 => LocRel.still
  | 3 => AReadsQuiet D
  | 4 => LocRel.still
  | 5 => LocRel.still
  | 6 => ADigitsQuiet D
  | 7 => ABatchQuiet D
  | 8 => ADoorQuiet D
  | _ => fun _ _ _ _ => True

/-- The nine places: the routine, then the calls behind it. -/
def placeA (D : AttLink) (i : Nat) : LocRel AttLoc := LocRel.comp (callA D i) (quietA D i)

end KObj.Course
