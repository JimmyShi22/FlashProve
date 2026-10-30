-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Course/LayPlaces.lean: the nine places of a layers' link of a proof file's first chain
as relations on what the verifier holds: for each place the success of its routine, and then of the
calls behind it that take no round.

No soundness: a test. This module serves a tool that runs, step by step, the verifier program of
OnBytes/Iop, OnBytes/Model and OnBytes/Proof (written by hand after the C++ source); it states
nothing on soundness.

Definitions alone. Johnson/Top/H/Course/LayCourse.lean [not in this library] shows that a run of the
verifier's routine for a link is these relations behind each other.

Which cut of a link. The library cuts a link in two ways, one place apart. Here a link is ONE CALL
of runLinkH (OnBytes/Model/StagesLinks.lean): the link's own first call (the code switch; at the
first link a sending) comes first, its closing last. That is the cut of the table planS
(Johnson/E/KObj/Plan0S.lean), of att_link_law (Johnson/Top/H/AttLinkLaw.lean), of LayBorders
(OnBytes/Tie/Pv/Lay/LayBorders.lean) and of fileRan_link_cut (OnBytes/Tie/Pv/Keeps/KeepsCut.lean).
The cut from door to door (link_meet, door_law, the maker of Johnson/Top/H/IterMeet.lean) is the
places 2 to 9 of this file and place 1 of the next link.

What the verifier holds. The nine routines read more than the context of the blocks (OnBytes.Ctx):
values that the text of runLinksFrom, runLinkH, Layer.runForkHidG2 and HTailF2.transcriptF holds
under local names. LayLoc lists them. TWO OF THEM ARE THE WALK's, check and out: runLinkH takes them
and returns them, so they live from link to link, whatever the kind of the link. The other six die
with the link.

A place is two relations behind each other: call D i, the success of the routine that takes the
place's rounds, and quiet D i, the successes and tests of the calls behind it that take no round, up
to the next place's routine. So one state stands between two places, and a test that guards the next
routine stands in the place in front, said of the state behind that place. Each relation has one
equation, same, that names the local values that it writes: it leaves all others.

The slot at the batching draw. The text hands t2Batch the next free slot as read behind the lookup
on the digits. The smallness test's record holds that number (slotB), so the relation stands at
a.tl.slotB. That it is the plan's number (hp.used) is a test of the place in front.

Main names:
  RunAll rs F c F' c': routines of the sub-proof's engine, run one behind the other.
  claimsFront, claimsBack, tailTests: the routines between t2Batch and doorH, in the text's order.
  LayLoc: the local values. LayLink: the public letters of one link.
  LayRel, LayRel.comp, LayRel.still, relRow.
  FirstCall, FirstQuiet; LookCall, LookQuiet; OwnCall; ReadsCall, ReadsQuiet; DrawCall; DigitsCall;
    DigitsLook, DigitsQuiet; BatchCall, BatchQuiet; DoorCall, DoorQuiet.
  call D i, quiet D i, place D i: the families; place i + 1 of the link has the number i.

BEYOND THE NUMBER 8 call, quiet AND place HOLD OF ALL STATES. They are set to hold there, not to
fail: of a relation that never holds, every law would hold emptily. No statement is meant at these
numbers.

What is not claimed. Nothing is proved here. No theorem of this library ties these relations to a
run of the program's routine: they were written by hand off its text, and that they repeat it rests
on reading alone. A routine succeeds here also where a named test on values (Blk.check,
Blk.checkOnView) has failed inside it: such a failure shows only in the field failed of the context
behind the place. Nothing says that X.kind is 0 or that X.run is some <$> Layer.runForkHidG2 P hp g:
the relations are written for such a link. What the routines do to the values is not said: a
relation is the routines' own equations. The lists claimsFront, claimsBack and tailTests repeat the
order of the text of Layer.runForkHidG2. Attention's links and the head's are not treated.

-/
import OnBytes.Model.StagesLinks
import OnBytes.Model.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-! ### the calls between the batching draw and the closing -/

/-- Routines of the sub-proof's engine that return nothing, run one behind the other. -/
inductive RunAll : List (SubM Unit) → Fork → Ctx → Fork → Ctx → Prop
  | nil (F : Fork) (c : Ctx) : RunAll [] F c F c
  | cons {r : SubM Unit} {rs : List (SubM Unit)} {F G F' : Fork} {c d c' : Ctx}
      (h : r F c = .ok (((), G), d)) (t : RunAll rs G d F' c') : RunAll (r :: rs) F c F' c'

/-- The list of claims of a layers' sub-proof, up to the smallness test's. -/
def claimsFront (P : Layer.Pub) (g : Nat) (o : Layer.Own) : List (SubM Unit) :=
  (get >>= fun s => Layer.note "the element that batches the claims" s.theta : SubM Unit) ::
  Forest.objects o.H.fo ::
  Layer.noteClaims "the look-up's own claims" ::
  Layer.claimsNorms P o.v o.H ::
  Layer.noteClaims "the sums of squares" ::
  Layer.claimRowBatch P.y o.H ::
  (if (P.y.h.xl == 5) = true then Layer.claimsLedger5 o.v o.H
    else Layer.claimsLedger4 o.v o.H) ::
  Layer.noteClaims "the norms' rows" ::
  Layer.claimsTerms o.v o.H ::
  Layer.noteClaims "the second token sum-check's shown values" ::
  Layer.claimsGated P o.v o.hd o.hd2 ::
  Layer.noteClaims "the gated products" ::
  Layer.claimsOneHot o.v ::
  Layer.claimsPlanes o.v o.H.fo ::
  (if (g == 0) = true then
    [Layer.claimEmbedding o.v o.H o.sVE, Layer.noteClaims "the planes and the embedding"]
  else [Layer.noteClaims "the planes and the embedding"])

/-- The claims behind the smallness test's, and the test that every slot occurs in a claim. -/
def claimsBack (hp : Layer.HPlan2) (g : Nat) (o : Layer.Own) : List (SubM Unit) :=
  [Layer.noteClaims "the smallness test", SubM.lin o.K.rowS, Forest.joinAdded o.H.fo,
    SubM.lin (Aff.slot o.K.sA0 - o.K.fin.Alin), SubM.lin (Aff.slot o.K.sB0 - o.K.fin.Blin),
    wsForkLin o.wo.toWsMerged, Layer.noteClaims "all claims",
    Layer.freeSlotTest g hp.used o.wo.sFv]

/-- The smallness test's three tests of its own books. -/
def tailTests (hp : Layer.HPlan2) (tl : HTailF2) : List (SubM Unit) :=
  [tl.selfTest hp.nU, tl.coefficients, tl.rkSelfTest]

/-! ### the local values -/

/-- What the verifier's text holds under local names between two places of a layers' link. The first
two fields are the walk's: they live from link to link. The other six are the link's. -/
structure LayLoc where
  /-- the walk's: the state of the calls over the links -/
  check : ChainCheck
  /-- the walk's: what the links have returned so far: the index masks' message, the pending rows,
  the reply -/
  out : Proof.LinksResult
  /-- the link's state -/
  L : LinkCtx
  /-- the sub-proof's state; the ledger of claims lies in it -/
  F : Fork
  /-- what the lookup on the calls has returned -/
  fo : Forest.Heard
  /-- what the own rounds have returned -/
  own : Layer.Own
  /-- the smallness test's record -/
  tl : HTailF2
  /-- the next free slot in front of the draw of the matrix -/
  slotA : Nat

/-- The public letters of one layers' link: the arguments of runLinkH but for the two that it hands
on, and those of Layer.runForkHidG2. -/
structure LayLink where
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
  /-- the layers' public numbers, with the request's tokens -/
  P : Layer.Pub
  /-- the sub-proof's plan -/
  hp : Layer.HPlan2
  /-- the group of layers -/
  g : Nat

/-- A relation between two states of a layers' link: local values and the context of the blocks. -/
abbrev LayRel : Type := LayLoc → Ctx → LayLoc → Ctx → Prop

/-- Two relations behind each other. -/
def LayRel.comp (R Q : LayRel) : LayRel :=
  fun a x a'' x'' => ∃ a' x', R a x a' x' ∧ Q a' x' a'' x''

/-- Nothing happens. -/
def LayRel.still : LayRel := fun a x a' x' => a' = a ∧ x' = x

/-- A head's relation and the relations 0 to n behind each other. -/
def relRow (Rh : LayRel) (R : Nat → LayRel) : Nat → LayRel
  | 0 => LayRel.comp Rh (R 0)
  | n + 1 => LayRel.comp (relRow Rh R n) (R (n + 1))

/-! ### the nine places -/

section Places
variable (D : LayLink) (a : LayLoc) (x : Ctx) (a' : LayLoc) (x' : Ctx)

/-- Place 1, the routine: the chain's first call for the link. -/
structure FirstCall : Prop where
  first : a.check.first x = .ok (a'.check, x')
  same : a' = { a with check := a'.check }

/-- Place 1, behind the routine: the tests of runLinkH, the link's first state, and the head of the
sub-proof's routine. The text also reads the number of the reads' array here (hp.tl.ix.U.getD 2
none); the relations say that reading at place 4 (ReadsCallAt.reads). It hangs on the plan alone. -/
structure FirstQuiet : Prop where
  masks : (D.l == 0) = true → indexMasksH D.links D.p a.check x = .ok (a'.out.indexMasks, x)
  masks' : ¬(D.l == 0) = true → a'.out.indexMasks = a.out.indexMasks
  noPlain : (a.check.plain.size == 0) = true
  atLink : (a.check.link == D.l) = true
  group : (a'.L.link == if D.P.y.h.p4 = true then 2 * D.g else D.g) = true
  sizes : (a'.L.list.nt == D.hp.Tp.nt &&
    (D.X.Fp.trees.map fun X => (X.R, X.K)) == D.hp.Fp.trees.map fun X => (X.R, X.K)) = true
  ctx : x' = x
  same : a' = { a with
    out := { a.out with indexMasks := a'.out.indexMasks }
    L := { check := a.check, link := D.l, arrayOf := D.X.arrayOf, list := D.X.Tp }
    F := D.X.Fp.fillL.slots D.hp.ns }

/-- Place 2, the routine: the lookup on the calls. -/
structure LookCall : Prop where
  pad : Forest.pad D.P.y.cl D.P.y.fo.pub D.P.y.h.lidb a.F x = .ok ((a'.fo, a'.F), x')
  same : a' = { a with fo := a'.fo, F := a'.F }

/-- Place 2, behind the routine: the test on the lookup's numbers. -/
structure LookQuiet : Prop where
  look : (a.fo.shape.dT == D.P.y.fo.dT && a.fo.shape.kT == D.P.y.fo.kT &&
    a.fo.shape.NT == D.P.y.fo.NT && a.fo.shape.rK == D.P.y.fo.rK &&
    a.fo.shape.first == D.P.y.fo.first && a.fo.shape.iota == D.P.y.fo.iota &&
    a.fo.shape.callOf == D.P.y.fo.callOf) = true
  ctx : x' = x
  same : a' = a

/-- Place 3: the sub-proof's own rounds. -/
structure OwnCall : Prop where
  own : Layer.hearOwn D.P D.hp D.g a.fo a.F x = .ok ((a'.own, a'.F), x')
  same : a' = { a with own := a'.own, F := a'.F }

/-- Place 4, the routine, at the number iU3 of the reads' array. -/
structure ReadsCallAt (iU3 : Nat) : Prop where
  reads : D.hp.tl.ix.U.getD 2 none = some iU3
  root : rootInH [iU3] a.L a.F x = .ok ((((), a'.L), a'.F), x')
  same : a' = { a with L := a'.L, F := a'.F }

/-- Place 4, the routine: the sending of the reads. -/
def ReadsCall : Prop := ∃ iU3, ReadsCallAt D a x a' x' iU3

/-- Place 4, behind the routine: the list of tables is closed; then the head of
HTailF2.transcriptF: two public tests, the next free slot, and the test on the order on which the
draw of the matrix relies. All tests are said of the state behind. -/
structure ReadsQuiet : Prop where
  closed : D.hp.tl.closeFuns a.own.funs = some a'.tl
  funClosed : a'.tl.funClosed = true
  map : (a'.tl.shp.size == a'.tl.NM) = true
  order : (a'.L.check.link == a'.L.link && decide (a'.L.link < a'.L.check.links) &&
      a'.tl.gtTree.size == a'.tl.NM && a'.tl.gtTree.all (HTailF2.arrayFixed a'.L x'.st) &&
    (List.range 4).all fun n =>
      Option.all (HTailF2.arrayFixed a'.L x'.st) (a'.tl.ix.U.getD n none)) = true
  ctx : x' = x
  same : a' = { a with tl := a'.tl, slotA := a.F.next }

/-- Place 5: the draw of the matrix. -/
structure DrawCall : Prop where
  draw : a.tl.drawMatrixF a.F x = .ok ((a'.tl, a'.F), x')
  same : a' = { a with tl := a'.tl, F := a'.F }

/-- Place 6: the sending of the digits. -/
structure DigitsCall : Prop where
  root : rootInH [a.tl.ix.ZZ, a.tl.ix.BZ] a.L a.F x = .ok ((((), a'.L), a'.F), x')
  same : a' = { a with L := a'.L, F := a'.F }

/-- Place 7, the routine, at what it returns. What it returns is written into the record. -/
structure DigitsLookAt (gz : Forest.Heard) : Prop where
  pad : Forest.pad #[a.tl.z1.call, a.tl.z2.call] a.tl.f9.pub a.tl.lidb a.F x =
    .ok ((gz, a'.F), x')
  same : a' = { a with
    F := a'.F
    tl := { a.tl with
      foldDrawn := a.tl.foldDrawn + 1, slotA := a.slotA, slotB := a'.F.next, heard := some gz } }

/-- Place 7, the routine: the lookup on the digits. -/
def DigitsLook : Prop := ∃ gz, DigitsLookAt a x a' x' gz

/-- Place 7, behind the routine: the slots are counted and the plan's number of claims is set. -/
structure DigitsQuiet : Prop where
  slots : (a.F.next == D.hp.used) = true
  setPlan : SubM.setPlanClaims D.hp.nLin a.F x = .ok (((), a'.F), x')
  same : a' = { a with F := a'.F }

/-- Place 8, the routine: the batching draw, at the slot that the record holds. -/
structure BatchCall : Prop where
  batch : t2Batch a.tl.slotB a.L a.F x = .ok ((((), a'.L), a'.F), x')
  same : a' = { a with L := a'.L, F := a'.F }

/-- Place 8, behind the routine, at the states and contexts between its parts. -/
structure BatchQuietAt (G₂ G₃ G₄ : Fork) (y₂ y₃ y₄ : Ctx) : Prop where
  front : RunAll (claimsFront D.P D.g a.own) a.F x G₂ y₂
  rowsBooked : (a.tl.foldDrawn == 1) = true
  callsBooked : (1 + a.tl.groupsRun == 2) = true
  objects : a.tl.objectsF a.own.funs G₂ y₂ = .ok ((a'.tl, G₃), y₃)
  back : RunAll (claimsBack D.hp D.g a.own) G₃ y₃ G₄ y₄
  claimCount : (G₄.nClaim == D.hp.nLin) = true
  held : a'.tl.funsHeld a.own.funs = true
  tests : RunAll (tailTests D.hp a'.tl) G₄ y₄ a'.F x'
  same : a' = { a with F := a'.F, tl := a'.tl }

/-- Place 8, behind the routine: the whole list of claims and the tests on it. -/
def BatchQuiet : Prop := ∃ G₂ G₃ G₄ y₂ y₃ y₄, BatchQuietAt D a x a' x' G₂ G₃ G₄ y₂ y₃ y₄

/-- Place 9, the routine, at the number of equations laid. -/
structure DoorCallAt (laid : Nat) : Prop where
  laidIs : a.tl.equationsLaidF = some laid
  door : doorH laid a.L a.F x = .ok ((((), a'.L), a'.F), x')
  same : a' = { a with L := a'.L, F := a'.F }

/-- Place 9, the routine: the closing of the link. -/
def DoorCall : Prop := ∃ laid, DoorCallAt a x a' x' laid

/-- Place 9, behind the routine: the routine's last counts, the two tests of runLinkH, the row on
the table, and what runLinkH returns: the walk's two values. -/
structure DoorQuiet : Prop where
  draws : (a.F.nClaim == a.F.planClaimsF) = true
  allTaken : (if a.F.kapAllTakenF = true then some () else none) = some ()
  foldTaken : a.tl.foldAllTakenF = true
  closed : (a.L.handed && a.L.done) = true
  plan : samePlan D.X a.F a.L.list = true
  row : D.X.fv = true → ∃ row,
    pendingRowH D.wsLay a.out.indexMasks a.own.wo D.X.NCL D.p.lin x = .ok (row, x') ∧
    a'.out = { a.out with pending := a.out.pending ++ [row] }
  noRow : ¬D.X.fv = true → x' = x ∧ a'.out = a.out
  same : a' = { a with check := a.L.check, out := a'.out }

end Places

/-- The nine routines. Beyond the number 8 the relation holds of all states. -/
def call (D : LayLink) : Nat → LayRel
  | 0 => FirstCall
  | 1 => LookCall D
  | 2 => OwnCall D
  | 3 => ReadsCall D
  | 4 => DrawCall
  | 5 => DigitsCall
  | 6 => DigitsLook
  | 7 => BatchCall
  | 8 => DoorCall
  | _ => fun _ _ _ _ => True

/-- The calls behind the nine routines. Beyond the number 8 the relation holds of all states. -/
def quiet (D : LayLink) : Nat → LayRel
  | 0 => FirstQuiet D
  | 1 => LookQuiet D
  | 2 => LayRel.still
  | 3 => ReadsQuiet D
  | 4 => LayRel.still
  | 5 => LayRel.still
  | 6 => DigitsQuiet D
  | 7 => BatchQuiet D
  | 8 => DoorQuiet D
  | _ => fun _ _ _ _ => True

/-- The nine places: the routine, then the calls behind it. -/
def place (D : LayLink) (i : Nat) : LayRel := LayRel.comp (call D i) (quiet D i)

end KObj.Course
