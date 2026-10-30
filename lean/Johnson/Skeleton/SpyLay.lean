-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Skeleton/SpyLay.lean: the 18 steps of a link of the kind "layers", in the second form of the
Lean verifier program's check of a proof file's first hash chain (Johnson/Skeleton/Steps.lean):
definitions with code; no theorem is about them.

Johnson/Top/H/Course/LayPlaces.lean describes the nine places of such a link by relations on a
record of the link's local values (`LayLoc`). Here routines on that record make the relations' calls
and tests, place by place, in their order: the 18 steps of `stepsG`. A place is one call of a
sub-protocol's routine with the tests and notes around it.

Where the code comes from: the steps were copied by hand from definitions of the Lean verifier
program `verify-on-bytes` (OnBytes/): its routine for a link, `runLinkH`
(OnBytes/Model/StagesLinks.lean); its check of a link of this kind, `Layer.runForkHidG2`
(OnBytes/Model/Layer.lean); and three routines that this check reaches, `Layer.hearLook`,
`HTailF2.transcriptF` and `HTailF2.fixedBeforeTheMatrixF` (the last two: OnBytes/Model/Tail.lean).
`Layer.hearOwn` is called as it is. The steps also call routines of OnBytes/Model/ReqChain.lean,
StagesLinks.lean, Look.lean, Trees.lean, Tail.lean and Hide.lean and of OnBytes/Iop/Ground.lean.
Three steps (`gClaimsFront`, `gClaimsBack`, `gTests`) run lists of routines that LayPlaces.lean
gives; these lists also name a routine of OnBytes/Model/Merge.lean. The program follows the source
text of `cp_verify`, the C++ verifier (lean/README.md).

Limits: definitions only; nothing is evaluated in this file. No theorem in this library says that a
step which returns satisfies its relation, or that the steps in a row are the program's routine for
the link. They differ from it in at least two ways. A test of this file that fails has no name and
no place (`Blk.must`, `Blk.get`); the program gives a name to most of these tests (`mustAs`) and a
place to a failure inside the link's check (`Blk.inPlace`). One read (`iU3`, in `gReads`) comes
after `hearOwn`, where the program makes it before. The steps read neither `X.run` nor `X.kind`:
that the link is of this kind, and that the plan in D (`D.P`, `D.hp`, `D.g`) is the one from which
the record's own check `X.run` was made, is the caller's duty.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Skeleton.Steps
import Johnson.Top.H.Course.LayPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course.SpyK1
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-! ### The steps -/

def gFirst (a : LayLoc) : Blk LayLoc := do
  let check ← a.check.first
  pure { a with check := check }

def gFirstQuiet (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  let im ← if D.l == 0 then indexMasksH D.links D.p a.check else pure a.out.indexMasks
  Blk.must (a.check.plain.size == 0)
  Blk.must (a.check.link == D.l)
  Blk.must (D.l == (if D.P.y.h.p4 then 2 * D.g else D.g))
  Blk.must (D.X.Tp.nt == D.hp.Tp.nt &&
    (D.X.Fp.trees.map fun X => (X.R, X.K)) == D.hp.Fp.trees.map fun X => (X.R, X.K))
  pure { a with
    out := { a.out with indexMasks := im }
    L := { check := a.check, link := D.l, arrayOf := D.X.arrayOf, list := D.X.Tp }
    F := D.X.Fp.fillL.slots D.hp.ns }

def gLook (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  let (fo, F) ← (Forest.pad D.P.y.cl D.P.y.fo.pub D.P.y.h.lidb).run a.F
  pure { a with fo := fo, F := F }

def gLookQuiet (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  Blk.must (a.fo.shape.dT == D.P.y.fo.dT && a.fo.shape.kT == D.P.y.fo.kT &&
    a.fo.shape.NT == D.P.y.fo.NT && a.fo.shape.rK == D.P.y.fo.rK &&
    a.fo.shape.first == D.P.y.fo.first && a.fo.shape.iota == D.P.y.fo.iota &&
    a.fo.shape.callOf == D.P.y.fo.callOf)
  pure a

def gOwn (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  let (own, F) ← (Layer.hearOwn D.P D.hp D.g a.fo).run a.F
  pure { a with own := own, F := F }

def gReads (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  let iU3 ← Blk.get (D.hp.tl.ix.U.getD 2 none)
  let ((_, L), F) ← ((rootInH [iU3]).run a.L).run a.F
  pure { a with L := L, F := F }

def gReadsQuiet (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  let tl ← Blk.get (D.hp.tl.closeFuns a.own.funs)
  Blk.must tl.funClosed
  Blk.must (tl.shp.size == tl.NM)
  let c ← get
  Blk.must (a.L.check.link == a.L.link && decide (a.L.link < a.L.check.links) &&
      tl.gtTree.size == tl.NM && tl.gtTree.all (HTailF2.arrayFixed a.L c.st) &&
    (List.range 4).all fun n => Option.all (HTailF2.arrayFixed a.L c.st) (tl.ix.U.getD n none))
  pure { a with tl := tl, slotA := a.F.next }

def gDraw (a : LayLoc) : Blk LayLoc := do
  let (tl, F) ← a.tl.drawMatrixF.run a.F
  pure { a with tl := tl, F := F }

def gDigits (a : LayLoc) : Blk LayLoc := do
  let ((_, L), F) ← ((rootInH [a.tl.ix.ZZ, a.tl.ix.BZ]).run a.L).run a.F
  pure { a with L := L, F := F }

def gDigitsLook (a : LayLoc) : Blk LayLoc := do
  let (gz, F) ← (Forest.pad #[a.tl.z1.call, a.tl.z2.call] a.tl.f9.pub a.tl.lidb).run a.F
  pure { a with
    F := F
    tl := { a.tl with
      foldDrawn := a.tl.foldDrawn + 1, slotA := a.slotA, slotB := F.next, heard := some gz } }

def gDigitsQuiet (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  Blk.must (a.F.next == D.hp.used)
  let (_, F) ← (SubM.setPlanClaims D.hp.nLin).run a.F
  pure { a with F := F }

def gBatch (a : LayLoc) : Blk LayLoc := do
  let ((_, L), F) ← ((t2Batch a.tl.slotB).run a.L).run a.F
  pure { a with L := L, F := F }

/-- The first of the four steps of place 7 that follow the draw of the batching element (`gBatch`):
the routines of `claimsFront`. The other three are `gObjects`, `gClaimsBack` and `gTests`. -/
def gClaimsFront (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  let (_, F) ← (runAll (claimsFront D.P D.g a.own)).run a.F
  pure { a with F := F }

def gObjects (a : LayLoc) : Blk LayLoc := do
  Blk.must (a.tl.foldDrawn == 1)
  Blk.must (1 + a.tl.groupsRun == 2)
  let (tl, F) ← (a.tl.objectsF a.own.funs).run a.F
  pure { a with F := F, tl := tl }

def gClaimsBack (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  let (_, F) ← (runAll (claimsBack D.hp D.g a.own)).run a.F
  pure { a with F := F }

def gTests (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  Blk.must (a.F.nClaim == D.hp.nLin)
  Blk.must (a.tl.funsHeld a.own.funs)
  let (_, F) ← (runAll (tailTests D.hp a.tl)).run a.F
  pure { a with F := F }

def gDoor (a : LayLoc) : Blk LayLoc := do
  let laid ← Blk.get a.tl.equationsLaidF
  let ((_, L), F) ← ((doorH laid).run a.L).run a.F
  pure { a with L := L, F := F }

def gDoorQuiet (D : LayLink) (a : LayLoc) : Blk LayLoc := do
  Blk.must (a.F.nClaim == a.F.planClaimsF)
  Blk.must a.F.kapAllTakenF
  Blk.must a.tl.foldAllTakenF
  Blk.must (a.L.handed && a.L.done)
  Blk.must (samePlan D.X a.F a.L.list)
  if D.X.fv then
    let row ← pendingRowH D.wsLay a.out.indexMasks a.own.wo D.X.NCL D.p.lin
    pure { a with check := a.L.check, out := { a.out with pending := a.out.pending ++ [row] } }
  else pure { a with check := a.L.check }

/-! ### The list of steps, and the run that records them -/

/-- The 18 steps of a link of the kind "layers", each with the name of the point just after it.
Places are numbered from 0 here. "i.call": after the routine of place i; "i.quiet": after the other
calls and tests of place i. Places 2, 4 and 5 have no step "i.quiet". Place 7 has three more points
between the two: "7.front", "7.objects" and "7.back". -/
def stepsG (D : LayLink) : List (String × (LayLoc → Blk LayLoc)) :=
  [("0.call", gFirst), ("0.quiet", gFirstQuiet D), ("1.call", gLook D), ("1.quiet", gLookQuiet D),
   ("2.call", gOwn D), ("3.call", gReads D), ("3.quiet", gReadsQuiet D), ("4.call", gDraw),
   ("5.call", gDigits), ("6.call", gDigitsLook), ("6.quiet", gDigitsQuiet D), ("7.call", gBatch),
   ("7.front", gClaimsFront D), ("7.objects", gObjects), ("7.back", gClaimsBack D),
   ("7.quiet", gTests D), ("8.call", gDoor), ("8.quiet", gDoorQuiet D)]

/-- Runs the 18 steps from a and records the state before the first step and after each one. If
every step returns, the list has 19 entries. If a step rejects, the run rejects: no list. -/
def spyG (D : LayLink) (a : LayLoc) : Blk (List (Look LayLoc)) := spy (stepsG D) a

end KObj.Course.SpyK1
