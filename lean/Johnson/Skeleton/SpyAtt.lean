-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Skeleton/SpyAtt.lean: the 18 steps of a link of the kind "attention", in the second form of
the Lean verifier program's check of a proof file's first hash chain (Johnson/Skeleton/Steps.lean):
definitions with code; no theorem is about them.

Johnson/Top/H/Course/AttPlaces.lean describes the nine places of such a link by relations on a
record of the link's local values (`AttLoc`). Here routines on that record make the relations' calls
and tests, place by place, in their order: the 18 steps of `stepsA`. A place is one call of a
sub-protocol's routine with the tests and notes around it.

Where the code comes from: the steps were cut by hand out of the definitions of two routines of the
Lean verifier program `verify-on-bytes` (OnBytes/): `runLinkH` (OnBytes/Model/StagesLinks.lean), its
routine for a link, and `Attention.run` (OnBytes/Model/Attention.lean), its check of the attention
sub-proof, with routines that `Attention.run` calls expanded, among them `hear`, `Seam.start`,
`Seam.transcript` and `Seam.finish` of that file and `transcriptF` and `fixedBeforeTheMatrixF` of
OnBytes/Model/Tail.lean. The steps call routines of OnBytes/Model/ReqChain.lean, StagesLinks.lean,
Look.lean, Attention.lean, AttentionScores.lean, AttentionDivide.lean, AttentionTables.lean,
Trees.lean, Tail.lean and Hide.lean and of OnBytes/Iop/Ground.lean. The program follows the source
text of `cp_verify`, the C++ verifier (lean/README.md).

Limits: definitions only; nothing is evaluated in this file. No theorem in this library says that a
step which returns satisfies its relation, or that the steps in a row are the program's routine for
the link. They differ from it at least in this. A test that a step makes itself (`Blk.must`,
`Blk.get`) fails without a name of its own, where the program's, but for `check.link == l`, fails
under a name (`mustAs`, `refuse`); and no failure gets a place here, where the program gives a
failure inside the sub-proof's check the sub-proof's name as its place (`Blk.inPlace`). A link whose
record says that it leaves a row on the weight table (`X.fv`) fails here (`aDoorQuiet`); at a link
of this kind, whose check returns no row, `runLinkH` refuses it too. The steps read neither `X.run`
nor `X.kind`: that the link is of this kind, and that the plan in D (`D.P`) is the one from which
the record's own check `X.run` was made, is the caller's duty.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Skeleton.Steps
import Johnson.Top.H.Course.AttPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course.SpyK1
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-! ### The steps -/

def aFirst (a : AttLoc) : Blk AttLoc := do
  let check ← a.check.first
  pure { a with check := check }

def aFirstQuiet (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let im ← if D.l == 0 then indexMasksH D.links D.p a.check else pure a.out.indexMasks
  Blk.must (a.check.plain.size == 0)
  Blk.must (a.check.link == D.l)
  pure { a with
    out := { a.out with indexMasks := im }
    L := { check := a.check, link := D.l, arrayOf := D.X.arrayOf, list := D.X.Tp }
    F := D.X.Fp.fillL.slots D.P.ns
    tl := { D.P.seam.tl with funClosed := false, foldDrawn := 0 } }

def aLook (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let (g, F) ← (Forest.pad (D.P.S.calls.map (·.call)) D.P.fs.pub D.P.lid).run a.F
  pure { a with g := g, F := F }

/-- Place 2 (places are numbered from 0) is three routines in a row, each of which takes rounds:
`aScores`, `aDivide`, `aAttain`. Each is a step of its own in `stepsA`. -/
def aScores (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let ((planes, scores), F) ← (Attention.scores D.P.S a.g.zk).run a.F
  pure { a with planes := planes, scores := scores, F := F }

def aDivide (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let (d, F) ← (Attention.divide D.P.S a.g.zk).run a.F
  pure { a with d := d, F := F }

def aAttain (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let (x, F) ← (Attention.attain D.P.S).run a.F
  pure { a with x := x, F := F }

def aReads (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let ((_, L), F) ← ((rootInH [D.P.iU3]).run a.L).run a.F
  pure { a with L := L, F := F }

def aReadsQuiet (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  Blk.must a.tl.funOpen
  let t ← Attention.tables D.P.S D.P.mats D.P.nW a.g a.planes a.scores a.d a.x
  let tl ← Blk.get (a.tl.closeFuns t.funs)
  Blk.must tl.funClosed
  Blk.must (tl.shp.size == tl.NM)
  let c ← get
  Blk.must (a.L.check.link == a.L.link && decide (a.L.link < a.L.check.links) &&
      tl.gtTree.size == tl.NM && tl.gtTree.all (HTailF2.arrayFixed a.L c.st) &&
    (List.range 4).all fun n => Option.all (HTailF2.arrayFixed a.L c.st) (tl.ix.U.getD n none))
  pure { a with t := t, tl := tl, slotA := a.F.next }

def aDraw (a : AttLoc) : Blk AttLoc := do
  let (tl, F) ← a.tl.drawMatrixF.run a.F
  pure { a with tl := tl, F := F }

def aDigits (a : AttLoc) : Blk AttLoc := do
  let ((_, L), F) ← ((rootInH [a.tl.ix.ZZ, a.tl.ix.BZ]).run a.L).run a.F
  pure { a with L := L, F := F }

def aDigitsLook (a : AttLoc) : Blk AttLoc := do
  let (gz, F) ← (Forest.pad #[a.tl.z1.call, a.tl.z2.call] a.tl.f9.pub a.tl.lidb).run a.F
  pure { a with
    F := F
    tl := { a.tl with
      foldDrawn := a.tl.foldDrawn + 1, slotA := a.slotA, slotB := F.next, heard := some gz } }

def aDigitsQuiet (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  Blk.must (a.F.next == D.P.nMsg)
  let (_, F) ← (SubM.setPlanClaims D.P.nLin).run a.F
  pure { a with F := F }

def aBatch (a : AttLoc) : Blk AttLoc := do
  let ((_, L), F) ← ((t2Batch a.F.next).run a.L).run a.F
  pure { a with L := L, F := F }

/-- The first of the three steps of place 7 that follow the draw of the batching element (`aBatch`):
`aClaims`, `aObjects`, `aTests`. -/
def aClaims (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let (_, F) ← (Attention.claims D.P (heardAt D.P a)).run a.F
  pure { a with F := F }

def aObjects (a : AttLoc) : Blk AttLoc := do
  let (tl, F) ← (a.tl.objectsF a.t.funs).run a.F
  pure { a with F := F, tl := tl }

def aTests (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let (_, F₃) ← (Attention.noFreeSlot D.P.nMsg).run a.F
  Blk.must (a.tl.funsHeld a.t.funs)
  let (_, F₄) ← (a.tl.selfTestF D.P.seam.nU).run F₃
  let (_, F₅) ← a.tl.coefficientsF.run F₄
  let (_, F) ← a.tl.tileSelfTestF.run F₅
  pure { a with F := F }

def aDoor (a : AttLoc) : Blk AttLoc := do
  let laid ← Blk.get a.tl.equationsLaidF
  let ((_, L), F) ← ((doorH laid).run a.L).run a.F
  pure { a with L := L, F := F }

def aDoorQuiet (D : AttLink) (a : AttLoc) : Blk AttLoc := do
  let (_, F) ← (Attention.countsHeld D.P a.tl).run a.F
  Blk.must (a.L.handed && a.L.done)
  Blk.must (samePlan D.X F a.L.list)
  Blk.must (!D.X.fv)
  pure { a with check := a.L.check, F := F }

/-! ### The steps in a row, with a record after each (`spyA`) -/

/-- The 18 steps of a link of the kind "attention", each with the name of the point just after it.
Places are numbered from 0. "i.call": after the routine of place i; "i.quiet": after the calls and
tests that follow that routine in the place. Place 2's routine is three steps: "2.scores",
"2.divide", "2.call". What follows place 7's routine is three steps: "7.claims", "7.objects",
"7.quiet". Places 1, 2, 4 and 5 have no step "i.quiet". -/
def stepsA (D : AttLink) : List (String × (AttLoc → Blk AttLoc)) :=
  [("0.call", aFirst), ("0.quiet", aFirstQuiet D), ("1.call", aLook D), ("2.scores", aScores D),
   ("2.divide", aDivide D), ("2.call", aAttain D), ("3.call", aReads D),
   ("3.quiet", aReadsQuiet D), ("4.call", aDraw), ("5.call", aDigits), ("6.call", aDigitsLook),
   ("6.quiet", aDigitsQuiet D), ("7.call", aBatch), ("7.claims", aClaims D),
   ("7.objects", aObjects), ("7.quiet", aTests D), ("8.call", aDoor), ("8.quiet", aDoorQuiet D)]

/-- Runs the 18 steps from a. If all of them return: 19 records (`Look`), one before the first step
and one after each step. If a step fails, the run fails and returns no record. -/
def spyA (D : AttLink) (a : AttLoc) : Blk (List (Look AttLoc)) := spy (stepsA D) a

end KObj.Course.SpyK1
