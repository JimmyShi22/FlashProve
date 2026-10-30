-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Skeleton/SpyTail.lean: the steps of two parts that lie outside every link, in the second
form of the Lean verifier program's check of a proof file's first hash chain
(Johnson/Skeleton/Steps.lean): definitions with code; no theorem is about them.

The two parts: the call after the last link (`ChainCheck.finish`: m + 3 places for a list of m + 1
stages) and the first part of the test on the table (`memberFirstVerify`: two places). A place is
one call of a sub-protocol's routine with the tests and notes around it. At a stage that is not the
last there are two calls (`foldVerify`, then `csVerify`); at a single row, `mBatt` makes none.
Johnson/Top/H/Course/FinishPlaces.lean and MemberPlaces.lean describe the places by relations on
records of local values (`FinishLoc`, `MemberLoc`). Here each relation has a routine on its record
which makes the relation's calls and tests in their order: the 2 m + 7 steps of `stepsF` and the 5
steps of `stepsM`. The chain's start and the last step of `Proof.firstBlock` (`Proof.firstEnd`) also
lie outside every link; they are not cut into steps.

Where the code comes from: the steps are the definitions, unfolded by hand, of routines of the Lean
verifier program `verify-on-bytes` (OnBytes/): `ChainCheck.finish` (OnBytes/Model/ReqChain.lean),
`ReqFrame.finish` (OnBytes/Iop/Req.lean), `ioppVerify` and `ioppStagesVerify`
(OnBytes/Iop/Prox.lean), and `memberFirstVerify` and `linFirstVerify` (OnBytes/Iop/Lin.lean), with
the tests of `Proof.firstBlock` (OnBytes/Proof/File.lean). They call routines of
OnBytes/Iop/Req.lean, Cs.lean, Prox.lean, Bat.lean, Fold.lean, Batt.lean, Lin.lean, Send.lean and
Ground.lean, and `stageOthers` of OnBytes/Slice/BlkTop.lean. Two steps run lists of notes that
MemberPlaces.lean gives. The program follows the source text of `cp_verify`, the C++ verifier
(lean/README.md).

Limits: definitions only; nothing is evaluated in this file. No theorem in this library says that a
step which returns satisfies its relation, or that the steps in a row are the program's routines.
One field is not filled in: `FinishLoc.D`, the record of the last code switch's run (`LocTaken`), is
no local value of the program, and we know no routine that produces it; the step `fSwitch`, which
makes the switch's call, leaves it as it was. So that step does not satisfy the relation
`FSwitchCall`, whose clause `ran` is about D. One test has another form than in the program: the
step `mFront` rejects at once where the reply differs from the claim (`Blk.must`); the program notes
the failed test in its context and goes on to its end (`Blk.check`, called in
OnBytes/Proof/File.lean). On a view on which no earlier test has failed the condition is the same.
In the dry run, and after an earlier failed test, `Blk.check` does nothing; `Blk.must` rejects there
too. Five tests are not in the program: `fStage`, `fStageQuiet`, `fBase`, `mBattQuiet` and
`mSendQuiet` reject if the list that they read has a form that the order of the steps rules out. One
read has another place: `mSendQuiet` reads the codes after the sending, where the program
(`linFirstVerify`) reads them before it. A test that fails here (`Blk.must`, `Blk.get`) has no name
of its own: the print shows "refused".
Terms: lean/GLOSSARY.md.

-/
import Johnson.Skeleton.Steps
import Johnson.Top.H.Course.FinishPlaces
import Johnson.Top.H.Course.MemberPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course.SpyK1
open OnBytes OnBytes.Model
open OnBytes.Params (IoppStage)
open OnBytes.Slice (stageOthers)

/-- Calls that return nothing, one after the other. -/
def blkRun : List (Blk Unit) → Blk Unit
  | [] => pure ()
  | b :: l => do b; blkRun l

/-! ### The steps of `ChainCheck.finish` -/

def fFront (a : FinishLoc) : Blk FinishLoc := do
  Blk.must (!a.check.inLink && a.check.link == a.check.links)
  Blk.must (a.check.frame.next == ReqNext.first &&
    a.check.frame.link == a.check.frame.shape.link.length)
  let G ← Blk.get a.check.frame.groups[a.check.frame.link]?
  let fr ← a.check.frame.beginLink
  pure { a with G := G, fr := fr }

def fSwitch (a : FinishLoc) : Blk FinishLoc := do
  let sw ← csSigmaVerify a.fr.rows a.G.target a.fr.group a.notice
  pure { a with sw := sw }

def fSwitchQuiet (a : FinishLoc) : Blk FinishLoc := do
  let o ← Blk.get a.sw.others[0]?
  pure { a with mask := some o }

def fBatFront (a : FinishLoc) : Blk FinishLoc := do
  let answers ← Blk.samples
  let S ← Blk.statement
  Blk.must (ioppOk S.codes a.fr.shape.last answers)
  pure { a with answers := answers }

def fBat (a : FinishLoc) : Blk FinishLoc := do
  let (row, L) ← batVerify a.fr.group
  pure { a with row := row, L := L }

def fBatQuiet (a : FinishLoc) : Blk FinishLoc := do
  Blk.note "BAT: target" a.row.target
  match a.fr.shape.last with
  | [] => Blk.must false; pure a
  | cur :: later =>
    let Gp ← Blk.group a.fr.group
    Blk.must (Gp.code == cur.code && Gp.maskCode == cur.maskCode && a.L.k == cur.k &&
      a.L.h == cur.h)
    pure { a with cur := cur, later := later }

def fStage (a : FinishLoc) : Blk FinishLoc := do
  match a.later with
  | [] => Blk.must false; pure a
  | next :: rest =>
    let rows ← foldVerify (ioppFoldShape a.cur a.L) a.row a.mask
    Blk.note "FOLD: target" rows.target
    let gp ← Blk.newGroup next.code next.maskCode
    let (st, row, L) ← csVerify rows
      (switchTargetStage next.code next.maskCode next.k next.h a.answers) gp
      (stageOthers a.ride next rest)
    pure { a with st := st, row := row, L := L }

def fStageQuiet (a : FinishLoc) : Blk FinishLoc := do
  match a.later with
  | [] => Blk.must false; pure a
  | next :: rest =>
    Blk.note "CS: target" a.row.target
    Blk.noteBy "CS: c'[0]" fun _ => a.row.c.entry 0
    Blk.note "CS: d'[0]" (a.row.d.getD 0 zeroE)
    Blk.note "CS: d's last entry" (a.row.d.back?.getD zeroE)
    if a.ride then
      let o ← Blk.get a.st.others[0]?
      pure { a with cur := next, later := rest, mask := some o }
    else pure { a with cur := next, later := rest, mask := none }

def fBase (a : FinishLoc) : Blk FinishLoc := do
  Blk.must a.later.isEmpty
  let R ← Blk.get (ioppLastRows a.cur a.L a.row)
  baseVerify R a.mask 0
  pure a

/-- The 2 m + 7 steps of `ChainCheck.finish` for a list of m + 1 stages, each with the name of the
point just after it. "i.front": before the routine of place number i (places 0 and 1 only);
"i.call": after the routine; "i.quiet": after the rest of the place. The last place, m + 2, has
"call" only. -/
def stepsF (m : Nat) : List (String × (FinishLoc → Blk FinishLoc)) :=
  [("0.front", fFront), ("0.call", fSwitch), ("0.quiet", fSwitchQuiet), ("1.front", fBatFront),
   ("1.call", fBat), ("1.quiet", fBatQuiet)] ++
  ((List.range m).map fun j =>
    [(s!"{j + 2}.call", fStage), (s!"{j + 2}.quiet", fStageQuiet)]).flatten ++
  [(s!"{m + 2}.call", fBase)]

/-- Runs the steps of `ChainCheck.finish`; if every step returns, keeps 2 m + 8 records (`Look`).
m + 1 is the number of stages in the starting record a (`a.check.frame.shape.last`); for no stage, m
is 0. -/
def spyF (a : FinishLoc) : Blk (List (Look FinishLoc)) :=
  spy (stepsF (a.check.frame.shape.last.length - 1)) a

/-! ### The steps of `memberFirstVerify` -/

def mFront (D : MemberLink) (a : MemberLoc) : Blk MemberLoc := do
  Blk.must (a.out.reply == some D.reply)
  Blk.must (a.out.pending.length == D.p.pendingRows)
  let c ← get
  Blk.must (memberRowsFit c.st D.p.lin a.out.indexMasks a.out.pending)
  pure { a with rows := a.out.pending }

def mBatt (D : MemberLink) (a : MemberLoc) : Blk MemberLoc := do
  match a.rows with
  | [_] => pure a
  | rows =>
    let r ← Batt.verify D.p.lin.kCol rows a.out.indexMasks
    pure { a with rows := [r] }

def mBattQuiet (D : MemberLink) (a : MemberLoc) : Blk MemberLoc := do
  match a.rows with
  | [one] =>
    blkRun (match a.out.pending with
      | [_] => []
      | _ => battNotes one)
    Blk.note "member: the claim's target" one.target
    let c ← get
    Blk.must (linOk c.st.codes D.p.lin)
    let msg ← Blk.get (linMessageW D.p.lin)
    pure { a with msg := msg }
  | _ => Blk.must false; pure a

def mSend (a : MemberLoc) : Blk MemberLoc := do
  let ids ← sendVerify a.msg true
  pure { a with ids := ids }

/-- The codes: the relation quantifies them existentially. The program (`linFirstVerify`) reads them
before the sending (`sendVerify`); this step reads them after it. -/
def mSendQuiet (D : MemberLink) (a : MemberLoc) : Blk MemberLoc := do
  match a.rows with
  | [one] =>
    let c ← get
    let lin ← linFirstRows D.p.lin (memberClaim one) a.ids
    blkRun (evalNotes D.p.lin (memberClaim one) c.st.codes lin.w)
    pure { a with lin := lin }
  | _ => Blk.must false; pure a

/-- The five steps of the two places of `memberFirstVerify`; the first step also makes the tests of
`Proof.firstBlock` that come before it. -/
def stepsM (D : MemberLink) : List (String × (MemberLoc → Blk MemberLoc)) :=
  [("0.front", mFront D), ("0.call", mBatt D), ("0.quiet", mBattQuiet D), ("1.call", mSend),
   ("1.quiet", mSendQuiet D)]

/-- Runs these five steps; if every step returns, keeps six records (`Look`). -/
def spyM (D : MemberLink) (a : MemberLoc) : Blk (List (Look MemberLoc)) := spy (stepsM D) a

end KObj.Course.SpyK1
