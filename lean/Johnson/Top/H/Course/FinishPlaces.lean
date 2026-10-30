-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Course/FinishPlaces.lean: the places of the call behind the last link of a proof
file's first chain (ChainCheck.finish) as relations on what the verifier holds: for each place the
success of its routine, and of the calls around it that take no round.

No soundness: a test. This module serves a tool that runs, step by step, the verifier program of
OnBytes/Iop, OnBytes/Model and OnBytes/Proof (written by hand after the C++ source); it states
nothing on soundness.

Definitions alone, in the form of Johnson/Top/H/Course/HeadPlaces.lean.
Johnson/Top/H/Course/FinishCourse.lean [not in this library] shows that a run of the call is these
relations behind each other.

Which cut. ChainCheck.finish (OnBytes/Model/ReqChain.lean) is a test and ReqFrame.finish
(OnBytes/Iop/Req.lean): the last code switch, and the last proximity test (ioppVerify,
OnBytes/Iop/Prox.lean). The table planS (Johnson/E/KObj/Plan0S.lean) has two entries for them
(sendLoc, test). Here the test is cut as its typed list of blocks is: the batching draw, one place
for each stage that is not the last, the last step. So the number of places hangs on the list of
stages: A LIST OF m + 1 STAGES GIVES m + 3 PLACES, with the numbers 0 to m + 2.

Which call of the verifier's text each place takes (number; in front; the routine; behind):
  0          in front: the tests of ChainCheck.finish and ReqFrame.finish, the last group,
             ReqFrame.beginLink. The routine: csSigmaVerify. Behind: the mask's number is read.
  1          in front: Blk.samples, Blk.statement, the test ioppOk. The routine: batVerify. Behind:
             a note, the list's first stage, Blk.group, the test on the group's codes and sizes.
  2 .. m + 1 the routine: foldVerify, a note, Blk.newGroup, csVerify. Behind: four notes, the
             mask's number is read, the stage is left.
  m + 2      the routine: the single rows are made (ioppLastRows), baseVerify. Nothing behind.

What the verifier holds. FinishLoc lists the values that the text of ReqFrame.finish, ioppVerify and
ioppStagesVerify holds under local names. TWO OF THEM ARE THE WALK's, check and out: the call reads
the first and returns nothing, so both stay. The frame that ReqFrame.finish returns is dropped by
ChainCheck.finish and is no field. Five fields are the arguments with which ioppStagesVerify calls
itself: cur, later, row, L, mask. ONE FIELD IS NO LOCAL OF THE TEXT: D, the record of the code
switch's run (LocRan, OnBytes/Tie/Pv/Switch/LocRan.lean). The routine writes it here so that a law
at the switch can speak of it behind the place.

THE CALL HAS NO PUBLIC ARGUMENT. The stages, the choice on the masks, the rows and the switch's
target are read off check.frame; the group's number is what ReqFrame.beginLink returns. So the
relations have one letter, the number m, and it decides only which relation stands at which number.

A place is a routine and then the calls behind it (callF, quietF). At the numbers 0 and 1 a stretch
without a round stands in front (FFront, FBatFront). The first turns the context of the blocks: it
opens a group. Each relation has one equation, same, that names the local values that it writes.
THREE THINGS DIFFER FROM THE HEAD's LINK.
  The stretch in front of the batching draw could stand behind the switch. It stands in front of the
  draw, so that the place is the calls of ioppVerify up to its stages.
  Inside the routine of a stage a call without a round opens the next group, between the fold and
  the switch: a stage is one place.
  The successes are said with Blk.Yields, as in OnBytes/Slice/BlkTop.lean.

Main names:
  FinishLoc, FinishLoc.walk, FinishLoc.ride, FinishLoc.notice.
  FFront; FSwitchCall, FSwitchQuiet; FBatFront, FBatCall, FBatQuiet; FStageCall, FStageQuiet;
    FBaseCall.
  callF m i, quietF m i, bodyF m i, placeF m i: the families.

BEYOND THE NUMBER m + 2 callF, quietF AND placeF HOLD OF ALL STATES. They are set to hold there, not
to fail: of a relation that never holds, every law would hold emptily. No statement is meant there.

What is not claimed. Nothing is proved here. A routine succeeds here also where a named test on
values (Blk.check, Blk.checkOnView) has failed inside it: such a failure shows only in the field
failed of the context behind the place. The last step's two tests are of that kind (baseVerify,
OnBytes/Iop/Prox.lean). No theorem of this library ties these relations to a run of the program's
routine: they were written by hand off its text, and that they repeat it rests on reading alone. The
clause ran of place 0 asks more than the routine's success: csSigmaVerify_ran
(OnBytes/Tie/Pv/Switch/LocRan.lean) gives it for a run on a view; for a dry run nothing gives it.
What the routines do to the values is not said: a relation is the routines' own equations. Nothing
says that the list of stages has m + 1 entries.

-/
import Johnson.Top.H.Course.LocRel
import OnBytes.Model.StagesLinks
import OnBytes.Slice.BlkTop
import OnBytes.Tie.Pv.Switch.LocRan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course
open OnBytes OnBytes.Model
open OnBytes.Params (IoppStage)
open OnBytes.Slice (stageOthers)
open OnBytes.Tie.Pv.Switch (LocTaken LocRan)

/-! ### the local values -/

/-- What the verifier's text holds under local names between two places of ChainCheck.finish. The
first two fields are the walk's: the call leaves them. -/
structure FinishLoc where
  /-- the walk's: the state of the calls over the links -/
  check : ChainCheck
  /-- the walk's: what the links have returned -/
  out : Proof.LinksResult
  /-- the last group of the request's shape -/
  G : ReqGroup
  /-- the frame behind the opening of the last group -/
  fr : ReqFrame
  /-- what the last code switch has returned -/
  sw : Switched
  /-- no local of the text: the record of that switch's run -/
  D : LocTaken
  /-- the answers to each sample -/
  answers : Nat
  /-- the present stage -/
  cur : IoppStage
  /-- the stages behind it -/
  later : List IoppStage
  /-- the claim on the present stage's group -/
  row : GroupRow
  /-- that group's layout -/
  L : GroupLayout
  /-- the number of the oracle message that holds the present stage's mask, if it has come -/
  mask : Option Nat
  /-- what the present stage's code switch has returned -/
  st : Switched

/-- The walk's two values. -/
def FinishLoc.walk (a : FinishLoc) : ChainCheck × Proof.LinksResult := (a.check, a.out)

/-- Whether the masks ride, as the test's routine reads it. -/
def FinishLoc.ride (a : FinishLoc) : Bool := a.fr.shape.choice.masksRide

/-- What the last code switch announces beside: the mask of the test's first fold. -/
def FinishLoc.notice (a : FinishLoc) : Array OracleNotice :=
  #[foldMaskNotice (a.fr.foldShape a.fr.link {})]

/-! ### the places -/

section Places
variable (a : FinishLoc) (x : Ctx) (a' : FinishLoc) (x' : Ctx)

/-- In front of place 0: the tests of ChainCheck.finish and ReqFrame.finish, the last group, and the
opening of its group in the statement, which turns the context and takes no round. -/
structure FFront : Prop where
  closed : (!a.check.inLink && a.check.link == a.check.links) = true
  due : (a.check.frame.next == ReqNext.first &&
    a.check.frame.link == a.check.frame.shape.link.length) = true
  group : a.check.frame.groups[a.check.frame.link]? = some a'.G
  begin : a.check.frame.beginLink.Yields x a'.fr x'
  same : a' = { a with G := a'.G, fr := a'.fr }

/-- Place 0, the routine: the last code switch. Its run's record is noted. -/
structure FSwitchCall : Prop where
  switch : (csSigmaVerify a.fr.rows a.G.target a.fr.group a.notice).Yields x a'.sw x'
  ran : LocRan a.fr.rows a.G.target a.fr.group a.notice a'.sw x x' a'.D
  same : a' = { a with sw := a'.sw, D := a'.D }

/-- Place 0, behind the routine, at the mask's number. -/
structure FSwitchQuietAt (o : Nat) : Prop where
  got : (Blk.get a.sw.others[0]?).Yields x o x'
  same : a' = { a with mask := some o }

/-- Place 0, behind the routine: the number of the oracle message that holds the first fold's mask
is read. -/
def FSwitchQuiet : Prop := ∃ o, FSwitchQuietAt a x a' x' o

/-- In front of place 1, at the context between its calls and the statement read. -/
structure FBatFrontAt (y : Ctx) (S : Statement) : Prop where
  samples : Blk.samples.Yields x a'.answers y
  statement : Blk.statement.Yields y S x'
  ok : ioppOk S.codes a.fr.shape.last a'.answers = true
  same : a' = { a with answers := a'.answers }

/-- In front of place 1: the number of answers is read, and the public test on the stages. -/
def FBatFront : Prop := ∃ y S, FBatFrontAt a x a' x' y S

/-- Place 1, the routine: the batching draw. -/
structure FBatCall : Prop where
  bat : (batVerify a.fr.group).Yields x (a'.row, a'.L) x'
  same : a' = { a with row := a'.row, L := a'.L }

/-- Place 1, behind the routine, at the context behind the note and the group read. -/
structure FBatQuietAt (y : Ctx) (Gp : Group) : Prop where
  note : (Blk.note "BAT: target" a.row.target).Yields x () y
  stages : a.fr.shape.last = a'.cur :: a'.later
  group : (Blk.group a.fr.group).Yields y Gp x'
  fits : (Gp.code == a'.cur.code && Gp.maskCode == a'.cur.maskCode && a.L.k == a'.cur.k &&
    a.L.h == a'.cur.h) = true
  same : a' = { a with cur := a'.cur, later := a'.later }

/-- Place 1, behind the routine: a note, the first stage, the test that the group is that stage's.
-/
def FBatQuiet : Prop := ∃ y Gp, FBatQuietAt a x a' x' y Gp

/-- A stage that is not the last, the routine, at the next stage, the stages behind it, the folded
rows, the new group's number and the contexts between the calls. -/
structure FStageCallAt (next : IoppStage) (rest : List IoppStage) (rows : SingleRows) (gp : Nat)
    (y₁ y₂ y₃ : Ctx) : Prop where
  more : a.later = next :: rest
  fold : (foldVerify (ioppFoldShape a.cur a.L) a.row a.mask).Yields x rows y₁
  note : (Blk.note "FOLD: target" rows.target).Yields y₁ () y₂
  opened : (Blk.newGroup next.code next.maskCode).Yields y₂ gp y₃
  switch : (csVerify rows (switchTargetStage next.code next.maskCode next.k next.h a.answers) gp
    (stageOthers a.ride next rest)).Yields y₃ (a'.st, a'.row, a'.L) x'
  same : a' = { a with st := a'.st, row := a'.row, L := a'.L }

/-- A stage that is not the last, the routine: the fold, the next group is opened, the code switch
into it. -/
def FStageCall : Prop :=
  ∃ next rest rows gp y₁ y₂ y₃, FStageCallAt a x a' x' next rest rows gp y₁ y₂ y₃

/-- A stage that is not the last, behind the routine, at the next stage, the stages behind it and
the contexts between the notes. -/
structure FStageQuietAt (next : IoppStage) (rest : List IoppStage) (y₁ y₂ y₃ : Ctx) : Prop where
  more : a.later = next :: rest
  note₁ : (Blk.note "CS: target" a.row.target).Yields x () y₁
  note₂ : (Blk.noteBy "CS: c'[0]" fun _ => a.row.c.entry 0).Yields y₁ () y₂
  note₃ : (Blk.note "CS: d'[0]" (a.row.d.getD 0 zeroE)).Yields y₂ () y₃
  note₄ : (Blk.note "CS: d's last entry" (a.row.d.back?.getD zeroE)).Yields y₃ () x'
  pick : (a.ride = true ∧ a.st.others[0]? = a'.mask ∧ a'.mask.isSome = true) ∨
    (a.ride = false ∧ a'.mask = none)
  same : a' = { a with cur := next, later := rest, mask := a'.mask }

/-- A stage that is not the last, behind the routine: four notes, the next mask's number is read,
and the routine calls itself at the next stage. -/
def FStageQuiet : Prop := ∃ next rest y₁ y₂ y₃, FStageQuietAt a x a' x' next rest y₁ y₂ y₃

/-- The last stage, at the single rows. -/
structure FBaseCallAt (R : SingleRows) : Prop where
  last : a.later = []
  rows : ioppLastRows a.cur a.L a.row = some R
  base : (baseVerify R a.mask 0).Yields x () x'
  same : a' = a

/-- The last stage: its claim as single rows, and the last step. -/
def FBaseCall : Prop := ∃ R, FBaseCallAt a x a' x' R

end Places

/-- The routines, at a list of m + 1 stages. Beyond the number m + 2 the relation holds of all
states. -/
def callF (m : ℕ) : ℕ → LocRel FinishLoc
  | 0 => FSwitchCall
  | 1 => FBatCall
  | i + 2 => if i < m then FStageCall else if i = m then FBaseCall else fun _ _ _ _ => True

/-- The calls behind the routines. Beyond the number m + 2 the relation holds of all states. -/
def quietF (m : ℕ) : ℕ → LocRel FinishLoc
  | 0 => FSwitchQuiet
  | 1 => FBatQuiet
  | i + 2 => if i < m then FStageQuiet else if i = m then LocRel.still else fun _ _ _ _ => True

/-- A routine, then the calls behind it. -/
def bodyF (m i : ℕ) : LocRel FinishLoc := LocRel.comp (callF m i) (quietF m i)

/-- The places. The first two have a stretch in front of their routines. -/
def placeF (m : ℕ) : ℕ → LocRel FinishLoc
  | 0 => LocRel.comp FFront (bodyF m 0)
  | 1 => LocRel.comp FBatFront (bodyF m 1)
  | i + 2 => bodyF m (i + 2)

end KObj.Course
