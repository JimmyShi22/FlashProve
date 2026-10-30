-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Test/Frame.lean: the frame of a proximity test and the loop over its stages, as plain
functions on data.

Why. The program 'verify-on-bytes' runs a proximity test by `ioppVerify` and `ioppStagesVerify`
(OnBytes/Iop/Prox.lean), which run in a context. A step of the description is a function on data,
with no context across its border. The functions here are these two routines, line for line. What
the routines call that is another routine in a context (the batching of the group's rows, a fold, a
new group, a code switch, the last step) comes in as a record of plain functions on a type σ of
states (`TestParts`), so that each can be written, tried and replaced by itself.

The cut. The text is cut where no round is open, into five pieces; three of them call no part and
read no state: they are functions of a few public values.
  `testFront`: in front of the batching: the stages' sizes fit together.
  `testFirst`: behind the batching: the first stage, and that the group is that stage's.
  `stageCall`: a stage that is not the last: the fold, a new group, the code switch into it.
  `stageNext`: behind such a stage: the next stage, the stages behind it, its mask's number.
  `lastCall`: the last stage: its claim as single rows, and the last step.
`proxStages` and `proxTest` lay them in a row: the whole loop, the whole test.

What is called by name, because it is a plain function already: `ioppOk`, `ioppFoldShape`,
`ioppLastRows`, `baseMaskNotice` (OnBytes/Iop/Prox.lean), `foldMaskNotice` (OnBytes/Iop/Fold.lean),
`switchTargetStage` (OnBytes/Iop/Cs.lean). Kin: the loop's two expressions, typed here in place,
stand under names of their own in two files of laws on the program's runs (`othersOf`, `maskOf`:
Johnson/Thin/K5/IoppCourse.lean; `stageOthers`: OnBytes/Slice/BlkTop.lean); these are not imported,
so that nothing but the program's own files on a test stands beneath this one.

Main definitions: `TestParts`; the five pieces; `proxStages`, `proxTest`.

Where the text parts from the program's. The program keeps intermediate values for a comparison with
another verifier (`Blk.note`, six calls); no test reads them; they are left out. A refusal has no
name here.

Not claimed. No theorem is stated here. That these functions return what the program's routines
return is not stated. What the test decides lies in the parts: of the guards of a whole test the
frame has three and the loop two, all on public values; three more tests (is a stage left) are the
loop's own branch on the list of stages, cut open. Whether a part that marks a failed check and goes
on is a refusal is that part's matter. Whoever lays the pieces in a row otherwise than `proxTest`
does answers for five wires: the codes and the number of answers come of the state in front of the
batching; the group of the state behind it, the layout of what the batching returns; the number of
answers goes to every stage; the present stage and the stages behind it turn in `stageNext` alone;
the claim, its layout and what the switch returned turn in `stageCall` alone. Nothing on rounds that
are left over behind the test: the caller's fold must use them up. Nothing on the dry run. Nothing
on soundness.


-/
import OnBytes.Iop.Prox

set_option autoImplicit false

namespace VerifiableInference.Desc.Test
open OnBytes
open OnBytes.Params (IoppStage IoppChoice)

/-- **What a proximity test calls**, as plain functions on a state. Three readings of the state, and
five steps; a step returns its value and the new state, or nothing where it refuses. -/
structure TestParts (σ : Type) where
  /-- the number of answers to a sample (`Blk.samples`) -/
  samples : σ → Nat
  /-- the statement's codes -/
  codes : σ → Codes
  /-- the group of this number (`Blk.group`); nothing if there is none -/
  group : Nat → σ → Option Group
  /-- all open rows of the group and its members' sample rows into one claim (`batVerify`) -/
  bat : Nat → σ → Option ((GroupRow × GroupLayout) × σ)
  /-- a stage's rows into single rows (`foldVerify`) -/
  fold : FoldShape → GroupRow → Option Nat → σ → Option (SingleRows × σ)
  /-- a new group under these two codes; its number (`Blk.newGroup`) -/
  newGroup : Nat → Nat → σ → Option (Nat × σ)
  /-- single rows into one new oracle message under shorter codes (`csVerify`) -/
  cs : SingleRows → SwitchTarget → Nat → Array OracleNotice → σ →
    Option ((Switched × GroupRow × GroupLayout) × σ)
  /-- the last step (`baseVerify`). Its two checks on values judge the whole test: where one fails
  the part returns nothing, or the state carries the mark and the caller's last test reads it -/
  base : SingleRows → Option Nat → Nat → σ → Option σ

variable {σ : Type}

/-! ## The five pieces -/

/-- **In front of the batching.** The number of answers to a sample, if the stages' sizes fit
together under the codes (`ioppOk`); else nothing. -/
def testFront (codes : Codes) (stages : List IoppStage) (samples : Nat) : Option Nat :=
  if ioppOk codes stages samples then some samples else none

/-- **Behind the batching.** The first stage and the stages behind it. G: the group as the statement
holds it behind the batching, if it is there; L: the layout that the batching has returned. Nothing
unless there is a stage, the group is there, and its two codes and the layout's two numbers of row
variables are the first stage's. -/
def testFirst (stages : List IoppStage) (G : Option Group) (L : GroupLayout) :
    Option (IoppStage × List IoppStage) :=
  match stages with
  | [] => none
  | first :: rest =>
    match G with
    | none => none
    | some G =>
      if G.code == first.code && G.maskCode == first.maskCode && L.k == first.k &&
          L.h == first.h then some (first, rest)
      else none

/-- **A stage that is not the last.** cur: the stage; later: the stages behind it; row, L: the claim
on cur and its layout; foldMask: the number of the oracle that holds the fold's fresh mask, if it
has come. The fold; a new group under the next stage's codes; the code switch into it, which
announces beside: nothing if the masks do not ride; else the last step's masking oracle if the next
stage is the last; else the mask of the next stage's fold. Returns what the switch returns. Nothing
if no stage is behind cur. -/
def stageCall (P : TestParts σ) (answers : Nat) (ride : Bool) (cur : IoppStage)
    (later : List IoppStage) (row : GroupRow) (L : GroupLayout) (foldMask : Option Nat) (s : σ) :
    Option ((Switched × GroupRow × GroupLayout) × σ) :=
  match later with
  | [] => none
  | next :: rest =>
    match P.fold (ioppFoldShape cur L) row foldMask s with
    | none => none
    | some (rows, s1) =>
      match P.newGroup next.code next.maskCode s1 with
      | none => none
      | some (to, s2) =>
        let others : Array OracleNotice :=
          if !ride then #[]
          else if rest.isEmpty then #[baseMaskNotice next.code next.maskCode 1 0]
          else #[foldMaskNotice (ioppFoldShape next {})]
        P.cs rows (switchTargetStage next.code next.maskCode next.k next.h answers) to others s2

/-- **Behind a stage that is not the last.** later: the stages behind the stage that has run; sw:
what its switch has returned. Returns the next stage, the stages behind that, and the number of the
oracle that holds the next stage's mask: the first that the switch has announced beside, if the
masks ride; none if they do not. Nothing if no stage is left, or if the masks ride and the switch
has announced none. -/
def stageNext (ride : Bool) (later : List IoppStage) (sw : Switched) :
    Option (IoppStage × List IoppStage × Option Nat) :=
  match later with
  | [] => none
  | next :: rest =>
    if ride then
      match sw.others[0]? with
      | none => none
      | some o => some (next, rest, some o)
    else some (next, rest, none)

/-- **The last stage.** Its claim as single rows (`ioppLastRows`; nothing unless the layout has one
row variable, no mask row variable and one member), and the last step, under the class of leaves 0.
Nothing if a stage is behind cur. -/
def lastCall (P : TestParts σ) (cur : IoppStage) (later : List IoppStage) (row : GroupRow)
    (L : GroupLayout) (baseMask : Option Nat) (s : σ) : Option σ :=
  if later.isEmpty then
    match ioppLastRows cur L row with
    | none => none
    | some R => P.base R baseMask 0 s
  else none

/-! ## The loop and the whole test -/

/-- **The stages of a proximity test from the stage cur on.** answers: the answers to each sample.
ride: the masks ride. cur: the present stage; then the stages after it; row, L: the claim on cur and
its layout; then the number of the oracle that holds cur's mask, if it has come. Ends with the last
step. (The list on which the loop goes on is written as the pattern's rest, so that Lean sees that
it grows shorter; it is the list that `stageNext` returns.) -/
def proxStages (P : TestParts σ) (answers : Nat) (ride : Bool) :
    IoppStage → List IoppStage → GroupRow → GroupLayout → Option Nat → σ → Option σ
  | cur, [], row, L, baseMask, s => lastCall P cur [] row L baseMask s
  | cur, next :: rest, row, L, foldMask, s =>
    match stageCall P answers ride cur (next :: rest) row L foldMask s with
    | none => none
    | some ((sw, row', L'), s1) =>
      match stageNext ride (next :: rest) sw with
      | none => none
      | some (cur', _, mask) => proxStages P answers ride cur' rest row' L' mask s1

/-- **The proximity test on group g.** firstMask: the number of the oracle that holds the fresh mask
of the first fold, if it came in an earlier message. -/
def proxTest (P : TestParts σ) (g : Nat) (stages : List IoppStage) (choice : IoppChoice)
    (firstMask : Option Nat) (s : σ) : Option σ :=
  match testFront (P.codes s) stages (P.samples s) with
  | none => none
  | some answers =>
    match P.bat g s with
    | none => none
    | some ((row, L), s1) =>
      match testFirst stages (P.group g s1) L with
      | none => none
      | some (first, rest) => proxStages P answers choice.masksRide first rest row L firstMask s1

end VerifiableInference.Desc.Test
