-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Fork/Ground.lean: the operations on the state of one sub-proof that had no name
as plain functions on a ledger and a tape. Definitions with code.

What it is for. The check of a sub-proof keeps a record, `Model.Fork` (OnBytes/Model/Hide.lean): its
arrays, what was shown under its slots, the sum of its claims. `verify-on-bytes` changes that record
by 23 plain functions of the namespace `Fork` (Hide.lean:232-407), and calls them from routines that
run in a context (`SubM`, Hide.lean:433-566). OnBytes/K/Kc/Flat.lean has a form without a context:
`Fl α`, a function from the record and the rounds not yet closed (`Tape`) to nothing, or to a value
with both as they are left. Flat.lean and FlatHear.lean give eighteen of SubM's names in that form.
Here are the others that a routine's text calls, each one line over `Fl.change`, `Fl.take` or
`Fl.ask` and `verify-on-bytes`'s own function. So a guard on the record comes with the call: it is
the same text.

Main names:
  `rootTaken`, `hide`, `batchBy`, `kap`, `push`, `lin`, `setPlanClaims`, `claims`, `allTaken`,
    `paid`, `settle`: eleven names of SubM in the form Fl. Each docstring gives SubM's line and the
    plain function's line in Hide.lean, and the guards that come with the call.
  `RowsOwed`, `nothingOwed`, `closeOneRows`, `batchOpen`, `batchRows`: the draw of the element that
    combines rows, for a caller that learns the number of rows only later. The number of rows that
    the plan's entry counts is a debt, carried as a field `Option Nat` of the caller's state:
    `batchOpen` asks that nothing waits and sets it; `batchRows` compares it and clears it; every
    other close, and the chain's last test, ask that nothing waits (`nothingOwed`). In
    `verify-on-bytes` the channel keeps the entry and a mark (OnBytes/Iop/Ground.lean:843-857).
  `Log`, `hideL`, `hideRunL`: a value put under a slot, with a log: one entry (slot, what was shown,
    the factor) for each value, in the order of the puttings.

The log is of puttings, not of takings. A sumcheck's own slots are taken as its rounds run
(`Fl.takeSlots`) and filled only where its claim is made (`Fl.pscRow`). So while a sumcheck is open
the log is shorter than the record's field next, and its slots are not in rising order. The next
free slot stays the field next.

Imported for types and plain functions alone: OnBytes.K.Kc.FlatHear (with Flat.lean beneath it: Fl,
Tape, FlatRound, the three lifters), which imports OnBytes.Model.HeadHeard, and through it Hide.lean
(Fork, Aff, the 23 functions) and the modules of the context. No definition here names a block, a
context, a run or a digest.

Limits: no theorem is stated. That a routine written with these names returns what
`verify-on-bytes`'s routine returns is not said here. `batchOpen` asks less of its round than
`verify-on-bytes`'s trBatchOpen. That one asks, through closeAs (Rounds.lean:93, :96) and Blk.close:
the format's kind of the name; that the entry draws one element, no matrix
entry and no position; that no item of any kind is left in the round; that the round's three numbers
of draws are the entry's. A `FlatRound` shows none of these. They are asked by whoever makes the
tape: `batchEntryB` and `batchRoundB` (Johnson/Desc/First/Door/Door.lean), or a strict maker of the
tape. By runs of that file's writer on two stored proofs a step without them says yes at three
altered inputs at which `verify-on-bytes` says no. That the field which a caller hands to
`batchRows` is the one that `batchOpen` returned, and that every other close asks `nothingOwed`, is
the caller's text: the closes of Flat.lean neither ask the field nor set it: an entry that counts
rows and is closed by one of them leaves nothing owed here, where `verify-on-bytes`'s next close
refuses (Blk.close); a strict maker of the tape, which lets an entry count rows at the
batching round's name alone, cures that. At an entry that counts no row `batchOpen` sets `some 0`,
where `verify-on-bytes` holds such an entry as settled: stricter; the later count refuses there in
both. The routines of Flat.lean that fill slots (`Fl.claimsIn`, `Fl.pscEnds`, `Fl.pscRow`) call
`Fork.hideRun` and keep no log: where they are called the record's marks gotF are the log, and the
refusal of a second value under a slot comes with the call. The matrix of the smallness test is no
field of a `FlatRound`: the step at that round reads its round itself. Nothing on soundness or on
hiding.

-/
import OnBytes.K.Kc.FlatHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkGround

open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff)

/-! ## Eleven names of SubM in the form Fl -/

/-- Notes that the chain has received the commitment of array number t. SubM.rootTaken,
Hide.lean:507; Fork.rootTaken, :235. No guard. -/
def rootTaken (t w : Nat) : Fl Unit := Fl.change fun F => some (F.rootTaken t w)

/-- Puts a hidden value under the free slot j. SubM.hide, Hide.lean:516; Fork.hide, :252. Guards
(:253): j is below ns; there are ns marks; slot j is still free. -/
def hide (j : Nat) (shownScalar factor : E) : Fl Unit := Fl.change (·.hide j shownScalar factor)

/-- Takes the drawn element as theta. SubM.batchBy, Hide.lean:537; Fork.batchBy, :320. Guard (:321):
theta has not been drawn. -/
def batchBy (drawn : E) : Fl Unit := Fl.change (·.batchBy drawn)

/-- Hands out the weight of the next claim. SubM.kap, Hide.lean:540; Fork.kap, :345. Guards: the
door is not shut (:333); once the marks are set up, the claim's number is below the plan's, there
are as many marks as claims in the plan, and this weight has not been handed out (:335-336); theta
has been drawn (:328). -/
def kap : Fl E := Fl.take (·.kap)

/-- Adds w times the form a to the one equation. SubM.push, Hide.lean:543; Fork.push, :307. Guards:
the door is not shut (:308); the arrays have each entry that a names, inside the columns that its
row's weights hold (:293 with :282-288); each slot that a names is below ns (:302). -/
def push (w : E) (a : Aff) : Fl Unit := Fl.change (·.push w a)

/-- Adds the claim that the form f is 0. SubM.lin, Hide.lean:546; Fork.lin, :363. Guards: those of
`kap`, then those of `push`. -/
def lin (f : Aff) : Fl Unit := Fl.change (·.lin f)

/-- Sets the number of claims in the plan. SubM.setPlanClaims, Hide.lean:549. No guard. -/
def setPlanClaims (n : Nat) : Fl Unit := Fl.change fun F => some { F with planClaimsF := n }

/-- The number of claims added so far. SubM.claims, Hide.lean:552. No guard. -/
def claims : Fl Nat := Fl.ask fun F => some F.nClaim

/-- Nothing unless the weight of every claim of the plan has been handed out. SubM.allTaken,
Hide.lean:555; Fork.kapAllTakenF, :341. Guards (:342): there are as many marks as claims in the
plan; every mark is set. -/
def allTaken : Fl Unit := Fl.ask fun F => if F.kapAllTakenF then some () else none

/-- Marks claim number i of the list of owed claims as added. SubM.paid, Hide.lean:561; Fork.paid,
:353. No guard. -/
def paid (i : Nat) : Fl Unit := Fl.change fun F => some (F.paid i)

/-- The one equation on the mask row: the coefficients of the mask entries and the constant. used:
the number of slots that the messages have taken. SubM.settle, Hide.lean:564; Fork.settle, :387.
Guards (:388-389): used is at most ns; the marks, the coefficients, what was shown and the factors
are ns each; every owed claim is marked as added; every slot below used is filled; and (:370-374) a
slot with a coefficient other than 0 is filled. -/
def settle (used : Nat) : Fl (Array E × E) := Fl.ask (·.settle used)

/-! ## The draw that combines rows, the number of rows asked later -/

/-- Closes the round, of which every element must have been taken, and returns the one element that
was drawn with the number of rows that the plan's entry counts. The plan's entry must have the name,
and nz elements drawn other than 0. It is `closeOne` (Flat.lean:114) but for what it returns. -/
def closeOneRows (name : String) (nz : Nat) : Tape → Option ((E × Nat) × Tape)
  | ⟨some nm, z, w, [], [x]⟩ :: t => if nm == name && z == nz then some ((x, w), t) else none
  | _ => none

/-- The channel's debt, as a field of the caller's state: the number of rows that the entry of a
closed round counts, until it has been compared; nothing where no such number waits. -/
abbrev RowsOwed : Type := Option Nat

/-- Nothing unless no number of rows waits. What every other close of a round asks first, and the
last test of a chain. In `verify-on-bytes`: the channel's condition for closing a further round,
and at the end (OnBytes/Iop/Ground.lean: `settled`). -/
def nothingOwed (owed : RowsOwed) : Fl Unit := Fl.must owed.isNone

/-- Draws the element that combines rows into one row, for a caller that learns the number of rows
only later. Asks that nothing waits; returns the element, and the entry's number of rows as what
waits now. SubM.batchOpen, Hide.lean:486; trBatchOpen, Rounds.lean:175-176. -/
def batchOpen (owed : RowsOwed) : Fl (E × RowsOwed) := do
  nothingOwed owed
  let x ← Fl.onTape (closeOneRows Model.RoundName.batSigma.name 0)
  pure (x.1, some x.2)

/-- Nothing unless a number of rows waits and it is the number of rows that were combined. Returns
that nothing waits any more. SubM.batchRows, Hide.lean:490; trBatchRows, Rounds.lean:180;
Blk.requireRows, OnBytes/Iop/Ground.lean:851-857, in a run on a view. -/
def batchRows (owed : RowsOwed) (rows : Nat) : Fl RowsOwed := do
  let held ← Fl.need owed
  Fl.must (held == rows)
  pure none

/-! ## A value under a slot, with the log -/

/-- One entry for each value that was put under a slot, in the order of the puttings: the slot, what
was shown, the factor of the mask entry. -/
abbrev Log : Type := List (Nat × E × E)

/-- `Fork.hide` (Hide.lean:252) with the log: where it does not refuse, one entry is appended. -/
def hideL (F : Fork) (log : Log) (j : Nat) (shownScalar factor : E) : Option (Fork × Log) :=
  (F.hide j shownScalar factor).map fun G => (G, log ++ [(j, shownScalar, factor)])

/-- The entries of a run: the elements of v under the slots first, first + 1 and so on. -/
def runEntries (first : Nat) (v : Array E) (factor : E) : Log :=
  v.toList.zipIdx.map fun y => (first + y.2, y.1, factor)

/-- `Fork.hideRun` (Hide.lean:265) with the log: where it does not refuse, the run's entries are
appended in their order. -/
def hideRunL (F : Fork) (log : Log) (first : Nat) (v : Array E) (factor : E) :
    Option (Fork × Log) :=
  (F.hideRun first v factor).map fun G => (G, log ++ runEntries first v factor)

end Johnson.Desc.First.ForkGround
