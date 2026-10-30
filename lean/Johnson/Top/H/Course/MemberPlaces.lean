-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Course/MemberPlaces.lean: the two places of a proof file's first chain that the first
part of the test on the table takes (memberFirstVerify, OnBytes/Iop/Lin.lean), as relations on what
the verifier holds: for each place the success of its routine, and then of the calls behind it that
take no round.

No soundness: a test. This module serves a tool that runs, step by step, the verifier program of
OnBytes/Iop, OnBytes/Model and OnBytes/Proof (written by hand after the C++ source); it states
nothing on soundness.

Definitions alone, in the form of Johnson/Top/H/Course/LayPlaces.lean.
Johnson/Top/H/Course/MemberCourse.lean [not in this library] shows that a run of the verifier's
routine is these relations behind each other.

Which cut. ONE CALL of memberFirstVerify, as Proof.firstBlock (OnBytes/Proof/File.lean) makes it
behind the links, with the tests of that block's text in front of the call. The places are those of
the table planS (Johnson/E/KObj/Plan0S.lean) between the last proximity test and the seal: the
batching of the pending rows, and the sending of W.

Which call of the verifier's text each place takes (place, the table's family, the number of rounds
that the routine takes, the routine, then the calls behind it that take no round). kCol: the number
of column variables of the shape of the test on the table; the table planS, of the full size, has 20
rounds at the first place.
   1  batPsc kCol + 2   Batt.verify, if there are several pending rows; no call and no round if
                  there is one. Behind:
                  the five notes on the batched row (if there are several), the note on the claim's
                  target, and the head of linFirstVerify: a public test and W's message.
                  In front: the reply's comparison and the count of the rows (Proof.firstBlock), the
                  test memberRowsFit.
   2  send 2      sendVerify; linFirstRows (the request's own group and the row on W), two notes.

What the verifier holds. MemberLoc lists the values that the text of Proof.firstBlock,
memberFirstVerify and linFirstVerify holds under local names. TWO OF THEM ARE THE WALK's, check and
out: no relation here writes them. ONE FIELD STANDS FOR TWO LOCAL NAMES OF THE TEXT: rows is the
list "pending" up to the batching and the list of the one row "one" behind it. So a law on the
batching that speaks of one list of rows, before and behind it
(Johnson/Top/H/Stations/BattShortValue.lean [not in this library]), can be stated of this one field.
lin is what the routine returns: the closing of the block reads it behind the last place.

A place is two relations behind each other: callM D i, the success of the routine that takes the
place's rounds, and quietM D i, the successes and tests of the calls behind it that take no round.
Each relation has one equation, same, that names the local values that it writes: it leaves all
others. In front of the first routine stands a stretch without a round, MFront. It leaves the
context of the blocks: it is three tests, and it lays the pending rows into rows.

THE FIRST PLACE STANDS IN TWO CASES, as the text does. With one pending row there is no routine: the
relation leaves all as it is, and a written stretch for this place has no round. Which case holds is
public: MemberLink.batched (MFront.many, MFront.one,
Johnson/Top/H/Course/MemberArrows.lean [not in this library]).

THE COMPARISON WITH THE INSTANCE's REPLY STANDS IN MFront. In the text it is a test under a name: if
it fails the block notes the name and goes on. So its truth follows from a run only where no such
name is noted at the end (first_course, Johnson/Thin/K5/ProofStep.lean [not in this library]).

Main names:
  blkAll: calls that return nothing, behind each other. battNotes, evalNotes: lists of notes, in the
    text's order.
  MemberLoc: the local values. MemberLoc.walk. MemberLink: the public letters. MemberLink.batched.
  MFront; MBattCall, MBattQuiet; MSendCall, MSendQuiet.
  callM D i, quietM D i, placeM D i: the families; place i + 1 has the number i.

BEYOND THE NUMBER 1 callM, quietM AND placeM HOLD OF ALL STATES. They are set to hold there, not to
fail: of a relation that never holds, every law would hold emptily. No statement is meant at these
numbers.

What is not claimed. Nothing is proved here. The codes of the second note behind place 2 are any
(MSendQuiet): nothing ties them to the statement in front of the sending. They enter a note's value
alone, which no test reads. No theorem of this library ties these relations to a run of the
program's routine: they were written by hand off its text, and that they repeat it rests on reading
alone. Nothing here asks that the field failed of the context is none: a named test on values
(Blk.check, Blk.checkOnView) that has failed earlier in the run shows there alone. What the routines
do to the values is not said: a relation is the routines' own equations. The number of the index
masks' message is no public letter here: it is read off the walk's second value.

-/
import Johnson.Top.H.Course.LocRel
import OnBytes.Proof.File
import OnBytes.Model.ReqChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Course
open OnBytes OnBytes.Model

/-! ### lists of calls that take no round -/

/-- Calls that return nothing, behind each other. -/
def blkAll : List (Blk Unit) → Ctx → Ctx → Prop
  | [], x, x' => x' = x
  | b :: l, x, x' => ∃ y, b x = .ok ((), y) ∧ blkAll l y x'

/-- The five notes on the batched row. -/
def battNotes (r : TensorRow) : List (Blk Unit) :=
  [Blk.note "BATT: target" r.target, Blk.note "BATT: gamma_0" (r.psi.headD zeroE),
    Blk.note "BATT: the first weight's scalar" ((r.g.head?.map (·.scalar)).getD zeroE),
    Blk.note "BATT: coefficient of its first mask entry" ((r.masks.head?.map (·.2)).getD zeroE),
    Blk.note "BATT: coefficient of the last mask term" ((r.masks.getLast?.map (·.2)).getD zeroE)]

/-- The two notes behind the row on W. codes: the codes as read in front of the sending. -/
def evalNotes (S : Params.LinShape) (claim : LinClaim) (codes : Codes) (w : Nat) :
    List (Blk Unit) :=
  [Blk.note "LIN: (Eval)'s target" claim.target,
    Blk.noteBy "LIN: (Eval) on W<1>" fun _ =>
      ((linEvalRow S claim w (linLayW codes S)).map
        (·.coefficient w .main ((linLayW codes S).index 1))).getD zeroE]

/-! ### the local values -/

/-- What the verifier's text holds under local names from the end of the links to the seal. The
first two fields are the walk's. -/
structure MemberLoc where
  /-- the walk's: the state of the calls over the links; read by no call here -/
  check : ChainCheck
  /-- the walk's: what the links have returned: the index masks' message, the pending rows, the
  reply -/
  out : Proof.LinksResult
  /-- the pending rows up to the batching; behind it the one row alone -/
  rows : List TensorRow
  /-- what the prover's message with W holds -/
  msg : Array OracleNotice
  /-- the numbers of the oracle messages of that message -/
  ids : Array Nat
  /-- what the first part of the test on the table passes to the second -/
  lin : LinFirst

/-- The walk's two values. -/
def MemberLoc.walk (a : MemberLoc) : ChainCheck × Proof.LinksResult := (a.check, a.out)

/-- The public letters: the arguments of Proof.firstBlock but for the links' block. -/
structure MemberLink where
  /-- the first chain's parameters -/
  p : Params.First
  /-- the instance's reply -/
  reply : E

/-- True if the plan has the batching's rounds: there are several pending rows. It is the planner's
own condition (OnBytes/Plan/PlanListsReq.lean). -/
def MemberLink.batched (D : MemberLink) : Bool := decide (1 < D.p.pendingRows)

/-! ### the two places -/

section Places
variable (D : MemberLink) (a : MemberLoc) (x : Ctx) (a' : MemberLoc) (x' : Ctx)

/-- In front of place 1: the reply that the links have returned is the instance's; the pending rows
are as many as the parameters say; they and the index masks' message fit the shape of the test on
the table. The context of the blocks stays. The pending rows are laid into rows. -/
structure MFront : Prop where
  reply : a.out.reply = some D.reply
  count : a.out.pending.length = D.p.pendingRows
  fit : memberRowsFit x.st D.p.lin a.out.indexMasks a.out.pending = true
  ctx : x' = x
  same : a' = { a with rows := a.out.pending }

/-- Place 1, the routine: several pending rows are batched into one; a single row is taken as it is,
by no call. -/
structure MBattCall : Prop where
  single : ∀ r, a.rows = [r] → x' = x ∧ a'.rows = a.rows
  many : (∀ r, a.rows ≠ [r]) → ∃ r,
    Batt.verify D.p.lin.kCol a.rows a.out.indexMasks x = .ok (r, x') ∧ a'.rows = [r]
  same : a' = { a with rows := a'.rows }

/-- Place 1, behind the routine, at the one row and the context behind the notes on the batching. -/
structure MBattQuietAt (one : TensorRow) (y : Ctx) : Prop where
  isOne : a.rows = [one]
  notes : (∀ r, a.out.pending ≠ [r]) → blkAll (battNotes one) x y
  noNotes : ∀ r, a.out.pending = [r] → y = x
  target : Blk.note "member: the claim's target" one.target y = .ok ((), x')
  lawful : linOk x'.st.codes D.p.lin = true
  message : linMessageW D.p.lin = some a'.msg
  same : a' = { a with msg := a'.msg }

/-- Place 1, behind the routine: the notes, and the head of linFirstVerify. -/
def MBattQuiet : Prop := ∃ one y, MBattQuietAt D a x a' x' one y

/-- Place 2, the routine: the sending of W. -/
structure MSendCall : Prop where
  send : sendVerify a.msg true x = .ok (a'.ids, x')
  same : a' = { a with ids := a'.ids }

/-- Place 2, behind the routine, at the one row, the context behind linFirstRows, and the codes that
the second note reads: in the text those of the statement in front of the sending. -/
structure MSendQuietAt (one : TensorRow) (y : Ctx) (codes : Codes) : Prop where
  isOne : a.rows = [one]
  group : linFirstRows D.p.lin (memberClaim one) a.ids x = .ok (a'.lin, y)
  notes : blkAll (evalNotes D.p.lin (memberClaim one) codes a'.lin.w) y x'
  same : a' = { a with lin := a'.lin }

/-- Place 2, behind the routine: the request's own group and the row on W; two notes. -/
def MSendQuiet : Prop := ∃ one y codes, MSendQuietAt D a x a' x' one y codes

end Places

/-- The two routines. Beyond the number 1 the relation holds of all states. -/
def callM (D : MemberLink) : Nat → LocRel MemberLoc
  | 0 => MBattCall D
  | 1 => MSendCall
  | _ => fun _ _ _ _ => True

/-- The calls behind the two routines. Beyond the number 1 the relation holds of all states. -/
def quietM (D : MemberLink) : Nat → LocRel MemberLoc
  | 0 => MBattQuiet D
  | 1 => MSendQuiet D
  | _ => fun _ _ _ _ => True

/-- A routine, then the calls behind it. -/
def bodyM (D : MemberLink) (i : Nat) : LocRel MemberLoc := LocRel.comp (callM D i) (quietM D i)

/-- The two places. The first has the stretch in front of its routine. -/
def placeM (D : MemberLink) : Nat → LocRel MemberLoc
  | 0 => LocRel.comp (MFront D) (bodyM D 0)
  | i + 1 => bodyM D (i + 1)

end KObj.Course
