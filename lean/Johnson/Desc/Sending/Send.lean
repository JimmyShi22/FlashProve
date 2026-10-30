-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sending/Send.lean: a sending of oracle messages that closes its own round of answers,
as a step of any chain; and the sending of a link's later moment on a proof file's first chain.

This file holds definitions only; no theorem is stated.

The sending itself is by import: sendP, rowsFor, sampleLoop over the seven ground functions
(Johnson/Desc/Ground/Calls.lean): general in the chain's own named values L and in which messages
are sent. What is added here:
  (1) the three tests that the program's two closing calls make on the plan's two entries. A
      sending takes its two entries as arguments and asks them itself, so that it can stand at any
      place.
  (2) the frame's part of a later moment, after ReqFrame.later and ReqFrame.joinOwn
      (OnBytes/Iop/Req.lean): a plain function on the program's record ReqFrame.

The caller's duty, said here because no type holds it: owed is an argument, and the state (DState)
has no field for the debt. Whoever calls a form of this file reads owed off the carried record at
the run, inside its decision, never once when a table of steps is made: a table that writes none
there makes the test idle at every sending, and no honest run shows it.
"Nothing waits" is owed.all (· == 0): a debt of no rows is no debt, as in the program's
Chan.settled (e.rows == 0 || askedRows) and in S.noneWaits (Johnson/Desc/First/State.lean).
sendOpen, sendStep and laterP return an Option: a refusal here bears no test's name;
Johnson/Desc/K1/Own.lean names each.
GPar.samples is read by none of the seven ground functions (recv takes firstTree alone), as the
program's sending reads no such number either.

Main names:
  owed: the number of rows that the entry of the round closed before counts, until it has been
    compared; none where no such number waits. Behind a sending nothing waits: both its entries
    count no rows.
  planOk2 owed sent es: nothing waits; and on the plan alone: es is two entries, "SEND seed" and
    "SEND answer"; the first draws from the elements other than 0 as many as the largest number of
    answers among the messages, the second none; neither counts batched rows.
  Mid.send m sent f: a step f on the next two rounds, where the two entries pass planOk2 and each
    round draws what its entry says (Mid.step).
  sendStep: the sending as such a step; put lays the numbers, the drawn elements and the answers
    into the chain's own values.
  joinAll, joinOwnP: the messages of one moment become members of the link's group.
  laterP: a later moment: the frame's two tests, the sending, the joining.
  laterStep: the same on Mid, with the frame read off and laid into the chain's own values.
  planOk1, sendOpen: the sending inside a code switch (the program's flag ownRound := false,
    OnBytes/Iop/Cs.lean): it asks the first entry alone, reads the answers as the second round's
    first items, asks nothing of what that round draws, and hands back how many items it took:
    the caller asks "no item left", the second entry and the positions.

Asked at the first close, as the program's first closing call asks it (Chan.settled,
OnBytes/Iop/Ground.lean): that nothing waits. Asked here a step earlier than the program: that the
entry "SEND answer" counts no batched rows: the program sees it at the next closing call.

What is not claimed. That a test written here is the program's. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.Ground.Mid
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Send
open OnBytes OnBytes.Params Desc.Plain

variable {L : Type}

/-- On the plan alone: the two entries of a sending that closes its own round of answers. -/
def planOk2 (owed : Option Nat) (sent : Array OracleNotice) : List Fmt.Entry → Bool
  | [e₁, e₂] =>
    owed.all (· == 0) && e₁.name == "SEND seed" && e₁.drawNZ == answersMax sent && e₁.rows == 0 &&
      e₂.name == "SEND answer" && e₂.drawNZ == 0 && e₂.rows == 0
  | _ => false

/-- A step on the next two rounds, which are a sending's by the plan. -/
def _root_.Desc.Plain.Mid.send (m : Mid L) (owed : Option Nat) (sent : Array OracleNotice)
    (f : DState L → List Fmt.RoundView → Option (DState L)) : Option (Mid L) :=
  if planOk2 owed sent (m.entries.take 2) then m.step 2 f else none

/-- The sending as a step. put: how the chain keeps the messages' numbers, the elements drawn and
the answers received. -/
def sendStep (G : Ground L) (p : GPar) (sent : Array OracleNotice)
    (put : L → Array Nat → List E → List E → L) (d : DState L) : List Fmt.RoundView → Option (DState L)
  | [r₁, r₂] =>
    (sendP G p true d sent r₁ r₂).map fun x => { x.2.2.2.2 with loc := put d.loc x.1 x.2.1 x.2.2.1 }
  | _ => none

/-- On the plan alone: the first entry of a sending whose round of answers the caller closes. -/
def planOk1 (owed : Option Nat) (sent : Array OracleNotice) (e₁ : Fmt.Entry) : Bool :=
  owed.all (· == 0) && e₁.name == "SEND seed" && e₁.drawNZ == answersMax sent && e₁.rows == 0

/-- The sending inside a code switch. Returns the messages' numbers, how many items of the second
round it took, and the state. Of the second round it reads these items alone. -/
def sendOpen (G : Ground L) (p : GPar) (owed : Option Nat) (sent : Array OracleNotice)
    (e₁ : Fmt.Entry) (d : DState L) (r₁ r₂ : Fmt.RoundView) : Option (Array Nat × Nat × DState L) :=
  if planOk1 owed sent e₁ && fits e₁ r₁ then
    (sendP G p false d sent r₁ r₂).map fun x => (x.1, x.2.2.2.1, x.2.2.2.2)
  else none

/-- Message by message: it joins the group g; its main rows are kept if it lives on. -/
def joinAll (G : Ground L) (p : GPar) (g : Nat) : List (ReqMessage × Nat) → DState L →
    Option (DState L)
  | [], d => some d
  | x :: l, d => (G.join p d g x.2 (decide (0 < x.1.life))).bind (joinAll G p g l)

/-- The link's own oracle messages of one moment become members of its group. -/
def joinOwnP (G : Ground L) (p : GPar) (d : DState L) (f : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) : Option (ReqFrame × DState L) :=
  if sent.length == ids.size then
    (joinAll G p f.group (zipT sent ids.toList) d).map fun d' =>
      ({ f with own := f.own ++ ids }, d')
  else none

/-- The oracle messages of the present link's next moment. Returns the frame, their numbers and the
state. -/
def laterP (G : Ground L) (p : GPar) (d : DState L) (f : ReqFrame) :
    List Fmt.RoundView → Option (ReqFrame × Array Nat × DState L)
  | [r₁, r₂] => do
    let Lk ← f.shape.link[f.link]?
    if f.next == .laterOrClose && decide (f.moment < reqMoments Lk) then
      let own := f.atMoment f.moment
      let x ← sendP G p true d (ReqFrame.notices own) r₁ r₂
      let y ← joinOwnP G p x.2.2.2.2 { f with moment := f.moment + 1 } own x.1
      some (y.1, x.1, y.2)
    else none
  | _ => none

/-- A later moment on the next two rounds. get, put: where the chain's own values hold the frame and
the numbers of the messages sent last. -/
def laterStep (G : Ground L) (p : GPar) (owed : Option Nat) (get : L → ReqFrame)
    (put : L → ReqFrame → Array Nat → L) (m : Mid L) : Option (Mid L) :=
  let f := get m.d.loc
  m.send owed (ReqFrame.notices (f.atMoment f.moment)) fun d rs =>
    (laterP G p d f rs).map fun x => { x.2.2 with loc := put d.loc x.1 x.2.1 }

end VerifiableInference.Desc.First.Send
