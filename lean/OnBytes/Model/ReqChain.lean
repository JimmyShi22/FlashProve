-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/ReqChain.lean: the order of the calls over the links of a request's own chain, as the
checks of the sub-proofs make them.

On a request's own chain the sub-proofs come as links (OnBytes/Iop/Req.lean), one link for each
sub-proof. This file is the Lean counterpart of the class ChainCheck of
verifier/src/vf_request_chain.h. The order of the calls, and which routine makes which call, are at
ChainCheck. OnBytes/Iop/Ground.lean explains chain, plan, view, statement, oracle message and group.

Main definitions: ChainCheck, ChainCheck.start, ChainCheck.first, ChainCheck.later,
ChainCheck.close, ChainCheck.finish.

Three rules that the types do not enforce are explained at ChainCheck, ChainCheck.start and
ChainCheck.close. No theorem is stated here. What a pass says, and what it does not, is said at
ChainCheck.finish.

vf_request_chain.h has a second form of the same sequence, for sub-proofs handed over as objects
with three routines. Only a test of the C++ programs uses it, and this file does not reproduce it.
-/
import OnBytes.Iop.ReqRows

namespace OnBytes.Model

open Params (ReqShape ReqLayout)

/-- The state between two calls of first, later, close and finish.

A link's oracle messages are sent in one or more batches, called moments. The check of a sub-proof
is one straight routine that is not cut at its moments. So it calls later and close itself, at the
places where they are due (rootInH and doorH, OnBytes/Model/Trees.lean). The routine that walks the
links calls start, first and finish (runLinksH and runLinkH, OnBytes/Model/StagesLinks.lean). Each
of first, later, close and finish tests that it is due and then makes the call of the same name of
ReqFrame, the record of OnBytes/Iop/Req.lean that orders a link's rounds (below: the frame). For
each link the order is:
 - first: the link's first moment;
 - later: once for each further moment, each after the part of the sub-proof that comes before it;
 - close: with the sub-proof's equation, after its last part.

After the last link's close comes finish. A call out of this order fails, provided that the caller
hands each call the state that the call before has returned. The C++ class keeps this state in
private members. Here the state is a plain structure: Lean lets a caller use an earlier state again
or write its fields, and against that ChainCheck and ReqFrame are no guard. -/
structure ChainCheck where
  /-- the state of ReqFrame -/
  frame : ReqFrame
  /-- the layout of every link's arrays, by which a link's equation becomes a row of its group -/
  rows : ReqRows
  /-- the indices in the statement of the oracle messages of the latest moment -/
  sent : Array Nat := #[]
  /-- true between a link's first and its close -/
  inLink : Bool := false
  /-- how many moments of the present link have been received -/
  moments : Nat := 0

namespace ChainCheck

/-- The state before the first link. Fails unless the shape is valid under the statement's codes and
has the plan's number of answers to a sample, and the layout is valid for the shape.

What the caller must ensure. The C++ class takes the request's shape and layout as values that are
part of the input of the chain's first hash call, and the C++ channel ends the program if they are
not. Here they are plain arguments. So the caller must take both from the chain's parameter bytes,
which the strict reader (OnBytes/Chain/Reader.lean) hashes, and from nowhere else. The same holds
for the codes in the statement with which the block starts. The reason: the challenges do not depend
on a public input that is not hashed, so a prover with influence on such an input could fix it once
the challenges are known. This file does not test that duty. -/
def start (shape : ReqShape) (layout : ReqLayout) : Blk ChainCheck := do
  let frame ← ReqFrame.start shape
  let rows ← ReqRows.make shape layout
  pure { frame := frame, rows := rows }

/-- The number of links. -/
def links (c : ChainCheck) : Nat := c.frame.shape.link.length

/-- The present link, counted from 0. -/
def link (c : ChainCheck) : Nat := c.frame.link

/-- The index in the statement of the present link's group of oracle messages. -/
def group (c : ChainCheck) : Nat := c.frame.group

/-- The present link's plain scalars: values that are sent as they are, in a round of their own,
before the link's first message. Only the output head's link has one, the reply's token. -/
def plain (c : ChainCheck) : Array E := c.frame.plain.toArray

/-- The indices in the statement of the oracle messages that were sent with the first link's first
moment and belong to no link. -/
def atStart (c : ChainCheck) : Array Nat := c.frame.atStart

/-- The number of moments that the shape gives link l; 0 for a link that is not there. -/
def momentsOf (c : ChainCheck) (l : Nat) : Nat :=
  ((c.frame.shape.link[l]?).map reqMoments).getD 0

/-- The number of moments that the shape gives the present link; 0 after the last link. -/
def momentsDue (c : ChainCheck) : Nat := c.momentsOf c.link

/-- The moment at which oracle message number message of link l is sent; none for a link or a
message that is not there. -/
def momentOfMessage (c : ChainCheck) (l message : Nat) : Option Nat :=
  ((c.frame.shape.link[l]?).bind fun L => L.messages[message]?).map (·.moment)

/-- The arrays of link l: for each its name and which of the link's oracle messages holds it. The
empty list for a link that is not there. -/
def arraysOf (c : ChainCheck) (l : Nat) : List (String × Nat) :=
  (c.rows.layout.link.getD l []).map fun a => (a.name, a.message)

/-- Begins the next link (ReqFrame.first; OnBytes/Iop/Req.lean lists all that its messages hold).
From the second link on, positions in the code words of the link before are drawn, opened and read
in this call: the closing of that link draws none. -/
def first (c : ChainCheck) : Blk ChainCheck := do
  Blk.must (!c.inLink && decide (c.link < c.links))
  let (f, sent) ← c.frame.first
  pure { c with frame := f, sent := sent, inLink := true, moments := 1 }

/-- The oracle messages of the present link's next moment, with their out-of-domain samples. -/
def later (c : ChainCheck) : Blk ChainCheck := do
  Blk.must (c.inLink && decide (c.moments < c.momentsDue))
  let (f, sent) ← c.frame.later
  pure { c with frame := f, sent := sent, moments := c.moments + 1 }

/-- Ends the present link's sub-proof. Its equation (ReqEquation, OnBytes/Iop/ReqRows.lean) is added
to the link's group as a row, and the frame closes the link.

What the caller must ensure. For the reason given at ChainCheck.start, the target, the coefficients
and the weights of the equation that the caller gives to close must be computed from three things
alone: the input of the chain's first hash call, what was received on this chain, and what was
drawn. This file does not test that duty. -/
def close (c : ChainCheck) (equation : ReqEquation) : Blk ChainCheck := do
  Blk.must (c.inLink && c.moments == c.momentsDue)
  let row ← c.rows.row c.frame equation
  Blk.addRow c.group row
  let f ← c.frame.close
  pure { c with frame := f, inLink := false }

/-- After every link is closed: ReqFrame.finish.

What a pass says, and what it does not. If all calls up to finish succeed on a view, the protocol's
claim is that every link's equation holds for the arrays that were committed, up to the errors that
are computed for the rounds of the chain's plan. No theorem is stated here, so this file does not
prove that claim. A pass says nothing about the oracle messages that were sent with the first link
and belong to no link, which are tested on another chain; nothing about what follows on this chain;
and nothing about the reply: to compare the output head's plain scalar with the reply that a client
was given is left to the caller. -/
def finish (c : ChainCheck) : Blk Unit := do
  Blk.must (!c.inLink && c.link == c.links)
  let _ ← c.frame.finish

end ChainCheck

end OnBytes.Model
