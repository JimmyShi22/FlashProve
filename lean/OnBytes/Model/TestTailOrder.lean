-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestTailOrder.lean: the test of the order before the smallness test's matrix is drawn.

HTailF2.fixedBeforeTheMatrixF (OnBytes/Model/Tail.lean) fails unless every array that the matrix is
applied to is fixed: its oracle message has been received in the present link and is recorded as
sampled. This file makes up the state of a second link of a request's chain, by hand and without a
proof: the link has an array of its own at each of its two moments, and it reads one array of the
first link. On that state the test passes. Each changed copy has a condition false. Then the test
must fail under its name, internal-f-matrix-order; where a guard calls only arrayFixed, the part of
the test that looks at one array, that function must be false. That no other condition is false is
by the choice of the change. One change cannot be made alone on the full state: if the link's number
is changed, arrays are not fixed either. The state named empty repeats that change alone. No chain
runs here, so it is not tested that a running chain keeps its record as the made-up state has it.

The terms are explained in OnBytes/Model/Tail.lean (the docstring of HTailF2 says where), and at the
head of OnBytes/Model/Trees.lean (link, moment, shape, layout); the frame is ReqFrame
(OnBytes/Iop/Req.lean). The file is not imported by the program.
-/
import OnBytes.Model.TestTailRun

namespace OnBytes.Model.TestTailOrder

open OnBytes OnBytes.Model OnBytes.Model.TestTailRun

/-- An oracle message of a link: its moment, and for how many later links it is kept. -/
def message (moment life : Nat) : Params.ReqMessage :=
  { shape := {}, leafClass := 0, moment := moment, life := life }

/-- Two links. The first sends one message, which is kept for one link. The second sends one message
at each of two moments. -/
def shape : Params.ReqShape :=
  { (default : Params.ReqShape) with
    link := [{ plain := 0, messages := [message 0 1] },
             { plain := 0, messages := [message 0 0, message 1 0] }] }

/-- An array in a link's layout. -/
def laid (name : String) (message : Nat) : Params.ReqArray :=
  { name := name, message := message, sizeI := 1, sizeC := 1, blocks := [] }

/-- The first link's array P; the second link's arrays Q, at moment 0, and U, at moment 1. -/
def layout : Params.ReqLayout := { link := [[laid "P" 0], [laid "Q" 0, laid "U" 1]] }

/-- The second link after both of its moments. In the statement its own messages are the oracle
messages 1 and 2, and the first link's message, sent again, is number 0. -/
def link : LinkCtx :=
  { check :=
      { frame :=
          { shape := shape, groups := #[{}, { born := #[(0, 0)] }], next := .laterOrClose,
            link := 1, keptBefore := #[0], own := #[1, 2] },
        rows := { layout := layout } },
    link := 1, arrayOf := #[(1, "U"), (1, "Q"), (0, "P")], moments := 2 }

/-- Three oracle messages, all sampled. -/
def statement : Statement := { oracles := Array.replicate 3 { shape := {}, sampled := true } }

/-- The smallness test's state: U3 is array 0; the matrices' symbol arrays are 1 and 2. -/
def test : HTailF2 :=
  { NM := 2, gtTree := #[1, 2], ix := { U := #[none, none, some 0, none] } }

/-- The name under which the test fails; "" if it passes. -/
def nameOn (tl : HTailF2) (L : LinkCtx) (S : Statement) : String :=
  match ((tl.fixedBeforeTheMatrixF L) {}) { noRounds false with st := S } with
  | .ok _ => ""
  | .error e => e.name

/-- Changes the frame of the calls over the links. -/
def onFrame (f : ReqFrame → ReqFrame) (L : LinkCtx) : LinkCtx :=
  { L with check := { L.check with frame := f L.check.frame } }

#guard nameOn test link statement == ""
#guard [0, 1, 2].all (HTailF2.arrayFixed link statement)
-- The commitment to U3, the link's second moment, has not come.
#guard nameOn test { link with moments := 1 } statement == "internal-f-matrix-order"
#guard !HTailF2.arrayFixed { link with moments := 1 } statement 0 &&
  HTailF2.arrayFixed { link with moments := 1 } statement 1
-- One of the three messages is not recorded as sampled.
#guard [0, 1, 2].all fun o =>
  nameOn test link { statement with
    oracles := statement.oracles.modify o fun x => { x with sampled := false } } ==
  "internal-f-matrix-order"
-- The first link's message is not kept up to the second link.
#guard nameOn test
  (onFrame (fun f => { f with shape := { shape with
    link := [{ plain := 0, messages := [message 0 0] },
             { plain := 0, messages := [message 0 0, message 1 0] }] } }) link) statement ==
  "internal-f-matrix-order"
-- A link that the layout does not have; a name that the layout does not have; an array outside the
-- list.
#guard !HTailF2.arrayFixed { link with arrayOf := #[(2, "U")] } statement 0
#guard !HTailF2.arrayFixed { link with arrayOf := #[(1, "V")] } statement 0
#guard !HTailF2.arrayFixed link statement 3
-- The layout names a message that the shape does not have.
#guard !HTailF2.arrayFixed
  { link with check := { link.check with rows := { layout := { link := [[], [laid "U" 2]] } } } }
  statement 0
-- The frame does not know the message in the present link.
#guard nameOn test (onFrame (fun f => { f with own := #[1] }) link) statement ==
  "internal-f-matrix-order"
#guard nameOn test (onFrame (fun f => { f with keptBefore := #[] }) link) statement ==
  "internal-f-matrix-order"
-- The link's number is not the frame's; the list of symbol arrays is too short.
#guard nameOn test { link with link := 0 } statement == "internal-f-matrix-order"
#guard nameOn { test with NM := 3 } link statement == "internal-f-matrix-order"
/-- A smallness test without a matrix and without a vector: only the conditions on the link's number
are left. -/
def empty : HTailF2 := { NM := 0, gtTree := #[], ix := { U := #[none, none, none, none] } }

#guard nameOn empty link statement == ""
-- The link's number is not the frame's, and nothing else is wrong.
#guard nameOn empty { link with link := 0 } statement == "internal-f-matrix-order"
-- The link's number is the frame's, and the request has no such link.
#guard nameOn empty (onFrame (fun f => { f with link := 5 }) { link with link := 5 }) statement ==
  "internal-f-matrix-order"

/-- The link in a request of three links, whose frame would know a message of the third link as one
that is kept from before. No chain makes such a frame. -/
def withLater : LinkCtx :=
  { onFrame (fun f => { f with
      shape := { shape with link := shape.link ++ [{ plain := 0, messages := [message 0 0] }] },
      groups := #[{}, { born := #[(0, 0), (2, 0)] }], keptBefore := #[0, 1] }) link with
    arrayOf := #[(2, "W")] }

-- An array of a later link is not fixed, though every other condition holds of it.
#guard !HTailF2.arrayFixed
  { withLater with check := { withLater.check with
      rows := { layout := { link := layout.link ++ [[laid "W" 0]] } } } } statement 0
-- Every symbol array and every vector is looked at: here the second symbol array, then U1, is
-- outside the list.
#guard nameOn { test with gtTree := #[1, 3] } link statement == "internal-f-matrix-order"
#guard nameOn { test with ix := { U := #[some 3, none, some 0, none] } } link statement ==
  "internal-f-matrix-order"

end OnBytes.Model.TestTailOrder
