-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Places.lean: the kind K1's blocks at their places on a proof file's first chain, out
of public values alone: the chain's parameters (Params.First: the codes, the shape, the test on the
table), the answers to a sample, the first tree's number, and, for a commitment, the numbers of the
arrays that the sub-proof's plan names.

This file holds definitions only; no theorem is stated.

A block comes into a fold by its place: chain 1, the link, the piece, K1.

Main names:
  noticesAt: the messages that the shape lays at a link's moment.
  ownGroup, inGroup: the groups that the messages tell.
  parLater, laterAt: a segment's moment 1 (the reads) or 2 (the digits): the place's numbers, and
    the block.
  parW, wAt: W's sending, behind the links: the place's numbers, and the block; none where the shape
    has no such message (the program's linMessageW, OnBytes/Iop/Lin.lean, is called for it).

work := 0, as the policy's line has it: a plan with work at "SEND seed" then parts from these
ROUNDS, and the tests on the plan say no.
Par.groups is filled: a sampled message of link l tells the group l; W's sampled messages tell the
request's own group (ownGroup); a message without a sample tells none. The numbers are those of the
statement's groups on this chain, in the order in which the program opens them: one a link
(OnBytes/Iop/Req.lean: beginLink), one a stage of the last proximity test (OnBytes/Iop/Prox.lean),
then the request's own (OnBytes/Iop/Lin.lean: linFirstRows). No theorem says that a message joins
the group that is told of it.

Not here: link 0's first message (Johnson/Desc/K1/First.lean).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- The messages that the shape lays at a link's moment. -/
def noticesAt (q : Params.First) (link moment : Nat) : Array OracleNotice :=
  let f : ReqFrame := { shape := q.shape, groups := reqGroups q.shape, link := link }
  ReqFrame.notices (f.atMoment moment)

/-- The number of the request's own group on the first chain: behind the links' groups, one a link,
and the groups of the last proximity test, one a stage. -/
def ownGroup (q : Params.First) : Nat := q.shape.link.length + q.shape.last.length

/-- Message by message: a sampled one belongs to the group g, one without a sample to none. -/
def inGroup (g : Nat) (ns : Array OracleNotice) : List (List Nat) :=
  ns.toList.map fun n => if n.shape.answers != 0 then [g] else []

/-- The numbers of a segment's later moment. piece: the place's number in its link. -/
def parLater (q : Params.First) (gp : GPar) (link piece moment : Nat) : Par :=
  { place := ⟨1, some link, piece, .K1⟩, codes := q.codes, gp := gp, work := 0,
    parts := [("own", noticesAt q link moment)]
    groups := inGroup link (noticesAt q link moment) }

/-- A segment's later moment. -/
def laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat) (arrays : Option (List Nat)) :
    Block S Cl :=
  commitAtS (parLater q gp link piece moment) link moment arrays

/-- The numbers of W's sending. piece: the place's number behind the links; msg: what goes out. -/
def parW (q : Params.First) (gp : GPar) (piece : Nat) (msg : Array OracleNotice) : Par :=
  { place := ⟨1, none, piece, .K1⟩, codes := q.codes, gp := gp, work := 0,
    parts := [("W and the messages sent with it", msg)], groups := inGroup (ownGroup q) msg }

/-- W's sending. none: the shape has no such message. -/
def wAt (q : Params.First) (gp : GPar) (piece : Nat) : Option (Block S Cl) :=
  (linMessageW q.lin).map fun msg => sendAtS (parW q gp piece msg)

end VerifiableInference.Desc.K1
