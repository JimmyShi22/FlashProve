-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadDoorRows.lean: two public tests for the verifier's list of public tests
(lawsAsk, Johnson/Desc/Laid/ProofAsks.lean), as functions of the public part Z (ProofFile.Pub: what is
computed from the three public files for the IOP as written in Lean) and of five further arguments
that are computed from Z elsewhere. Definitions with code only. It imports one file that lawsAsk's
own file imports already (Johnson/Desc/ProofFile/Pub.lean) and our light tests.

The list's form. Z is computed once for all new entries. An entry is a pair of a sentence and a
truth value. The sentence says what is wrong where the test rejects.

Main names.
  DoorLetters   the five arguments, as one structure. arr j t: the number of the oracle message at
          tree j, tenant t. num l m: the number of message m of segment l. group k: the sampled
          oracle messages of segment k. sent0: those that the output head's segment sends in its
          first sending. mems: every sampled oracle message's shape and (tree, tenant).
  labsOf X k a  the label of matrix number a of segment k's list.
  nasOf X g     a number of the attention segment of group g.
  planK6Row Z P   Johnson/Desc/Kinds/PlanK6Door.lean's planK6Door at Z's codes, layout and output
          head's sizes; n := P.num 24 0; rb := 0.
  padsRow Z P     Johnson/Desc/Kinds/PadsDoor.lean's padsDoor at Z's codes, layout and lists.
  planK6Words, padsWords   the two entries' sentences.

Not claimed here. No theorem. What acceptance implies: Law/HeadDoorRowsLaw.lean. The full size only:
24 and the 24 pairs are literals. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Pub
import Johnson.Desc.Kinds.PadsDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes OnBytes.Model

/-- The five arguments that are computed from Z elsewhere. -/
structure DoorLetters where
  arr : Nat → Nat → Nat
  num : Nat → Nat → Nat
  group : Nat → List (Nat × Nat)
  sent0 : List (Nat × Nat)
  mems : List (OnBytes.OracleShape × (Nat × Nat))

/-- The label of matrix number a of segment k's list. -/
def labsOf (X : Verify.Public) (k a : Nat) : Nat :=
  ((if 24 < k then ({} : HTailF2)
    else if k = 24 then X.H.tl
    else if k % 2 = 0 then ((X.G[k / 2]?).map fun P => P.tl).getD {}
    else ((X.A[k / 2]?).map fun P => P.seam.tl).getD {}).mats.getD a {}).aId

/-- In the attention segment of group g, the matrix that it reads from the segment before has the
number nasOf X g + 3. -/
def nasOf (X : Verify.Public) (g : Nat) : Nat :=
  (((X.A[g]?).map fun (P : OnBytes.Attention.Plan) => P.S).getD default).cf.NAs

/-- **The first test.** -/
def planK6Row (Z : ProofFile.Pub) (P : DoorLetters) : Bool :=
  planK6Door Z.first.codes Z.first.layout Z.p.X.H.tl.NM Z.p.X.hS.NHf Z.p.X.H.ns (labsOf Z.p.X 24)
    P.num P.arr (P.group 24) P.sent0 P.mems (P.num 24 0) 0

/-- **The second test.** -/
def padsRow (Z : ProofFile.Pub) (P : DoorLetters) : Bool :=
  padsDoor Z.first.codes Z.first.layout (labsOf Z.p.X) P.num P.arr P.group P.mems
    (Layer.matIx Z.p.X.y).iXI (nasOf Z.p.X) Z.p.X.hS.NHf

def planK6Words : String :=
  "a matrix of the output head, or its mask row, does not lie inside one oracle message that \
    the head's segment sends first"

def padsWords : String :=
  "a matrix that a segment reads from an earlier segment lies on a pad of its oracle message, \
    or that oracle message is missing"

end VerifiableInference.Desc.Kinds.Head.Law.OffPad
