-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K5.lean: kind K5 (an attention segment's own rounds) as a lot for the
fold over blocks: which blocks the kind brings, and at which places.

`lotN`: at every attention segment the kind's block with its four runs of claims, "first", "keys",
"join", "second", in that order and under these names, typed at VerifiableInference.Desc.Claim
(`k5AtN`, Johnson/Desc/First/Att/SeatN.lean). It is for a driver that lays the order of the runs
uncut, so that every run must be stated by its block. The block comes in the field hearC; the field
own is empty. The kind states no run behind the batching.

The place: chain 1, the link's number, piece 3: the segment's hearing block number 2. The block
takes no token (letters := false).

"before": the commitments that the segment has sent in front of the kind's rounds: those of the
first chain's declared rounds between the segment's steps ".0.call" and ".2.scores". Where one of
these two steps is not found among the cuts, the block's test on the plan is false: without that an
empty list would be laid in silence, and the test that a block's draws stand behind the messages
named in "before" would ask nothing of this block.

This file imports the lots' common record and the kind's text alone: no control, no weakened copy.

Limits. That "before" names every message that the kind's law needs fixed in front of its draws is
not tested here: where both steps are found and no root is sent between them the list is empty and
this file does not refuse. Where `k5AtN` returns nothing (the public record has no plan of the
segment's group) the lot brings no block for that segment, and this file does not refuse either.
The block lays what it heard in the field heard5 alone: the four older fields planes, scores, d and
x stay as they lay, and whoever reads them behind this block finds nothing or blanks. Nothing is
claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.First.Att.SeatN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5
open ProofFile
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First

/-- The roots that the first chain's declared rounds send in front of a named step; none where the
step is not found. -/
def k5Roots? (Z : Pub) (look : String) : Option Nat :=
  (Z.roundsBefore? look).map fun k => (Z.D.1.take k).foldl (fun n r => n + r.entry.roots) 0

/-- The attention segments: number in the chain, name, group. -/
def k5Places (G : Ground) : List (Nat × String × Nat) :=
  (G.built.toList.zipIdx.filter fun x => x.1.kind == 1).map fun x => (x.2, x.1.name, x.1.g)

/-- Fixed before the draw: the commitments that the segment has sent in front of its own rounds;
none where one of the two steps is not found. -/
def k5Before? (Z : Pub) (name : String) : Option (List (Nat × Nat)) := do
  let r0 ← k5Roots? Z (name ++ ".0.call")
  let r1 ← k5Roots? Z (name ++ ".2.scores")
  pure (Att.P.beforeOf r0 r1)

/-- K5's block with its four runs, typed at the fold's type of a claim, at every attention segment
whose group has a plan: a segment without one gets no block, in silence (the head's Limits).
Where "before" cannot be made the block stands with a test on the plan that is false. -/
def k5OwnN (Z : Pub) (G : Ground) : List (Block S Cl) :=
  (k5Places G).filterMap fun x =>
    (Att.P.k5AtN G.W x.1 x.2.2 ((k5Before? Z x.2.1).getD [])).map fun b =>
      { b with planOk := b.planOk && (k5Before? Z x.2.1).isSome }

/-- **K5's lot**: the four runs stated: "first", "keys", "join", "second". -/
def lotN (Z : Pub) : Lot :=
  { name := "K5: the attention segments' own rounds"
    letters := false
    own := fun _ => []
    hearC := k5OwnN Z
    controls := [] }

end H2K5
