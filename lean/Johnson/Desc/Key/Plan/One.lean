-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Plan/One.lean: the test on the plan of a key file's first chain, the one-time
chain: from the lookups' own message to the batching of the pending rows the plan's entries say
what the shapes, the codes, the lookups and the stages ask. Definitions with code; one Bool test;
public data only: no view and no value of the field is read.

What is compared (`Want.meets`, Johnson/Desc/Key/Plan/Test.lean): names, bytes, roots, answers,
elements drawn, how many of them must not be 0, the range of the positions, the rows at every round
that batches. The stretches, in the rounds' order, from round 2 on:
  the two rounds of the lookups' own message;
  each lookup's rounds, after the verifier program's own statement of them (`Lkp.roundsOf`,
    OnBytes/Iop/Lkp.lean);
  the proximity test, from its batching round on;
  the batching of the pending rows: BAT-sigma and a sumcheck, after `Psc.roundsOf`
    (OnBytes/Iop/Psc.lean).

Main names.
  `wantsMessage`, `wantsLookups`, `wantsRanges`, `wantsBatching`, `wantsFirst`: the four
    stretches; all of them in a row.
  `okFirst`: the test: one answer to a sample; the entries from round 2 on meet `wantsFirst`; the
    plan's first round BAT and the first round behind the test (`firstBat`, `behindTest`,
    Johnson/Desc/Key/Where.lean) lie where the stretches' lengths put them.

Limits. Not asked: the chain's first two rounds (the index-mask message), the sending behind the
batching, the seal; an entry's bits of work and its number of positions. A plan with any number of
answers to a sample but one is refused, though the wants are written for any number. No theorem.
Nothing on soundness.

-/
import Johnson.Desc.Key.Where
import Johnson.Desc.Key.Plan.Test

set_option autoImplicit false

namespace VerifiableInference.Desc.Key.Plan

open OnBytes OnBytes.Params

/-- What a plan's entry must say at a round that the program states by `Lkp.roundsOf` or
`Psc.roundsOf`: the stated entry's name, bytes, roots, answers, elements drawn and how many of them
must not be 0. The rest is wanted as at a round that draws no position and no matrix entry and
batches no row. All entries of these two lists are such (`rDraw`, `rOne`, `rValues`,
OnBytes/Iop/Psc.lean); nothing here asks it. -/
def wantOf (e : Fmt.Entry) : Want :=
  { name := e.name, msg := e.msg, roots := e.roots, answers := e.answers, drawE := e.drawE,
    drawNZ := e.drawNZ }

/-- The answers to each sample, by the one-time chain's plan. -/
def samplesOf (one : OneTime) : Nat := one.given.plan.samples

/-- The two rounds of the lookups' own message. -/
def wantsMessage (one : OneTime) : List Want :=
  let m := Wf.messageOf one.ranges
  [wantSeed (samplesOf one) (treesSent one.codes m)
     (largestCube one.codes (m.toList.map (·.shape))),
   wantAnswer (samplesOf one) (m.toList.filter fun n => n.shape.answers != 0).length]

/-- All lookups' rounds, one lookup behind the other. -/
def wantsLookups (one : OneTime) : List Want :=
  (lookupsAt one).flatMap fun x => (Lkp.roundsOf 0 x.1).map fun r => wantOf r.entry

/-- The proximity test, from its batching round on. -/
def wantsRanges (one : OneTime) : List Want :=
  wantsTest one.codes (samplesOf one) one.ranges.stages
    (Wf.rowsBatched one.ranges (Wf.matrixOf one.lin))
    (if one.ranges.choice.masksRide then 0 else 1) one.ranges.choice.masksRide

/-- The number of pending rows: one for each part of each lookup. -/
def pendingRows (one : OneTime) : Nat := ((one.ranges.lookups.map (·.parts.length)).sum)

/-- The batching of the pending rows; no round if there is at most one row. -/
def wantsBatching (one : OneTime) : List Want :=
  if pendingRows one ≤ 1 then []
  else
    { name := "BAT-sigma", drawE := 1, rows := fun _ => pendingRows one } ::
      (Psc.roundsOf 0
        { degree := List.replicate one.lin.kCol 3, withY := false, degreeY := 0, values := 0 }).map
        fun r => wantOf r.entry

/-- All wants from round 2 on, in the rounds' order. -/
def wantsFirst (one : OneTime) : List Want :=
  wantsMessage one ++ wantsLookups one ++ wantsRanges one ++ wantsBatching one

/-- **The plan's side of the first chain, from the lookups' own message to the batching.** One
answer to a sample; the entries from round 2 on meet `wantsFirst`; the first round BAT and the first
round behind the test lie where the stretches' lengths put them. -/
def okFirst (one : OneTime) : Bool :=
  samplesOf one == 1 && okFrom (wantsFirst one) one.given.rounds 2 &&
  firstBat one == some (2 + (wantsMessage one).length + (wantsLookups one).length) &&
  behindTest one ==
    some (2 + (wantsMessage one).length + (wantsLookups one).length + (wantsRanges one).length)

end VerifiableInference.Desc.Key.Plan
