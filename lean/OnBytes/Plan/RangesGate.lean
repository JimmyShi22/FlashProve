-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/RangesGate.lean: the conditions on sizes that the C++ programs ask of the key's proof
of the ranges before they admit public files, in addition to the conditions of soundness.

The C++ programs refuse public files under which a committed row would be read at more positions
than it has random entries, or under which more scalars would be masked than there are mask entries.
This file renders the part of that test that is about the proof of the ranges:
 1. the key's first chain draws one list of positions for each stage of the proof's proximity test,
    and each stage's rows and mask rows have at least as many random entries as its list has
    positions;
 2. a mask row of each stage has at least 2 k + 1 - h entries, where the stage has 2^k main rows and
    2^h mask rows (missedInTest, OnBytes/Params/Gate.lean);
 3. the scalars that the lookups' sumchecks send, less two for each part (these are masked by
    entries of the index-mask message), fit the free entries of the mask rows of the proof's own
    oracle message. Each mask row gives up one place for each answer to a sample, and all rows
    except one have one further free entry.

Main definition: missedInTheRanges.
C++ counterpart: hiding_conditions_missed_in_the_ranges() in blocks/frame/hiding_conditions.h.

Not claimed here: that files which pass hide anything. Committer, prover and verifier of the C++
programs all refuse public files that miss one of these conditions (configure() in
blocks/frame/configure.h). This file follows the verifier's steps, a test on numbers, so that it
refuses the same public files.
-/
import OnBytes.Plan.KeyOneTime
import OnBytes.Params.Gate

namespace OnBytes.Plan

open OnBytes.Params

/-- The scalars that the sumchecks of all lookups send. -/
def lookupScalars (z : KeySized) : Except String Nat :=
  scalarsOf z.set (forEach (lookupSizes z.ranges.x z.ranges.matrix) planLookup)

/-- True if a condition on the proof of the ranges is missed, or if the chain's rounds cannot be
planned. -/
def missedInTheRanges (z : KeySized) : Bool :=
  let x := z.ranges.x
  match finish z.set .once (oneTimeRounds z), lookupScalars z with
  | .ok plan, .ok scalars =>
    let lists := listsOf plan
    let parts := (x.lookups.map (·.parts.length)).sum
    let rows := x.message.shape.maskRows
    let inARow := (codeAt z.codes.mask x.message.shape.maskCode).ell
    let room :=
      if rows != 0 && z.set.samples < inARow then rows * (inARow - z.set.samples) + (rows - 1)
      else 0
    lists.length != x.stages.length || missedInTest z.codes x.stages lists 0 0 ||
      scalars < 2 * parts || room < scalars - 2 * parts
  | _, _ => true

end OnBytes.Plan
