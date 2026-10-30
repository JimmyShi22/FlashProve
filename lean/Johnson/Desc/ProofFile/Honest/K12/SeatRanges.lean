-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SeatRanges.lean: the key file's test on the ranges, `rangesTest`
(Johnson/Desc/Key/Ranges.lean), meets `SeatOf` (SaysYesSeat.lean in this folder): it has a proximity
test's place, rounds and oracle messages, and its decision is the test's decision between two
functions. `SeatOf` is one of the five hypotheses of `saysYes_seat` (SaysYesSeat.lean). General in
the type σ of the chain's states, in the type Cl of claims, in the place's numbers N, in the
functions `laid` and `back`, and in the job J, under one hypothesis on J. One theorem, with its
proof.

In the list: a block (`Block σ Cl`, Johnson/Desc/Block.lean) is a sub-protocol at one place
(`Place`) of a description's chain. The test on the ranges is the proximity test on the group of the
lookups' own message, in a key file's first chain. The job J (`TestJob`, Test.lean in this folder)
is what a caller supplies for its test; `J.p` (`P12`, Johnson/Desc/K12/Frame.lean) has the test's
parameters. `rangesParams N` (Ranges.lean) is these parameters at the place `rangesPlace` and the
place's numbers N (`H2U.PlaceNums`, Johnson/Desc/K12/Plan/PlaceOfPlan.lean). The test's own block is
`proximityTestKind guardedProximityTestParts J.p` (`proximityTestKind`: Frame.lean; `guardedProximityTestParts`: Johnson/Desc/K12/JoinGuarded.lean), on states of type
`T12` (Johnson/Desc/K12/Join.lean). `laid` and `back` are the two function parameters of
`rangesTest`. By Ranges.lean, `laid` returns what a chain's state passes to the test (`RangesLaid`),
and `back` writes the test's state back into the chain's state; nothing is asked of either here.
`enterAndAsk laid p` (Ranges.lean) builds the test's state from what `laid` returns and then runs
tests of Ranges.lean on it. All three can refuse: they return in `Except String`.

  `seatOf_ranges`: for every job J with `J.p = rangesParams N`,
    `SeatOf (rangesTest laid back N) J (enterAndAsk laid (rangesParams N)) back` holds. That is: the
    block's place is `J.p.place`; its rounds and its oracle messages are those of the test's own
    block; its decision at a state s is `enterAndAsk laid (rangesParams N) s`, then the decision of
    the test's own block, then `back s`. In `SeatOf` the test's own block is taken at `Unit` as the
    type of claims

By what. `seatOf_inside` (SaysYesSeat.lean) gives `SeatOf` of
`Block.inside enter (proximityTestKind guardedProximityTestParts J.p) leave` (`Block.inside`: Block.lean) at every type of claims;
the hypothesis rewrites `J.p` in that block to `rangesParams N`. `rangesTest` is that `Block.inside`
with the field `name` set to "rng" and one more test on the plan, `asksOnPlan (rangesParams N)`, in
the field `planOk`. `SeatOf` reads neither field, so the four equations carry over by unfolding.

Limits. The conclusion is the four equations of `SeatOf` and no more. The other four hypotheses of
`saysYes_seat` are not shown here. Nothing on whether `enterAndAsk laid (rangesParams N)` or `back`
returns. N is a free parameter: the theorem also holds where `H2U.proximityTestParametersAt`
(Johnson/Desc/K12/AtPlan.lean), by which `rangesParams N` is defined, returns `noP12 rangesPlace`,
parameters without a stage; there the test's own block fails its test on the plan. Nothing on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import Johnson.Desc.Key.Ranges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Key

variable {σ Cl W X : Type}

/-- **The key file's test on the ranges meets `SeatOf`**: for every job J with
`J.p = rangesParams N`, with `enterAndAsk laid (rangesParams N)` as `enter` and `back` as `leave`.
Nothing on whether either of the two returns. -/
theorem seatOf_ranges (laid : σ → Except String RangesLaid) (back : σ → T12 → Except String σ)
    (N : H2U.PlaceNums) (J : TestJob W X) (hJ : J.p = rangesParams N) :
    SeatOf (rangesTest laid back N : Block σ Cl) J (enterAndAsk laid (rangesParams N)) back := by
  have h := seatOf_inside (Cl := Cl) J (enterAndAsk laid (rangesParams N)) back
  have e : (Block.inside (enterAndAsk laid (rangesParams N))
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Cl) back) =
      Block.inside (enterAndAsk laid (rangesParams N))
        (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Cl) back := by rw [hJ]
  rw [e] at h
  exact ⟨h.place, h.rounds, h.oracles, h.decide⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.seatOf_ranges
