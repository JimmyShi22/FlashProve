-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LevelDef.lean: the level at a place of the code switch: where the planner's
own test says that the record's two rounds hold at the target, work counted, each of the block's two
errors, as a share, is at most 2 ^ work / 2 ^ target, at the bits of work that the plan holds for
the two rounds. General in the record; no test is evaluated here.

Johnson/G/SwitchCovers.lean has this at written lists (level_full_vec, level_small_vec). Here the
same general theorems (OnBytes/Tie/Pv/Below.lean: belowG_of_covered, held_of_holds) are called at
one record.
  SwRow.levelOK: the planner's test roundHolds (OnBytes/Params/Planner.lean) at the record's two
      rounds
  bitsAt: the bits of work that the plan holds for the two rounds, as the block's two numbers of
      bits
  Letters.level: Err.BelowG of the caller's two errors at 1 / 2 ^ target, for all letters
  SwRow.works: the target and the two numbers of bits at a record
Limits: those of OnBytes/Tie/Pv/Below.lean and Johnson/G/SwitchCovers.lean: Err.BelowG is a
statement on numbers: that work is worth its bits is not said here; it is a bound on each round, not
on a sum over rounds; the planner's addition for the distance from uniform of its draws is dropped.
That the two counts bound a prover's chance is SendLocRide.hAt, under SendLocRide.OK. Those of
Row.lean. Nothing on soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Member
import OnBytes.Tie.Pv.Below

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Cb Iop IOR
open scoped ENNReal

/-- The planner's test that a round holds at the target, work counted, at the record's two rounds.
-/
def SwRow.levelOK (r : SwRow) : Bool := r.specs.all fun y => roundHolds r.set (capped r.set)
    (y.round r.set .request)

/-- The bits of work that the plan holds for the two rounds. -/
def bitsAt {r : SwRow} {H : r.OK} (X : Letters r H) : GBits (Cb.Pv.SendLocRide.R X.caller).shape :=
  (Cb.Pv.heldWork r.set .request (sendSeed r.set r.o r.roots),
    Cb.Pv.heldWork r.set .request (locRound r.set .request r.g (24 * (r.set.samples * r.o.length)) 0
        (r.set.samples * r.o.length)), ())

/-- **The level at a record**, for all letters. -/
theorem Letters.level {r : SwRow} (h : r.ok = true) (hL : r.levelOK = true) (X : Letters r
    (r.ok_says h)) :
    Err.BelowG (bitsAt X) (Cb.Pv.SendLocRide.eps X.caller) (ENNReal.ofReal ((2 : ℝ) ^
        r.set.target)⁻¹) :=
  Cb.Pv.belowG_of_covered r.set .request _ (by positivity) _ _ _ r.specs (Letters.holds h X).2 rfl
      fun y hy =>
    Cb.Pv.held_of_holds (List.all_eq_true.1 hL y hy)

/-- The target and the two numbers of bits at a record. -/
def SwRow.works (r : SwRow) : ℕ × List ℕ := (r.set.target, r.specs.map (Cb.Pv.heldWork r.set
    .request))

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.Letters.level
