-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/GateRanges.lean: the planner's second gate: what it runs, a twin without the two
planners' runs, and that the twin says no at the written sizes of a key file. One definition, five
theorems, one plant.

Why. `Params.configure` (OnBytes/Params/Configure.lean) refuses where `Plan.missedInTheRanges z.key`
(OnBytes/Plan/RangesGate.lean) says yes. It is the premise f₂ of `configure_of_parts`
(Johnson/AtFull/Made/Ledger.lean). It reads the key file's sizes alone: but it RUNS two routines of
the planner on them: the key file's first plan once more (18,852 rounds) and the lookups' rounds for
their count of scalars. Lean's kernel does not get through the gate as it stands (tried: 259 s; no
verdict).

What is said. `rangesGateBy z lists n`: the gate's text behind the two runs, with the first plan's
lists of positions and the count as letters: a test with code. `finish_of_held`: where `finishHeld`
returns a plan, `finish` returns it. `gate_ranges_by`: where the two runs return, the gate's answer
is the twin's. `lists_key`: the first written plan's lists are 49, 39, 33, 25: by the kernel.
`gate_ranges_twin`: at `writtenSized.key`, these lists and 34,933 scalars the twin says false: by
the kernel. `gate_ranges_of`: so f₂, to the letter, UNDER TWO PREMISES: the ledger's own d₁
(`Plan.oneTimePlan` returns; then it returns the first written plan: `first_written`,
Johnson/Goal/Numbers/KeyFirstListed.lean) and "the lookups' count returns 34,933".
`gate_ranges_plant`: at 40,000 scalars the twin says true (no room among the masks): it can fail.

Limits. The written sizes alone. The second premise is shown by nobody here (by Lean's evaluator at
the written sizes the count is 34,933 and the gate says false: an evaluation). Nothing on soundness.

-/
import Johnson.Goal.Written.Made
import Johnson.Goal.Numbers.KeyFirstListed
import OnBytes.Params.Configure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull)

/-- The second gate behind its two runs. -/
def rangesGateBy (z : Plan.KeySized) (lists : List Nat) (scalars : Nat) : Bool :=
  let x := z.ranges.x
  let parts := (x.lookups.map (·.parts.length)).sum
  let rows := x.message.shape.maskRows
  let inARow := (codeAt z.codes.mask x.message.shape.maskCode).ell
  let room :=
    if rows != 0 && z.set.samples < inARow then rows * (inARow - z.set.samples) + (rows - 1)
    else 0
  lists.length != x.stages.length || missedInTest z.codes x.stages lists 0 0 ||
    scalars < 2 * parts || room < scalars - 2 * parts

/-- Where `finishHeld` returns a plan, `finish` returns it. -/
theorem finish_of_held {s : Setting} {c : Scope} {x : Planning Unit} {P : Planned}
    (h : finishHeld s c x = .ok P) : finish s c x = .ok P := by
  unfold finishHeld at h
  cases hf : finish s c x with
  | error e =>
    rw [hf] at h
    cases h
  | ok p =>
    rw [hf] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
      rfl
    · cases h

/-- **What the second gate runs.** -/
theorem gate_ranges_by (z : Plan.KeySized) (plan : Planned) (n : Nat)
    (h1 : finish z.set .once (Plan.oneTimeRounds z) = .ok plan)
    (h2 : Plan.lookupScalars z = .ok n) :
    Plan.missedInTheRanges z = rangesGateBy z (listsOf plan) n := by
  unfold Plan.missedInTheRanges rangesGateBy
  simp only [h1, h2]

set_option maxRecDepth 1000000 in
/-- The first written plan's lists of positions. -/
theorem lists_key : listsOf keyThree.A.plan = [49, 39, 33, 25] := by decide +kernel

/-- **The twin at the written sizes.** -/
theorem gate_ranges_twin : rangesGateBy writtenSized.key [49, 39, 33, 25] 34933 = false := by
  decide +kernel

/-- **f₂, in the ledger's own letters**, under its d₁ and the lookups' count. -/
theorem gate_ranges_of {oneTime : Planned}
    (d₁ : Plan.oneTimePlan writtenSized.key = .ok oneTime)
    (hs : Plan.lookupScalars writtenSized.key = .ok 34933) :
    Plan.missedInTheRanges writtenSized.key = false := by
  have e : oneTime = keyThree.A.plan := VerifiableInference.Number.ByRuns.first_written d₁
  rw [gate_ranges_by writtenSized.key oneTime 34933 (finish_of_held d₁) hs, e, lists_key]
  exact gate_ranges_twin

theorem gate_ranges_plant : rangesGateBy writtenSized.key [49, 39, 33, 25] 40000 = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.finish_of_held
#print axioms Johnson.AtFull.Made.gate_ranges_by
#print axioms Johnson.AtFull.Made.lists_key
#print axioms Johnson.AtFull.Made.gate_ranges_twin
#print axioms Johnson.AtFull.Made.gate_ranges_of
#print axioms Johnson.AtFull.Made.gate_ranges_plant
