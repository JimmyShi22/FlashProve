-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/GateChecks.lean: the planner's fourth gate says no at the written sizes and the
written list of a request's range checks. Three definitions, three theorems, one plant.

Why. `Params.configure` (OnBytes/Params/Configure.lean) refuses where `missedInTheChecks`
(OnBytes/Params/Gate.lean) says yes. It is the premise f₄ of `configure_of_parts`
(Johnson/AtFull/Made/Ledger.lean). OF THE RUN's SHAPES x IT READS `x.rangeChecks`, and of that list
only each check's number of bits (`rangeCheckBits`) and how many checks there are.

What is said. `checksPair`, `checksHead`, `checksFull`: the written list: fourteen checks for each
of the twelve pairs of a layers' and an attention segment, eight for the output head's: 176.
`gate_checks`: at `recordLines`, `checksFull` and the three numbers of `writtenSized` the gate says
false: by an evaluation in Lean's kernel. `gate_checks_reads`: two lists with the same bits get the
same answer. `gate_checks_of`: so f₄, to the letter, at every x whose checks have the written list's
bits. `gate_checks_plant`: with one more check in front, whose range is 2 ^ 13 (digits 7 and 7), the
gate says true: the test can fail (177 checks have the same rounded-up logarithm as 176: it is that
check's bits that turn the answer).

Limits. The written values alone. WHENCE THE LIST: copied off a run of the library's own
`shapesOf` at a stored full-size set's public files (an evaluation; no theorem): that a run's
shapes have these checks is a premise. Nothing on soundness.
-/
import Johnson.Goal.Written.Made
import OnBytes.Params.Configure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull)

/-- The checks of one layers' segment and the attention segment behind it. -/
def checksPair : List RangeCheck :=
  [⟨65536, 5990, 128, 129, 131072, (10, 8)⟩, ⟨65536, 5990, 128, 129, 131072, (10, 8)⟩,
   ⟨65536, 5990, 128, 129, 131072, (10, 8)⟩, ⟨32768, 3200, 128, 129, 131072, (10, 8)⟩,
   ⟨8192, 324, 128, 129, 131072, (10, 8)⟩, ⟨65536, 256, 128, 129, 131072, (10, 8)⟩,
   ⟨65536, 1536, 128, 129, 131072, (10, 8)⟩, ⟨65536, 400, 128, 129, 131072, (10, 8)⟩,
   ⟨65536, 400, 128, 129, 131072, (10, 8)⟩, ⟨65536, 7200, 128, 129, 131072, (10, 8)⟩,
   ⟨8192, 360, 128, 129, 131072, (10, 8)⟩, ⟨65536, 640, 128, 129, 131072, (10, 8)⟩,
   ⟨16384, 512, 128, 129, 131072, (10, 8)⟩, ⟨65536, 1536, 128, 129, 131072, (10, 8)⟩]

/-- The checks of the output head's segment. -/
def checksHead : List RangeCheck :=
  [⟨65536, 4816, 128, 129, 131072, (10, 8)⟩, ⟨65536, 4816, 128, 129, 131072, (10, 8)⟩,
   ⟨65536, 4816, 128, 129, 131072, (10, 8)⟩, ⟨65536, 4816, 128, 129, 131072, (10, 8)⟩,
   ⟨16384, 640, 128, 129, 131072, (10, 8)⟩, ⟨8192, 15, 128, 129, 131072, (10, 8)⟩,
   ⟨32768, 384, 128, 129, 131072, (10, 8)⟩, ⟨65536, 400, 128, 129, 131072, (10, 8)⟩]

/-- **The written list of a request's range checks.** -/
def checksFull : List RangeCheck :=
  (List.replicate 12 checksPair).flatten ++ checksHead

/-- **f₄ at the written values.** -/
theorem gate_checks : missedInTheChecks recordLines checksFull
    writtenSized.key.once.shape.fold.columns writtenSized.link.shape.columnsFirst
    writtenSized.proof.batch.batches = false := by decide +kernel

/-- The gate reads of the list each check's bits, and so the list's length, alone. -/
theorem gate_checks_reads (l : Lines) (cs cs' : List RangeCheck) (a b c : Nat)
    (h : cs.map rangeCheckBits = cs'.map rangeCheckBits) :
    missedInTheChecks l cs a b c = missedInTheChecks l cs' a b c := by
  have hl : cs.length = cs'.length := by
    have := congrArg List.length h
    simpa using this
  have he : cs.isEmpty = cs'.isEmpty := by
    cases cs <;> cases cs' <;> simp_all
  unfold missedInTheChecks
  rw [h, hl, he]

/-- In the ledger's own letters. -/
theorem gate_checks_of (x : Shapes)
    (hx : x.rangeChecks.map rangeCheckBits = checksFull.map rangeCheckBits) :
    missedInTheChecks recordLines x.rangeChecks writtenSized.key.once.shape.fold.columns
      writtenSized.link.shape.columnsFirst writtenSized.proof.batch.batches = false := by
  rw [gate_checks_reads _ _ _ _ _ _ hx]
  exact gate_checks

theorem gate_checks_plant : missedInTheChecks recordLines
    (⟨65536, 5990, 128, 129, 2 ^ 13, (7, 7)⟩ :: checksFull)
    writtenSized.key.once.shape.fold.columns writtenSized.link.shape.columnsFirst
    writtenSized.proof.batch.batches = true := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.gate_checks
#print axioms Johnson.AtFull.Made.gate_checks_reads
#print axioms Johnson.AtFull.Made.gate_checks_of
#print axioms Johnson.AtFull.Made.gate_checks_plant
