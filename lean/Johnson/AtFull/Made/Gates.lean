-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/Gates.lean: THE FIVE GATES AND THE FOUR SMALL CONDITIONS OF `Params.configure`,
AT THE WRITTEN SIZES AND PLANS, IN THE LEDGER's OWN LETTERS. One structure, one theorem.

Why. `configure_of_parts` (Johnson/AtFull/Made/Ledger.lean) takes six premises f₁ … f₆. Each is
shown in a file of its own (GateLinks, GateRanges, GateTable, GateChecks, GateKey, GateSmall). Here
they stand together, so that the ledger's caller lays in one term, and so that ALL THAT THE SIX READ
OF THE RUN's SHAPES x AND OF THE FIRST PLAN stands in one place.

What is said. `ShapesRead x first`: FIVE FACTS: 13 pending rows; 25 identifiers; the range checks
have the written list's bits; the first plan's lists of positions are the written ones; each
segment's count of scalars returns the written number. `gates_written`: under it, the ledger's d₁
and one closed equation, f₁ … f₆, each to the letter of the ledger at l := `recordLines`, z :=
`writtenSized`, shared | second := the proof file's second and third written plans, keyShared |
keySecond := the key file's, entry := the entry file's.

WHAT IS LEFT IN FRONT, AND WHOSE IT IS. (1) `ShapesRead`: pending, identifiers, checks: facts on
what `shapesWith` returns (the ledger's c₁); lists: on what `firstPlan` returns (its e₁); scalars:
25 equations on `x.sub.plan j m`, closures over the public part: THE WEIGHT OF f₁ LIES THERE. (2)
d₁: the ledger's own premise. (3) hs: a closed equation at the written sizes (ScalarsKeyJoin.lean
asks the kernel). (4) That the ledger's z, shared, second, keyShared, keySecond, entry ARE these
written terms is its c₂, e₂, e₃, d₂, d₃, d₄: for the last five closed equations lie
(`proof_shared_written`, `proof_second_written`, `shared_written`, `second_written`,
`entry_written`).

Limits. A joining. `ShapesRead` is shown of no shapes here. Its three written lists were copied off
a run's print; a second run holds the five facts against the lists themselves (an evaluation; no
proof). Nothing on soundness.
-/
import Johnson.AtFull.Made.GateLinks
import Johnson.AtFull.Made.GateRanges
import Johnson.AtFull.Made.GateTable
import Johnson.AtFull.Made.GateChecks
import Johnson.AtFull.Made.GateKey
import Johnson.AtFull.Made.GateSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull)

/-- **All that the six premises read of the run's shapes and of the first plan.** -/
structure ShapesRead (x : Shapes) (first : Planned) : Prop where
  pending : x.sub.pendingRows = 13
  identifiers : x.identifiers.length = 25
  checks : x.rangeChecks.map rangeCheckBits = checksFull.map rangeCheckBits
  lists : listsOf first = listsFull
  scalars : ∀ j (hj : j < writtenSized.proof.request.link.length) (hj' : j < scalarsFull.length),
    scalarsOf writtenSized.proof.set
      (forEach (List.range (momentsOf writtenSized.proof.request.link[j])) fun m =>
        x.sub.plan j m) = .ok scalarsFull[j]

/-- **f₁ … f₆ at the written values.** -/
theorem gates_written (x : Shapes) (first oneTime : Planned) (R : ShapesRead x first)
    (d₁ : Plan.oneTimePlan writtenSized.key = .ok oneTime)
    (hs : Plan.lookupScalars writtenSized.key = .ok 34933) :
    missedInTheLinks recordLines writtenSized.proof x.sub first = .ok false ∧
    Plan.missedInTheRanges writtenSized.key = false ∧
    missedOnTheTable recordLines
      ⟨writtenSized.proof.batch, writtenSized.proof.codes, proofThree.B.plan, proofThree.C.plan,
        x.sub.pendingRows, 0⟩
      ⟨writtenSized.key.once, writtenSized.key.codes, keyThree.B.plan, keyThree.C.plan,
        if sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length)) != 0 then
          sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length)) else 1,
        sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length))⟩
      writtenSized.link writtenSized.entryCodes pricedEntryFull = false ∧
    missedInTheChecks recordLines x.rangeChecks writtenSized.key.once.shape.fold.columns
      writtenSized.link.shape.columnsFirst writtenSized.proof.batch.batches = false ∧
    Plan.keyOk writtenSized.key = true ∧
    (x.identifiers.length != writtenSized.proof.request.link.length ||
      writtenSized.proof.request.atStart.length != 1 || x.sub.pendingRows == 0 ||
      writtenSized.proof.request.link.map (·.plain) !=
        List.replicate (writtenSized.proof.request.link.length - 1) 0 ++ [1]) = false :=
  ⟨gate_links_of x.sub first R.lists R.scalars, gate_ranges_of d₁ hs, gate_table_of x R.pending,
    gate_checks_of x R.checks, gate_key,
    gate_small_of x R.identifiers (by rw [R.pending]; decide)⟩

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.gates_written
