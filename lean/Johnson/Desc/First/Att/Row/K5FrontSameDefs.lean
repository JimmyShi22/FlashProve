-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontSameDefs.lean: the runs of two written lists of the full size,
each run
with its entry: the first of the planner's written lists of rounds for the proof file
(`proofThree.A`, Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean; 17,109 runs) and the first of the
written lists of the dry runs (`dryProofFull.1`, Johnson/G/DryProofLit.lean; 17,108 runs): 48,293
entries each. Two definitions and two laws; nothing is evaluated.
  `runsA` · `runsD` · `priced_is` · `dry_is`: the two lists' entries are these runs written out.
Limits. Both lists are WRITTEN values: whence each is, its own file's head says. Nothing on
soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5FrontRuns
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
import Johnson.G.DryProofLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open Johnson.G (dryProofFull dryProofRecsFull dryProofRunsFull0 pricedProofRecsFull0
  pricedProofRunsFull0)
open Johnson.G.Runs (unrunG valRuns)
open VerifiableInference.Number.ByRuns (proofThree)

/-- The planner's first written list: its runs, each with its entry. -/
def runsA : List (Nat × Fmt.Entry) :=
  (valRuns pricedProofRecsFull0 pricedProofRunsFull0).map fun x => (x.1, x.2.entry)

/-- The dry runs' first written list: its runs, each with its entry. -/
def runsD : List (Nat × Fmt.Entry) :=
  (valRuns dryProofRecsFull dryProofRunsFull0).map fun x => (x.1, x.2.1.entry)

theorem dry_is : dryProofFull.1.map (·.1.entry) = outOf runsD := by
  show (unrunG dryProofRecsFull dryProofRunsFull0).map (·.1.entry) = _
  rw [outOf_val, outOf_map]
  rfl

theorem priced_is : proofThree.A.plan.plan.entries = outOf runsA := by
  show (unrunG pricedProofRecsFull0 pricedProofRunsFull0).map (·.entry) = _
  rw [outOf_val, outOf_map]
  rfl

end H2K5.Row

#print axioms H2K5.Row.dry_is
#print axioms H2K5.Row.priced_is
