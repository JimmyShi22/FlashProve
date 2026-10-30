-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OmegaAtKeyBookKernel.lean

The book's two tests at the key file's test on G_omega, BY THE KERNEL's OWN EVALUATION. It imports
OmegaAtKeyBookGuards.lean, where the evaluator says the same first.

  `lays_O`, `ties_O`   `laysB` in the shared chain and `tiesOB`, at the written book
  `lays_O_bent`, `lays_O_short`, `ties_O_bare`, `ties_O_3`, `ties_O_1`   controls: each says no

Limits. Public numbers alone: nothing is played, and `chainSteps` is not here. `lays_of_B` asks
`proverSideOfProximityTest J`, so it does not apply to a half behind the guard. `atFull` is false where `fullPub` is
none, so a yes here is not true for nothing. Nothing on completeness, on soundness or on what is
hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.OmegaAtKeyBookGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.OmegaAtKeyBook
open AtPublicFiles.KeyBook (atFull keyBook)
open H2K.Member (piKOFull)

set_option maxRecDepth 1000000 in
/-- `laysB` at the job with the place's numbers, at the written book. -/
theorem lays_O : atFull (fun K => laysO (keyBook K) jobKOB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- `tiesOB` at the place and the two members, at the written book. -/
theorem ties_O : atFull (fun K => tiesO (keyBook K) 2) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Control: a place that the book has no cut for. -/
theorem lays_O_bent : atFull (fun K => !laysO (keyBook K)
    { jobKOB with p := { piKOFull with place := ⟨2, none, 99, .K12⟩ } }) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Control: the job with its last member dropped. -/
theorem lays_O_short : atFull (fun K => !laysO (keyBook K)
    { jobKOB with members := jobKOB.members.dropLast }) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Control: the book without its carried entries. -/
theorem ties_O_bare : atFull (fun K => !tiesO (keyBook K false) 2) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Control: one member more. -/
theorem ties_O_3 : atFull (fun K => !tiesO (keyBook K) 3) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Control: one member fewer. -/
theorem ties_O_1 : atFull (fun K => !tiesO (keyBook K) 1) = true := by decide +kernel

end ProofFile.Honest.K12.OmegaAtKeyBook

#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.lays_O
#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.ties_O
#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.lays_O_bent
#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.lays_O_short
#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.ties_O_bare
#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.ties_O_3
#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.ties_O_1
