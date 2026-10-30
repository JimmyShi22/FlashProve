-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FoldedAtKeyBookKernel.lean

The book's test on laying at the key file's test on G_u, BY THE KERNEL's OWN EVALUATION: the twin of
OmegaAtKeyBookKernel.lean's lays_O. It imports FoldedAtKeyBookGuards.lean, where the evaluator says
the same first.

  lays_U   laysB in the shared chain, at the written book
  lays_U_bent, lays_U_short   controls: each says no

Limits. Public numbers alone: nothing is played, and chainSteps is not here. atFull is false where
fullPub is none, so a yes here is not true for nothing. Nothing on completeness, on soundness or on
what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.FoldedAtKeyBookGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.FoldedAtKeyBook
open AtPublicFiles.KeyBook (atFull keyBook)
open H2K.Member (piKUFull)

set_option maxRecDepth 1000000 in
/-- laysB at the job with the place's numbers, at the written book. -/
theorem lays_U : atFull (fun K => laysU (keyBook K) jobKUB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Control: a place that the book has no cut for. -/
theorem lays_U_bent : atFull (fun K => !laysU (keyBook K)
    { jobKUB with p := { piKUFull with place := ⟨2, none, 99, .K12⟩ } }) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Control: the job with its last member dropped. -/
theorem lays_U_short : atFull (fun K => !laysU (keyBook K)
    { jobKUB with members := jobKUB.members.dropLast }) = true := by decide +kernel

end ProofFile.Honest.K12.FoldedAtKeyBook

#print axioms ProofFile.Honest.K12.FoldedAtKeyBook.lays_U
#print axioms ProofFile.Honest.K12.FoldedAtKeyBook.lays_U_bent
#print axioms ProofFile.Honest.K12.FoldedAtKeyBook.lays_U_short
