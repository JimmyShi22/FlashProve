-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LaysLastTestBite.lean: the evaluation of LaysLastTest can fail: at the written record's own place, piece 0, no cut stands. Imported by no law.

Limits.
- The full size alone: closed terms. An evaluation in Lean's kernel; no independent checker has
  replayed it.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.LaysBookFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piWFull)

set_option maxRecDepth 1000000 in
/-- The evaluation can fail. -/
theorem lays_W_bite : laysLastB bookW (bareJob piWFull membersWF (some (senderW, 1)) :
    TestJob Unit Unit) = false := by decide +kernel

end AtFullSide.K12

#print axioms AtFullSide.K12.lays_W_bite
