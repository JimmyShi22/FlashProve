-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/TableLines.lean: at which round each tree of the shared and the
last chain is sent, as closed numbers at the written description `WP`, and the same out of the test's
places: first by Lean's evaluator, then by the kernel. A thread's field `fixed` asks just these numbers,
with no slack: a tree's table reads the challenges drawn in front of the round that sends it.

  `sentShared`, `sentLast`   the lists of rounds, read off the declared rounds by `sentIn`
                 (Honest/Small/FixedSent.lean)
  `sent_shared`, `sent_last`   they are [1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 63] and [7, 14, 20, 26]
  `seed_U`, `seed_O`, `seed_W`   the test's own numbers give the same: 8 rounds stand in front of the
                 test on G_u, 43 in front of the test on G_omega; `seedRound` (K12/ScriptLots.lean)
  `trees_shared`   the shared chain sends 11 trees
  `sent_bent`, `seed_bent`   controls: one round more: no

Limits. Public numbers. Round numbers count from the chain's first own round; a last chain's thread adds
its field `front`. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLines
import Johnson.Desc.ProofFile.Honest.K12.ScriptLots
import Johnson.Desc.ProofFile.Honest.Small.FixedSent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest.K12 (seedRound)
open P2Law.ProofPlan (WP declProofFull)
open H2K.Member (piUFull piOFull piWFull)

/-- The round of each of the shared chain's eleven trees. -/
def sentShared : List Nat := (List.range 11).map (ProofFile.Honest.Small.sentIn declProofFull.2.1)

/-- The round of each of the last chain's four own trees. -/
def sentLast : List Nat := (List.range 4).map (ProofFile.Honest.Small.sentIn declProofFull.2.2)

#eval sentShared
#eval sentLast
#eval (List.range 4).map (seedRound piUFull.nums.stages)
#eval (List.range 3).map (seedRound piOFull.nums.stages)
#eval (List.range 4).map (seedRound piWFull.nums.stages)

-- Foretold, off the places' lists of oracle messages.
#guard sentShared == [1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 63]
#guard sentLast == [7, 14, 20, 26]
#guard (List.range 4).map (fun τ => 8 + seedRound piUFull.nums.stages τ) == [17, 25, 32, 39]
#guard (List.range 3).map (fun τ => 43 + seedRound piOFull.nums.stages τ) == [49, 56, 63]
#guard (List.range 4).map (seedRound piWFull.nums.stages) == [7, 14, 20, 26]
#guard (sharedR.map (·.2)).sum == 11
-- Controls.
#guard sentShared != [1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 64]
#guard (List.range 4).map (seedRound piUFull.nums.stages) != [17, 25, 32, 39]

theorem sent_shared : sentShared = [1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 63] := by decide +kernel

theorem sent_last : sentLast = [7, 14, 20, 26] := by decide +kernel

theorem seed_U : (List.range 4).map (fun τ => 8 + seedRound piUFull.nums.stages τ) =
    [17, 25, 32, 39] := by decide +kernel

theorem seed_O : (List.range 3).map (fun τ => 43 + seedRound piOFull.nums.stages τ) =
    [49, 56, 63] := by decide +kernel

theorem seed_W : (List.range 4).map (seedRound piWFull.nums.stages) = [7, 14, 20, 26] := by
  decide +kernel

theorem trees_shared : (sharedR.map (·.2)).sum = 11 := by decide +kernel

theorem sent_bent : sentShared ≠ [1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 64] := by decide +kernel

theorem seed_bent : (List.range 4).map (seedRound piUFull.nums.stages) ≠ [17, 25, 32, 39] := by
  decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.sent_shared
#print axioms ProofFile.Honest.K12.AtFile.sent_last
#print axioms ProofFile.Honest.K12.AtFile.seed_U
#print axioms ProofFile.Honest.K12.AtFile.seed_O
#print axioms ProofFile.Honest.K12.AtFile.seed_W
#print axioms ProofFile.Honest.K12.AtFile.trees_shared
#print axioms ProofFile.Honest.K12.AtFile.sent_bent
#print axioms ProofFile.Honest.K12.AtFile.seed_bent
