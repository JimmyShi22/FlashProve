-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/WP.lean: THE WRITTEN DESCRIPTION AT WHICH THE PROOF FILE's TESTS ON THE
PLAN ARE ASKED OF LEAN's KERNEL, AT THE FULL SIZE: `WP`. Two definitions, and the lengths of its
lists by an evaluation in Lean's kernel.

What it is made of. All of it lies written. The declared rounds (`declProofFull`): the distinct
declared rounds (`VerifiableInference.PlanWritten.declRecsFull`, Johnson/Unfolds/DeclRecsLit.lean:
the proof file's; a `Johnson.KB8.declRecsFull` is the key file's), laid out by `unrunG`
(Johnson/G/RunsDefs.lean) along the three written lists of runs (`dryProofRunsFull0`, `1`, `2`,
Johnson/G/DryProofLit.lean). The cut into sub-protocols: `cutFirstFull`, `cutSharedFull`,
`cutSecondFull` (Johnson/Desc/Ok/PlanWritten/CutLit.lean). Put together by `wOf`
(Johnson/AtFull/ProofPlan/WrittenDesc.lean): every block's own test and fileOk ARE THE LITERAL true.

The depth, 32, is not free: one stored part is opened in the written rounds (a round "LOC" of the
shared chain), and its depth is 32: at another depth the test on the stored parts' depth says no (at
31: Johnson/AtFull/ProofPlan/At/No/Depth.lean).

  `declProofFull`, `WP`: the two definitions. `decl_runs`: the first, as an equation.
  `decl_lengths`: the three lists have 48293, 68 and 30 rounds. One limit is raised for it:
    maxRecDepth to 1000000.

Limits. THAT ANY DESCRIPTION HAS THESE ROUNDS OR THIS CUT IS NO THEOREM: the written values were
printed off `ProofFile.onlineDescription` at the goals' stored full-size public files by Lean's evaluator; their
files say by whom and how they were held. Nothing is said here of the proof file's own description.
More closed facts on the parts: Johnson/AtFull/ProofPlan/WPFacts.lean. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.WrittenDesc
import Johnson.Unfolds.DeclRecsLit
import Johnson.G.DryProofLit
import Johnson.G.RunsDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open VerifiableInference.PlanWritten (declRecsFull cutFirstFull cutSharedFull cutSecondFull)
open Johnson.G (dryProofRunsFull0 dryProofRunsFull1 dryProofRunsFull2 lenE length_of_lenE)
open Johnson.G.Runs (unrunG)

/-- **The proof file's three lists of declared rounds at the full size, written**: the distinct
declared rounds along the written runs (how often, which). -/
def declProofFull : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound :=
  (unrunG declRecsFull dryProofRunsFull0, unrunG declRecsFull dryProofRunsFull1,
    unrunG declRecsFull dryProofRunsFull2)

/-- The definition, as an equation: for whoever states these rounds in the general form. -/
theorem decl_runs :
    declProofFull = (unrunG declRecsFull dryProofRunsFull0, unrunG declRecsFull dryProofRunsFull1,
      unrunG declRecsFull dryProofRunsFull2) := rfl

/-- **The written description.** -/
def WP : FileDescription Unit := wOf cutFirstFull cutSharedFull cutSecondFull declProofFull 32

set_option maxRecDepth 1000000 in
theorem decl_lengths :
    (declProofFull.1.length, declProofFull.2.1.length, declProofFull.2.2.length) =
      (48293, 68, 30) := by
  have h : lenE 0 declProofFull.1 = 48293 := by decide +kernel
  have g : (declProofFull.2.1.length, declProofFull.2.2.length) = (68, 30) := by decide +kernel
  rw [length_of_lenE h]
  exact congrArg (Prod.mk 48293) g

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.decl_runs
#print axioms P2Law.ProofPlan.decl_lengths
