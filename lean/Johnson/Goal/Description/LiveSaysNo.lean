-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Description/LiveSaysNo.lean: a negative test of `protocolDataWellFormed`
(Johnson/Goal/Description/Live.lean), the test on the public files with which the Lean verifier
gates its three decisions: it can reject. At the library's written copy of the full-size public
files with one line of the parameter file changed, it rejects. A joining of laws; nothing is
evaluated. This file states no goal: it defines nothing, and holds three theorems about names that
stand elsewhere.

Why. Where `protocolDataWellFormed` rejects, the verifier rejects everything, and a theorem on what it accepts
holds there idly. So a theorem "protocolDataWellFormed accepts at these files" is wanted; and such a theorem would
be worth little of a test that accepted at all files. Here is a triple of files at which it rejects.

The files. `VerifierAndGoals.zAt 256 257 0` (Johnson/Goal/Files/ScopeAtPolicies.lean): `VerifierAndGoals.storedPublicFiles`'s
layout file and scale file, and its parameter file with the acceptance policy's three numbers set
to C = 256, theta = 257, cap = 0: theta lies above C. The planner's own text rejects such a policy
(`refuses_theta_above`, Johnson/Goal/Description/RefusesAbove.lean), so the public part is not
made, and `protocolDataWellFormed` rejects (`theLive_no_of_public`, Johnson/Goal/Description/SeatsEvery.lean).

Main names.
* `above_out_of_scope`: these files are outside the goals' scope.
* `theLive_no_of_refusal`: at any files at which the public part is not made, `protocolDataWellFormed` rejects.
* **`theLive_no_above`**: `protocolDataWellFormed (asDescriptionFiles (zAt 256 257 0)) = false`.

Limits.
* THE FILES OF THIS NEGATIVE TEST ARE OUTSIDE THE GOALS' SCOPE. No files in scope are known at which
  `protocolDataWellFormed` rejects. In this family of files none can be had, given that it accepts at `storedPublicFiles`:
  `zAt C theta cap` is in scope exactly within four bounds on the three numbers
  (`inScope_zAt_iff`), and the law `live_up` (Johnson/LPFPol/LiveAtPolicy.lean) carries an accept
  at `storedPublicFiles` to all of these. The scope is wider than this family: five more free numbers of the
  parameter file, and the scale file: whether `protocolDataWellFormed` accepts at all of it is not said here.
* ONE REASON FOR A REJECTION IS TRIED: a comparison on a number that was read, theta against C. The
  two parameter files differ in the one line theta (256 | 257). The proof goes by the key file's
  maker. By the text the plan's maker, which `protocolDataWellFormed` asks first, returns nothing there either:
  its first line makes the same public part (`plannedAtO`,
  Johnson/Desc/Ok/PlanWritten/PublicAt.lean). So the test's own comparisons of numbers (`dataWellFormedAtFullSizeDepth`)
  are never reached. A rejection for a bad layout file, a bad scale file or a wrong size is not
  shown.
* Beside a theorem that `protocolDataWellFormed` accepts at `storedPublicFiles` it shows that the test tells apart two
  parameter files that differ in the line theta, and no more; nor that what the test asks is enough
  for any purpose.
* That `protocolDataWellFormed` accepts anywhere is not shown here.
* Nothing on soundness, completeness or hiding.

-/
import Johnson.Goal.Description.RefusesAbove
import Johnson.Goal.Description.SeatsEvery
import Johnson.Goal.Files.ScopeAtPolicies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open VerifiableInference.PlanWritten (publicOfO)

/-- The files of the negative test are outside the goals' scope: theta lies above C. -/
theorem above_out_of_scope : InScope (zAt 256 257 0) = false :=
  Bool.eq_false_iff.2 fun h => absurd (inScope_zAt_iff.1 h).2.1 (by decide)

/-- Where the public part is not made, the test rejects. The files stand as a letter here: with the
named files in its place Lean would compare whole files byte by byte. -/
theorem theLive_no_of_refusal (Z : PublicFiles)
    (hr : ∀ X, publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) ≠ .ok X) :
    protocolDataWellFormed (asDescriptionFiles Z) = false := by
  cases h : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) with
  | error e => exact theLive_no_of_public (asDescriptionFiles Z) e h
  | ok X => exact absurd h (hr X)

/-- **A negative test: `protocolDataWellFormed` rejects.** -/
theorem theLive_no_above : protocolDataWellFormed (asDescriptionFiles (zAt 256 257 0)) = false :=
  theLive_no_of_refusal (zAt 256 257 0) fun X => by
    rw [zAt_pol]
    exact refuses_theta_above _ _ _ X

end FlashProve

#print axioms FlashProve.above_out_of_scope
#print axioms FlashProve.theLive_no_of_refusal
#print axioms FlashProve.theLive_no_above
