-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/NoTwoOpeningsAtLive.lean: NO TWO OPENINGS, BUT WITH PROBABILITY 2 · bindingErrorInQueries t,
FOR THE STAND-IN COMMITTER OF theCpp (theTwin g), at every set of public files in scope that is read
AND AT WHICH THE DESCRIPTION's TESTS ON THE PUBLIC FILES (protocolDataWellFormed) PASS. One theorem, by one
application: noTwoOpenings_salt (Johnson/Bind/Cpp/TheTie.lean) at saltAt_of_live
(Johnson/Bind/Cpp/SaltAt.lean).
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE's COMMITTING PROGRAM CANNOT BE OPENED TO TWO
DIFFERENT WEIGHTS: the committer is the Lean text of Johnson/Bind/Twin.lean, a model of one part of
that program; no theorem ties them.

What it says, in plain words. Fix such public files Z and a generator g; then the hash function is
sampled. An adversary asks it at most t queries and names a commitment ID and two pairs of weights
and randomness (each a seed or coins). The probability that this committer gives that ID from both
pairs while the two weights differ is at most 2 · bindingErrorInQueries t: twice the error of the opening form
(bindsAt, Johnson/Bind/Cpp/TheTie.lean). The form is NoTwoOpenings
(VerifiableInference/MoreStatements.lean).

Limits. Those of Johnson/Bind/Cpp/TheTie.lean travel whole. THIS IS NOT G9bits: the goal has another
form, the opening form (BindsWith), and asks it at all files in scope that are read. It is none of
the goals of Ladder.lean and Ladder/Bits.lean: no goal is stated here.
No theorem of the main library says that protocolDataWellFormed passes at any files. At the library's written
copies of the two stored sets of public files it passes by theorems of a side library, outside the
main library and with that library's own limits (AtFullSide/Bind/LiveAtNamed.lean); no two openings
at these copies, without that premise: noTwoOpenings_zFull, noTwoOpenings_zGap
(AtFullSide/Bind/TheTieAtNamed.lean).
The committer's two runs are not among the adversary's t queries. Nothing is said of two openings
with the same weights and different randomness.
Terms: lean/TERMS.md, lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.TheTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Bind.Twin (Shape Table)

/- Lean compares these by their names. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget theTwin
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan
  FlashProve.theItem LayoutsByPublicReading.commitAtCoins

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **No two openings, for the stand-in committer of theCpp (theTwin g)**: nobody names one
commitment ID and two different weights, each with a seed or coins of its own pick, such that this
committer gives that ID from both, but with probability 2 · bindingErrorInQueries t (t: the adversary's
queries), at every Z in scope that is read and at which protocolDataWellFormed passes. -/
theorem noTwoOpenings_live (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    NoTwoOpenings (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
      fun t => 2 * bindingErrorInQueries t :=
  noTwoOpenings_salt prove g Z pp hr (saltAt_of_live hs hl)

end Bind.Cpp

end

#print axioms Bind.Cpp.noTwoOpenings_live
