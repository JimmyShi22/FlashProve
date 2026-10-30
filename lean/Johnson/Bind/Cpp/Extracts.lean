-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/Extracts.lean: CORRECTNESS OF EXTRACTION FOR THE COMMITTER OF theCpp T prove, IN
THE LIBRARY's OWN FORM (ExtractsCommittedWeights, VerifiableInference/MoreStatements.lean: the
randomness is drawn by the system's own sampler), at one set of public files, FROM THE TIE AND THE
COUNT THERE. The tie is a hypothesis here (at theTwin g: tieAt, Johnson/Bind/Cpp/TheTie.lean); the
count is proved at theTwin g (Johnson/Bind/Cpp/AtTwin.lean).
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
"Binding" in this file is the opening form, BindsWith (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (BindsWith.atRandomness). It is not the index binding of ZKCP/Defs.lean's
HasIndexBinding: soundness under the files' policy (G8bits, Ladder/Bits.lean) has that form, for the
claim "meets the policy" (the tie is typed at exact match: sound_iff,
VerifiableInference/Agreement.lean), and speaks of every commitment, whoever made it.

Main names.
  By BindsWith.extractsDrawn (Johnson/Bind/ExtractsDrawn.lean), general in the system.
  **extractsCommitted_cpp** (namespace Bind.Cpp): at theCpp: at bindingErrorInQueries (2^35 + 2), about 2^-89.
Limits. Those of Johnson/Bind/Cpp/OfTie.lean. The sampler of theCpp draws a seed; what the generator
makes of it is a letter. Nothing on index privacy.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.OfTie
import Johnson.Bind.ExtractsDrawn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀
  FlashProve.thePlan FlashProve.theItem LayoutsByPublicReading.commitAtCoins

variable (T : Letters)
  (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **CORRECTNESS OF EXTRACTION FOR THE COMMITTER OF theCpp T prove, AT ONE Z**: for all weights:
draw a seed,
commit; from the commitment ID and that run's queries the description's extractor gives these
weights, but with probability bindingErrorInQueries at the run's count. From "read", the tie and the count at
Z. -/
theorem extractsCommitted_cpp (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (tie : TieAt T Z) (cnt : CountAt T Z) :
    ExtractsCommittedWeights (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp T prove)).extractor Z (settingsOfRead pp)) (bindingErrorInQueries (twinBudget + 2)) :=
  (bindsAtZ_cpp T prove Z pp hr tie cnt).2.extractsDrawn (2 ^ 256 - 1) (fun t => .inl t) rfl
    (twinBudget + 2) fun w ρ => commit_count T Z cnt (settingsOfRead pp) w ρ

end Bind.Cpp

end

#print axioms Bind.Cpp.extractsCommitted_cpp
