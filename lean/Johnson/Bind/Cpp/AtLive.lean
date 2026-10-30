-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/AtLive.lean: THE HEADLINE FORMS: at every set of public files in scope that is read
AND AT WHICH THE DESCRIPTION's TESTS ON THE PUBLIC FILES (protocolDataWellFormed) PASS: correctness of extraction
for the committer of theCpp T prove, and the body of the goal on binding, of that description
(Johnson/Bind/Cpp/Defs.lean), FROM THE TIE AT SUCH FILES (TieLive), which is a hypothesis here; at
theTwin g it is tieLive (Johnson/Bind/Cpp/TheTie.lean). Calls alone.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
"Binding" in this file is the opening form, BindsWith (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (BindsWith.atRandomness). It is not the index binding of ZKCP/Defs.lean's
HasIndexBinding: soundness under the files' policy (G8bits, Ladder/Bits.lean) has that form, for the
claim "meets the policy" (the tie is typed at exact match: sound_iff,
VerifiableInference/Agreement.lean), and speaks of every commitment, whoever made it.

Why. The tie, whole (Tie, Defs.lean), speaks of every Z whose frame has salts of 40 bytes, out of
scope and dead frames among them: wider than these forms use. In scope, that protocolDataWellFormed passes gives
the salts (saltAt_of_live, Johnson/Bind/Cpp/SaltAt.lean). An accept of verify, at any parser and any
hash function, gives both "in scope" and that protocolDataWellFormed passes (scope_and_live_of_accept,
Johnson/Goal/Description/AcceptGivesLive.lean): so these forms leave out only files at which verify
accepts nothing.

Main names (namespace Bind.Cpp).
  TieLive T: the tie at every Z in scope at which protocolDataWellFormed passes. tieLive_of_tie: from the tie
    whole.
  **extractsCommitted_live**: CORRECTNESS OF EXTRACTION (ExtractsCommittedWeights,
    VerifiableInference/MoreStatements.lean): sample a seed, commit: from the commitment ID and that
    run's queries the description's extractor gives the committed weights, but with probability
    bindingErrorInQueries (2^35 + 2), about 2^-89.
  **bindsAt_live**: the body of G9bits (Ladder/Bits.lean) at such a Z.
  extractsCommitted_live_theTwin, bindsAt_live_theTwin: the same at Bind.Twin.twinID and every
    generator: the count is paid: ONE hypothesis is left: TieLive (theTwin g) (proved: tieLive,
    Johnson/Bind/Cpp/TheTie.lean).
Limits. Those of OfTie.lean. THIS IS NOT G9bits: it does not reach all files in scope that are read.
It is none of the goals of Ladder.lean and Ladder/Bits.lean: no goal is stated here.
THAT protocolDataWellFormed PASSES AT ANY FILES IS NO THEOREM OF THE MAIN LIBRARY: at the library's written copies
of the two stored sets of public files it is evaluated. There it passes by theorems of a side
library, outside the main library and with that library's own limits
(AtFullSide/Bind/LiveAtNamed.lean). AT THE FULL-SIZE SHAPE. The generator and
the prover are letters. protocolDataWellFormed is more than is needed: that the planner returns suffices for the
salts (saltAt_iff).
Terms: lean/TERMS.md, lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.AtTwin
import Johnson.Bind.Cpp.Extracts
import Johnson.Bind.Cpp.SaltAt

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

variable (T : Letters)
  (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **THE TIE AT THE FILES OF THE HEADLINE**: at every Z in scope at which protocolDataWellFormed passes. -/
def TieLive (T : Letters) : Prop :=
  ∀ Z : PublicFiles, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → TieAt T Z

/-- From the tie whole. -/
theorem tieLive_of_tie (tie : Tie T) : TieLive T :=
  fun Z hs hl => tie Z (saltAt_of_live hs hl)

/-- **CORRECTNESS OF EXTRACTION FOR THE COMMITTER OF theCpp T prove**, at every Z in scope that is
read and at which protocolDataWellFormed passes. -/
theorem extractsCommitted_live (tie : TieLive T) (cnt : Count T) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hs : InScope Z = true) (hr : readFiles Z = .ok pp) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ExtractsCommittedWeights (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp T prove)).extractor Z (settingsOfRead pp)) (bindingErrorInQueries (twinBudget + 2)) :=
  extractsCommitted_cpp T prove Z pp hr (tie Z hs hl) (cnt Z)

/-- **THE BODY OF G9bits**, at every Z in scope that is read and at which protocolDataWellFormed passes. -/
theorem bindsAt_live (tie : TieLive T) (cnt : Count T) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hs : InScope Z = true) (hr : readFiles Z = .ok pp) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (∀ w ρ, ((atSecondHashFunction (theCpp T prove)).commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound
        honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp T prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  bindsAtZ_cpp T prove Z pp hr (tie Z hs hl) (cnt Z)

/-- Correctness of extraction for the committer of theCpp (theTwin g), at every generator. -/
theorem extractsCommitted_live_theTwin (g : Shape → Seed → Digest → Digest → Coins)
    (tie : TieLive (theTwin g)) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ExtractsCommittedWeights
      (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp))
      (bindingErrorInQueries (twinBudget + 2)) :=
  extractsCommitted_live (theTwin g) prove tie (count_theTwin g) Z pp hs hr hl

/-- The body of G9bits at Bind.Twin.twinID, at every generator. -/
theorem bindsAt_live_theTwin (g : Shape → Seed → Digest → Digest → Coins)
    (tie : TieLive (theTwin g)) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  bindsAt_live (theTwin g) prove tie (count_theTwin g) Z pp hs hr hl

end Bind.Cpp

end

#print axioms Bind.Cpp.tieLive_of_tie
#print axioms Bind.Cpp.extractsCommitted_live
#print axioms Bind.Cpp.bindsAt_live
#print axioms Bind.Cpp.extractsCommitted_live_theTwin
#print axioms Bind.Cpp.bindsAt_live_theTwin
