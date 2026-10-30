-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/AtTwin.lean: THE STATEMENTS OF Johnson/Bind/Cpp/OfTie.lean AT THE RUNNING COMMITTER
OF Johnson/Bind/Twin.lean (Bind.Twin.twinID, Johnson/Bind/TwinAlgorithm.lean), at every generator:
the count is paid, so ONE hypothesis is left beside "read": the tie (proved where the frame's salts
have 40 bytes: tieAt, Johnson/Bind/Cpp/TheTie.lean). Calls alone.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
"Binding" in this file is the opening form, BindsWith (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (BindsWith.atRandomness). It is not the index binding of ZKCP/Defs.lean's
HasIndexBinding: soundness under the files' policy (G8bits, Ladder/Bits.lean) has that form, for the
claim "meets the policy" (the tie is typed at exact match: sound_iff,
VerifiableInference/Agreement.lean), and speaks of every commitment, whoever made it.

Main names (namespace Bind.Cpp).
  count_full: the running committer's bound on its queries at the full size's shape, as a number, by
    the kernel's evaluation: 17,179,869,330, about 2^34.
  **count_theTwin**: Count (theTwin g), at every g.
  **bindsAtZ_theTwin**: the body of G9bits (Ladder/Bits.lean) at one Z, from "read" and the tie.
Limits. Those of OfTie.lean. The generator g is a letter: a constant one passes every theorem here.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.OfTie
import Johnson.Bind.TwinBudget

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

/-- Its bound on the queries at the full size's shape, as a number. -/
theorem count_full : Bind.Twin.calls shapeFull * 2 = 17179869330 := by decide +kernel

theorem count_le : Bind.Twin.calls shapeFull * 2 ≤ twinBudget := by
  rw [count_full]
  unfold twinBudget
  norm_num

/-- The first letter of theTwin g. -/
theorem id_theTwin (g : Shape → Seed → Digest → Digest → Coins) :
    (theTwin g).id = Bind.Twin.twinID := rfl

/- Lean compares these by their names: at the constant shape their unfolding does not end. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget theTwin
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan
  FlashProve.theItem LayoutsByPublicReading.commitAtCoins

/-- **THE COUNT IS PAID at it**, at every generator. -/
theorem count_theTwin (g : Shape → Seed → Digest → Digest → Coins) : Count (theTwin g) := by
  intro Z t
  rw [id_theTwin]
  exact Bind.Twin.queryBound_twinID_of shapeFull twinBudget count_le Z.pol Z.lay Z.KL t

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **THE BODY OF G9bits AT ONE Z, at Bind.Twin.twinID and every generator**: one hypothesis is left
beside "read": the tie. At a Z whose frame's salts have not 40 bytes the tie is false at theTwin g
(argued), and this says nothing there. -/
theorem bindsAtZ_theTwin (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (tie : TieAt (theTwin g) Z) :
    (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  bindsAtZ_cpp (theTwin g) prove Z pp hr tie (count_theTwin g Z)

end Bind.Cpp

end

#print axioms Bind.Cpp.count_full
#print axioms Bind.Cpp.count_le
#print axioms Bind.Cpp.id_theTwin
#print axioms Bind.Cpp.count_theTwin
#print axioms Bind.Cpp.bindsAtZ_theTwin
