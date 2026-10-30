-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WiderComplete.lean: WHAT THE GOALS' SYSTEM IS AT A MEMBER OF theWider
(Johnson/Goal/Conditions/WiderAtThe.lean), FIELD BY FIELD: equations, each by unfolding.

Why. The frame of completeness (completeOn_of_public, Johnson/Goal/Conditions/CompleteOfPublic.lean)
is general in the argument system. A first text that called it at a member, with the form read as
FormBytes and descriptionOfDataOnBytes open, ran into Lean's limit (whnf). So the call is made at letters, and the
member's fields are laid in by these equations.

Main names.
  sample_theWider, prove_theWider   a member's sampler and honest prover are K's.
  sample_record, prove_record, commit_record, verify_record   THE FOUR FIELDS OF THE GOALS' SYSTEM
    AT A MEMBER, systemOfRecord (atSecondHashFunction (theWider K W)) Z s: K's sampler, K's prover, the member's
    committer, verify() at descriptionOfDataOnBytes flashProveData.

Limits. Equations alone. No completeness. WiderAtThe.lean's limits travel whole.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WiderAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference Rom

/- Lean compares these names and does not unfold them. (descriptionOfDataOnBytes is left open here: that its form
is FormBytes is read off its text.) -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

/-- The sampler of a member is K's. -/
theorem sample_theWider (K : TheCoins) (W : WiderCoins K) (o : SecondHashFunctionType) :
    (theWider K W o).sample = K.sample := rfl

/-- The honest prover of a member is K's. -/
theorem prove_theWider (K : TheCoins) (W : WiderCoins K) (o : SecondHashFunctionType) :
    (theWider K W o).prove = K.prove := rfl

/-- The goals' system at a member: its sampler is K's. -/
theorem sample_record (K : TheCoins) (W : WiderCoins K) (Z : PublicFiles)
    (s : IntegerTransformer.Settings) :
    (systemOfRecord (atSecondHashFunction (theWider K W)) Z s).sampleCommitmentRandomness = K.sample := rfl

/-- Its honest prover is K's. -/
theorem prove_record (K : TheCoins) (W : WiderCoins K) (Z : PublicFiles)
    (s : IntegerTransformer.Settings) :
    (systemOfRecord (atSecondHashFunction (theWider K W)) Z s).prove = K.prove Z s := rfl

/-- Its committer is the member's. -/
theorem commit_record (K : TheCoins) (W : WiderCoins K) (Z : PublicFiles)
    (s : IntegerTransformer.Settings) :
    (systemOfRecord (atSecondHashFunction (theWider K W)) Z s).commit =
      (theWider K W OnBytes.secondHashFunction).commit Z s := rfl

section
/- From here on Lean compares the description by its name. -/
attribute [local irreducible] descriptionOfDataOnBytes

/-- **Its verifier is verify() at `descriptionOfDataOnBytes flashProveData` and that description's own parser.** -/
theorem verify_record (K : TheCoins) (W : WiderCoins K) (Z : PublicFiles)
    (s : IntegerTransformer.Settings) :
    (systemOfRecord (atSecondHashFunction (theWider K W)) Z s).verify = verify flashProveDescription Z (flashProveDescription.parse Z) :=
  verify_theWider K W OnBytes.secondHashFunction Z (flashProveDescription.parse Z)

end

end FlashProve

#print axioms FlashProve.sample_theWider
#print axioms FlashProve.prove_theWider
#print axioms FlashProve.sample_record
#print axioms FlashProve.prove_record
#print axioms FlashProve.commit_record
#print axioms FlashProve.verify_record
