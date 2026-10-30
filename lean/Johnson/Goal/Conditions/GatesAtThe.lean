-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/GatesAtThe.lean: at the closed term `VerifierAndGoals.theDescription`: what the three
decisions of `dataAtFiles flashProveData Z` are: each is the gate `protocolDataWellFormed (asDescriptionFiles Z)` in front of the named
decision at `asDescriptionFiles Z`; and the same with the named decision replaced by any value that it equals
at that one Z. Theorems.

Why. Whoever states a file's hypothesis on soundness at a description's own run states it at a
decision `gatedFileDecision b run` or `gatedLinkDecision b dec`, with b a letter. These three lemmas say what b and the
decision are at the name, so that the last call there is one rewriting. The equation on the value is
asked at one Z, so it can be shown at the files in scope alone.

Main names. `runK_the_at`, `dec_the_at`, `runP_the_at`. Each goes by the lemma that is general in
the record (`runK_built`, `dec_built`, `runP_built`, Johnson/Goal/Conditions/NumbersAtThe.lean), so
that Lean does not unfold `dataAtFiles` at `flashProveData`.

Limits. Three equations by definition. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.NumbersAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals FlashProve VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open _root_.Run
open LPFD.Full (XF)

/-- The key file's slot. -/
theorem runK_the_at (Z : PublicFiles) (r : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (hv : theKeyRun (asDescriptionFiles Z) = r) : (dataAtFiles flashProveData Z).runK = gatedFileDecision (protocolDataWellFormed (asDescriptionFiles Z)) r := by
  rw [← hv]
  exact (runK_built flashProveData Z).trans rfl

/-- The entry file's slot. -/
theorem dec_the_at (Z : PublicFiles) (d : RecFull × RecFull → PQ.View → Bool)
    (hv : linkDecisionAtFiles (asDescriptionFiles Z) = d) : (dataAtFiles flashProveData Z).dec = gatedLinkDecision (protocolDataWellFormed (asDescriptionFiles Z)) d := by
  rw [← hv]
  exact (dec_built flashProveData Z).trans rfl

/-- The proof file's slot. -/
theorem runP_the_at (Z : PublicFiles) (r : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (hv : theProofRun (asDescriptionFiles Z) = r) :
    (dataAtFiles flashProveData Z).runP = gatedFileDecision (protocolDataWellFormed (asDescriptionFiles Z)) r := by
  rw [← hv]
  exact (runP_built flashProveData Z).trans rfl

end FlashProve

#print axioms FlashProve.runK_the_at
#print axioms FlashProve.dec_the_at
#print axioms FlashProve.runP_the_at
