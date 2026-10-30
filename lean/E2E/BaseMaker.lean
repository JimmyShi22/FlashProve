-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/BaseMaker.lean: the filling that onlineFilling (E2E/TheHonestProver.lean) reads through, and the
maker at it: one term for every statement at the filling's prover.

  baseFilling          the kinds' sides, the closings, the proximity tests' and the message W's, at the
                       matrices, at the stored randomness IndexCommitterCoins
  baseMaker            the maker at it and the three public files
  onlineFilling_eq     onlineFilling is baseFilling read through

Limits. Definitions and one rfl. That the maker returns is not said here.
-/
import E2E.TheHonestProver

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles

/-- **The filling at the matrices, which onlineFilling reads through.** The argument does not enter:
it is there so that a statement reads alike at baseFilling files and at onlineFilling files. -/
abbrev baseFilling (_files : VerifierAndGoals.PublicFiles) : OnlineProverParts FullSizeMatrix IndexCommitterCoins Cells Unit Unit :=
  onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- **The maker at that filling and the three public files.** -/
abbrev baseMaker (files : VerifierAndGoals.PublicFiles) : Except String (OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) :=
  onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (baseFilling files)

/-- onlineFilling is baseFilling read through. -/
theorem onlineFilling_eq (files : VerifierAndGoals.PublicFiles) :
    onlineFilling files = OnlineProverParts.through id (tableCoins files) matrixInput.dummy (baseFilling files) :=
  rfl

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.baseFilling
#print axioms ProofFile.Honest.Term.baseMaker
#print axioms ProofFile.Honest.Term.onlineFilling_eq
