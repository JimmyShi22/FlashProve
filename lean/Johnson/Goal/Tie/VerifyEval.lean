-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/VerifyEval.lean: the goals' `VerifierAndGoals.verify` at a hash function, general in the
description.
`cAt`, `mAt`, `proofAt`: what the first public reading, the further public reading and a parser
return at a hash function. `verify_evaluate`: at files in the goals' scope, the value of
`VerifierAndGoals.verify D Z parse commitment prompt output form` at a hash function is the value of
`innerCompiledVerifier` at `D.input Z` of the two readings, at the typed proof that the parser returns; `InScope
Z = true` is its one hypothesis. `verify_evaluate_out`: at files out of scope it is false.

-/
import Ladder.ReadThru

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat

/-- What the first public reading returns at a hash function. -/
def cAt (Z : PublicFiles) (hash : VerifiableInference.Hash) : Digest := (readConfig Z).evaluate hash

/-- What the further public reading returns. -/
def mAt (D : Description) (Z : PublicFiles) (hash : VerifiableInference.Hash) : D.More :=
  (D.readMore Z (cAt Z hash)).evaluate hash

/-- What a parser returns. -/
def proofAt {D : Description} {Z : PublicFiles} {Form : Type} (parse : Parser D Z Form) (prompt output :
            List Token)
    (form : Form) (hash : VerifiableInference.Hash) : TypedProof (D.F Z) (D.P Z) :=
  (parse prompt output form).evaluate hash

/-- **THE GOALS' verify AT A HASH FUNCTION, AT FILES IN SCOPE.** -/
theorem verify_evaluate (D : Description) (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form)
    (scope : VerifierAndGoals.InScope Z = true) (hash : VerifiableInference.Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify D Z parse commitment prompt output form).evaluate hash =
      (innerCompiledVerifier (D.input Z (cAt Z hash) (mAt D Z hash)) commitment prompt output
        (proofAt parse prompt output form hash)).evaluate hash := by
  unfold verify verifyAt
  rw [if_pos scope, evaluate_andThen, evaluate_andThen, evaluate_andThen]
  rfl

/-- At files out of scope it refuses. -/
theorem verify_evaluate_out (D : Description) (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form)
    (scope : VerifierAndGoals.InScope Z = false) (hash : VerifiableInference.Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify D Z parse commitment prompt output form).evaluate hash = false := by
  unfold verify verifyAt
  rw [if_neg (by rw [scope]; exact Bool.false_ne_true)]
  rfl

end FlashProve
