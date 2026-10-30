-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/AcceptGivesLive.lean: where the goals' verifier at `VerifierAndGoals.theDescription`
accepts, the public files are in scope and `protocolDataWellFormed` accepts.
`scope_of_accept`: general in the description: an accept, at any parser argument and any hash
function, gives `InScope Z = true`: the contrapositive of `verify_evaluate_out`
(Goal/Tie/VerifyEval.lean).
`liveAt_of_accept`: at every function o in the second hash function's place: an accept gives
`protocolDataWellFormedAt o (asDescriptionFiles Z) = true`: the contrapositive of `theDescription_dead_all` (DeadParser.lean).
`live_of_accept`: the same where the goals read the description: `protocolDataWellFormed (asDescriptionFiles Z) = true`.
`scope_and_live_of_accept`: both.
So a run whose verdict is that verifier's value (by a tie) and is "accept" shows both tests' yes at
its public files, as far as the run is trusted.
Limits. One direction. Nothing on whether any input is accepted. Nothing on soundness.

-/
import Johnson.Goal.Description.DeadParser

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **An accept gives the scope**: at every description, parser argument and hash function. -/
theorem scope_of_accept (D : Description) (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form)
    (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token)
    (form : Form)
    (h : (VerifierAndGoals.verify D Z parse commitment prompt output form).evaluate hash = true) :
    InScope Z = true := by
  cases scope : InScope Z with
  | true => rfl
  | false =>
    rw [verify_evaluate_out D Z parse scope hash commitment prompt output form] at h
    exact absurd h Bool.false_ne_true

/-- **An accept gives the live test's yes**: at every o, parser argument and hash function. -/
theorem liveAt_of_accept (o : SecondHashFunctionType) (Z : PublicFiles) {Form : Type}
    (parse : Parser (theDescription o) Z Form) (hash : VerifiableInference.Hash)
    (commitment : Commitment) (prompt output : List Token) (form : Form)
    (h : (VerifierAndGoals.verify (theDescription o) Z parse commitment prompt output form).evaluate hash =
      true) :
    protocolDataWellFormedAt o (asDescriptionFiles Z) = true := by
  cases live : protocolDataWellFormedAt o (asDescriptionFiles Z) with
  | true => rfl
  | false =>
    rw [theDescription_dead_all o Z live parse hash commitment prompt output form] at h
    exact absurd h Bool.false_ne_true

/-- **Where the goals read the description.** -/
theorem live_of_accept (Z : PublicFiles) {Form : Type} (parse : Parser (atSecondHashFunction theDescription) Z Form)
    (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token)
    (form : Form)
    (h : (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z parse commitment prompt output form).evaluate
      hash = true) :
    protocolDataWellFormed (asDescriptionFiles Z) = true :=
  liveAt_of_accept OnBytes.secondHashFunction Z parse hash commitment prompt output form h

/-- Both. -/
theorem scope_and_live_of_accept (Z : PublicFiles) {Form : Type}
    (parse : Parser (atSecondHashFunction theDescription) Z Form) (hash : VerifiableInference.Hash)
    (commitment : Commitment) (prompt output : List Token) (form : Form)
    (h : (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z parse commitment prompt output form).evaluate
      hash = true) :
    InScope Z = true ∧ protocolDataWellFormed (asDescriptionFiles Z) = true :=
  ⟨scope_of_accept _ Z parse hash commitment prompt output form h,
    live_of_accept Z parse hash commitment prompt output form h⟩

end FlashProve

#print axioms FlashProve.scope_of_accept
#print axioms FlashProve.liveAt_of_accept
#print axioms FlashProve.live_of_accept
#print axioms FlashProve.scope_and_live_of_accept
