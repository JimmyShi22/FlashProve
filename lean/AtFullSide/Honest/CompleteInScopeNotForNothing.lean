-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/CompleteInScopeNotForNothing.lean

This file shows that complete_in_scope (CompleteAtTheFiles.lean of this folder) does not hold
vacuously: in scope some request is served, at an index in range. It also shows that at every served
input some list of challenges of the declared form triggers none of the honest online prover's
stopping rules. The header of CompleteAtTheFiles.lean explains the terms.

Main statements.
  * someRequestIsServed_in_scope. Premises: InScope Z = true and readFiles Z = .ok pp. Conclusion:
    there are an index i with rangeAtFiles i and an instance x with ServedRequest committerCoinCountLessOne Z hr i
    x. This is the proposition of the field someRequestIsServed in
    VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean.
  * complete_in_scope_with_a_served_request. Premises: InScope Z = true, protocolDataWellFormed (asDescriptionFiles Z) = true
    and readFiles Z = .ok pp. Conclusion: that proposition, together with the conclusion of
    complete_in_scope.
  * aDueListWithNoStop_in_scope. Premises: the same three. Conclusion: there are a return A of the
    base construction and an h : HeadAtReturn Z A such that every served input (ServedInput,
    E2E/TheHonestProverStatements.lean) has a list of challenges with StandsAtServed
    (E2E/TheHonestProverNotTaken.lean). StandsAtServed has three clauses: the input is served; the
    list has the form that the description declares (Draws.due); and silentAt returns none, which
    means that no stopping rule of the honest prover fires. The prover here is that of onlineReturn
    Z A, which is A with its randomness supplied by the table's coins.

Limits.
  * This file adds nothing on completeness beyond what complete_in_scope says, and all limits of
    that theorem hold here: the level of the interactive oracle proof, the honest provers as they
    are defined in Lean, served requests alone.
  * "Some request is served" is shown at made-up weights (Meaning.served_met: weights under which
    the model answers 1 after any one token, with the prompt [0] and the output [1]). It says
    nothing of a real model's weights.
  * The statements are existence statements: nothing computes the request.
  * The list of challenges in aDueListWithNoStop_in_scope is obtained by a counting argument, and
    nothing computes it. That the run succeeds at that list is not said there.
  * silentAt also returns none where the prover has no trace for the request. The third theorem does
    not say that a trace exists.
  * The statements hold for the full-size layout and for the format's second hash function,
    OnBytes.secondHashFunction, alone.
  * The proofs in this file only combine theorems of other files.
  * Nothing on soundness or on what a proof hides.

Built on.
  * someRequestIsServed_holds (VerifiableInference/Final/ZeroKnowledgeAtTheProtocolLaws.lean), which
    calls servedRequest_met (E2E/CompleteAsIOPServedLaws.lean).
  * complete_in_scope (CompleteAtTheFiles.lean) and aDueListWithNoStopAtEveryServedInput
    (StandsAtServedHasAMember.lean), both in this folder.
  * baseMaker_returns and headAtReturn_baseMaker (AtFullSide/K1/HeadAtBaseMaker.lean).
-/
import AtFullSide.Honest.CompleteAtTheFiles
import AtFullSide.Honest.StandsAtServedHasAMember
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtFullSide.Honest
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open OnBytes.Slice (frS)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open ProofFile.Honest (OnlineProverWithDescription IndexCommitterCoins Cells onlineProverFromPublicFiles)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixFilling)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles settingsOfRead)
open FlashProve (committerCoinCountLessOne protocolDataWellFormed)
open OnBytes.Prover (CompleteAtEveryCoin)
open VerifiableInference.Compilation (theProvers rangeAtFiles someRequestIsServed_holds)

local instance (priority := high) nonemptyPadZ_notForNothing : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_notForNothing : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_notForNothing : Inhabited RunValue :=
  ⟨fun _ => 0⟩

variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- In scope some request is served, at an index in range. The request is one at made-up weights:
nothing is said of a real model's weights. -/
theorem someRequestIsServed_in_scope (scope : InScope Z = true) (hr : readFiles Z = .ok pp) :
    ∃ i x, rangeAtFiles i ∧ ServedRequest committerCoinCountLessOne Z hr i x :=
  someRequestIsServed_holds Z scope hr

/-- The conclusion of complete_in_scope, and beside it that the relation ServedRequest, on which
that conclusion speaks, has a member. -/
theorem complete_in_scope_with_a_served_request (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hr : readFiles Z = .ok pp) :
    (∃ i x, rangeAtFiles i ∧ ServedRequest committerCoinCountLessOne Z hr i x) ∧
    (CompleteAtFiles Z (thePartsAt Z) hr ∧
      ∃ a c : ℝ≥0∞, a + 0 + c ≤ completenessTarget ∧
        CompleteAtEveryCoin (protocolAtFiles Z) (theProvers Z (settingsOfRead pp) (thePartsAt Z)) (workAtFiles Z)
          (ServedRequest committerCoinCountLessOne Z hr) a 0 c) :=
  ⟨someRequestIsServed_in_scope scope hr, complete_in_scope scope live hr⟩

/-- In scope, where the verifier's test on the public files accepts: at every served input some list
of challenges of the declared form triggers no stopping rule. The prover is that of onlineReturn Z
A, at the places and the first chain of h. -/
theorem aDueListWithNoStop_in_scope (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hr : readFiles Z = .ok pp) :
    ∃ (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (h : HeadAtReturn Z A),
      onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A ∧
      ∀ matrix coins input, ServedInput (ServedRequest committerCoinCountLessOne Z hr) Z matrix coins input →
        ∃ challenges, StandsAtServed (ServedRequest committerCoinCountLessOne Z hr) (onlineReturn Z A) h.places
          h.firstChain matrix coins input challenges := by
  obtain ⟨A, made⟩ := ProofFile.Honest.K1.baseMaker_returns Z scope live
  obtain ⟨h, -⟩ := ProofFile.Honest.K1.headAtReturn_baseMaker Z scope live made
  exact ⟨A, h, made, fun matrix coins input served =>
    aDueListWithNoStopAtEveryServedInput (h := h) made live matrix coins input served⟩

end AtFullSide.Honest

#check @AtFullSide.Honest.someRequestIsServed_in_scope
#check @AtFullSide.Honest.complete_in_scope_with_a_served_request
#check @AtFullSide.Honest.aDueListWithNoStop_in_scope
#print axioms AtFullSide.Honest.someRequestIsServed_in_scope
#print axioms AtFullSide.Honest.complete_in_scope_with_a_served_request
#print axioms AtFullSide.Honest.aDueListWithNoStop_in_scope
