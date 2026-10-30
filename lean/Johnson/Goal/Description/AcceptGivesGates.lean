-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/AcceptGivesGates.lean: where the goals' verifier at `VerifierAndGoals.theDescription`
accepts, each of its three decisions accepts somewhere.
`verifyBy_never_proof_all`, `verifyBy_never_key_all`: at every structure of letters L and every
further public reading: where L's decision on the proof file (on the key file) never accepts,
`VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z parse …` rejects: at every parser argument, form and hash
function. The fellow for the copy's file is `verifyBy_never_all` (DeadParser.lean).
`proofGateAt_of_accept`, `keyGateAt_of_accept`, `linkGateAt_of_accept`: by contraposition, at every
function o in the second hash function's place: an accept gives an instance and views at which the
gate accepts.
`gates_of_accept`: the three where the goals read the description.
`runs_of_accept`: and, since an accept gives `protocolDataWellFormed`'s yes (AcceptGivesLive.lean), the same of the
three seated decisions themselves: `theKeyRun`, `linkDecisionAtFiles`, `theProofRun`.
So whatever follows from "the proof file's decision accepts at some instance and views" follows, by
a theorem, from ONE Bool: the verifier's accept.
Limits. "There are": by contradiction: no instance and no views are named: they need not be those
that a run's fast form hands the decision. One direction. Nothing on soundness.

-/
import Johnson.Goal.Tie.NeverWhole
import Johnson.Goal.Description.AcceptGivesLive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat

/-- **Reject, at every parser argument, form and hash function**, where the proof file's decision
never accepts. -/
theorem verifyBy_never_proof_all
    (more : PublicFiles → Digest → DeterministicAlgorithm (List (_root_.Iop.Dig 256))) (L : DescriptionData) (Z : PublicFiles)
    (never : ∀ x v₁ v₂ v₃, L.runP (asDescriptionFiles Z) x v₁ v₂ v₃ = false) {Form : Type}
    (parse : Parser (descriptionOfDataWithReading more L) Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z parse commitment prompt output form).evaluate hash =
      false := by
  cases scope : VerifierAndGoals.InScope Z with
  | false => exact verify_evaluate_out _ Z parse scope hash commitment prompt output form
  | true =>
    rw [verify_evaluate _ Z parse scope hash]
    exact innerCompiledVerifierAtFullSize_never_proof never ((dataAtFiles L Z).inputFieldsAtReadings _ _) hash commitment prompt output _

/-- The same where the key file's decision never accepts. -/
theorem verifyBy_never_key_all
    (more : PublicFiles → Digest → DeterministicAlgorithm (List (_root_.Iop.Dig 256))) (L : DescriptionData) (Z : PublicFiles)
    (never : ∀ r v₁ v₂ v₃, L.runK (asDescriptionFiles Z) r v₁ v₂ v₃ = false) {Form : Type}
    (parse : Parser (descriptionOfDataWithReading more L) Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z parse commitment prompt output form).evaluate hash =
      false := by
  cases scope : VerifierAndGoals.InScope Z with
  | false => exact verify_evaluate_out _ Z parse scope hash commitment prompt output form
  | true =>
    rw [verify_evaluate _ Z parse scope hash]
    exact innerCompiledVerifierAtFullSize_never_key never ((dataAtFiles L Z).inputFieldsAtReadings _ _) hash commitment prompt output _

end FlashProve

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat

section
variable (o : SecondHashFunctionType) (Z : PublicFiles) {Form : Type} (parse : Parser (theDescription o) Z Form)
  (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token)
  (form : Form)
  (h : (VerifierAndGoals.verify (theDescription o) Z parse commitment prompt output form).evaluate hash =
    true)
include h

/-- **An accept gives an instance and views at which the proof file's gate accepts.** -/
theorem proofGateAt_of_accept : ∃ z v₁ v₂ v₃, theProofGateAt o (asDescriptionFiles Z) z v₁ v₂ v₃ = true := by
  by_contra hn
  have never : ∀ x v₁ v₂ v₃, (flashProveDataAtSecondHash o).runP (asDescriptionFiles Z) x v₁ v₂ v₃ = false :=
    fun x v₁ v₂ v₃ => Bool.eq_false_iff.2 fun e => hn ⟨x, v₁, v₂, v₃, e⟩
  have e := verifyBy_never_proof_all _ (flashProveDataAtSecondHash o) Z never parse hash commitment prompt output
    form
  exact Bool.false_ne_true (e.symm.trans h)

/-- The key file's gate. -/
theorem keyGateAt_of_accept : ∃ r v₁ v₂ v₃, theKeyGateAt o (asDescriptionFiles Z) r v₁ v₂ v₃ = true := by
  by_contra hn
  have never : ∀ r v₁ v₂ v₃, (flashProveDataAtSecondHash o).runK (asDescriptionFiles Z) r v₁ v₂ v₃ = false :=
    fun r v₁ v₂ v₃ => Bool.eq_false_iff.2 fun e => hn ⟨r, v₁, v₂, v₃, e⟩
  have e := verifyBy_never_key_all _ (flashProveDataAtSecondHash o) Z never parse hash commitment prompt output form
  exact Bool.false_ne_true (e.symm.trans h)

/-- The copy's file's gate. -/
theorem linkGateAt_of_accept : ∃ rr v, theLinkGateAt o (asDescriptionFiles Z) rr v = true := by
  by_contra hn
  have never : ∀ rr v, (flashProveDataAtSecondHash o).dec (asDescriptionFiles Z) rr v = false :=
    fun rr v => Bool.eq_false_iff.2 fun e => hn ⟨rr, v, e⟩
  have e := verifyBy_never_all _ (flashProveDataAtSecondHash o) Z never parse hash commitment prompt output form
  exact Bool.false_ne_true (e.symm.trans h)

end

section
variable (Z : PublicFiles) {Form : Type} (parse : Parser (atSecondHashFunction theDescription) Z Form)
  (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token)
  (form : Form)
  (h : (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z parse commitment prompt output form).evaluate
    hash = true)
include h

/-- **The three gates, where the goals read the description.** -/
theorem gates_of_accept :
    (∃ r v₁ v₂ v₃, theKeyGate (asDescriptionFiles Z) r v₁ v₂ v₃ = true) ∧
      (∃ rr v, theLinkGate (asDescriptionFiles Z) rr v = true) ∧
      ∃ z v₁ v₂ v₃, theProofGate (asDescriptionFiles Z) z v₁ v₂ v₃ = true :=
  ⟨keyGateAt_of_accept OnBytes.secondHashFunction Z parse hash commitment prompt output form h,
    linkGateAt_of_accept OnBytes.secondHashFunction Z parse hash commitment prompt output form h,
    proofGateAt_of_accept OnBytes.secondHashFunction Z parse hash commitment prompt output form h⟩

/-- **The three seated decisions themselves.** -/
theorem runs_of_accept :
    (∃ r v₁ v₂ v₃, theKeyRun (asDescriptionFiles Z) r v₁ v₂ v₃ = true) ∧
      (∃ rr v, linkDecisionAtFiles (asDescriptionFiles Z) rr v = true) ∧
      ∃ z v₁ v₂ v₃, theProofRun (asDescriptionFiles Z) z v₁ v₂ v₃ = true := by
  have live := live_of_accept Z parse hash commitment prompt output form h
  have g := gates_of_accept Z parse hash commitment prompt output form h
  rw [theKeyGate_live _ live, theLinkGate_live _ live, theProofGate_live _ live] at g
  exact g

end

end FlashProve

#print axioms FlashProve.verifyBy_never_proof_all
#print axioms FlashProve.verifyBy_never_key_all
#print axioms FlashProve.proofGateAt_of_accept
#print axioms FlashProve.keyGateAt_of_accept
#print axioms FlashProve.linkGateAt_of_accept
#print axioms FlashProve.gates_of_accept
#print axioms FlashProve.runs_of_accept
