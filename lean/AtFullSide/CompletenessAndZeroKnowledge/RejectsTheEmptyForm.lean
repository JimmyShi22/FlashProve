-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/RejectsTheEmptyForm.lean: the compiled verifier rejects the empty form, under every
hash function.

  verify_rejects_noProofForm
      the verifier of the goals, at the description flashProveDescription, rejects noProofForm at every commitment,
      prompt and output, at all public files, in scope or not
  rejectsNoProof_flashProve
      the same of compile (flashProveAtFiles …), at every honest part, at all public files, in scope or
      not, and at all settings
  rejectsNoProof_value
      the same of the final system at honestProversAndSettings, at all public files, in scope or not, and at
      all settings

From what. Inside the scope: verify_refuses_empty (Johnson/Face/EmptyProof.lean), whose two
conditions on sizes hold at every function with 32-byte answers (size_cThru, size_sevenThru), and
every hash function is hashOf of such a function (forall_hashOf32). Outside the scope the verifier
says no at once. compile_flashProve_verify_eq carries this to the compiled verifier.

Limits. This says nothing on whether the form of a served request is non-empty, and an empty form
does not show that the request was refused: a prover can return it at a request that it could serve.
It is a statement about the verifier as defined in Lean, not about a program that runs.
-/
import Johnson.Face.EmptyProof
import Johnson.Goal.Tie.HashOfEvery
import Johnson.Goal.Tie.TieSteps
import VerifiableInference.Final.RefuseUnserved
import AtFullSide.Face.HonestProversAndSettingsValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve

/-- **The verifier of the goals rejects the empty form, under every hash function**, at all public
files, in scope or not. -/
theorem verify_rejects_noProofForm (files : PublicFiles) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) :
    (VerifierAndGoals.verify flashProveDescription files (flashProveDescription.parse files) commitment prompt output noProofForm).evaluate hash =
        false := by
  by_cases scope : InScope files = true
  · refine (VerifiableInference.OnPublicFiles.forall_hashOf32 (fun hash =>
            (VerifierAndGoals.verify flashProveDescription files (flashProveDescription.parse files) commitment prompt output noProofForm).evaluate hash =
                false)).1
      ?_ hash
    intro O sizes
    exact FlashProve.verify_refuses_empty flashProveData files scope O (size_cThru O sizes _)
        (size_sevenThru O sizes _ _ _)
      commitment prompt output noProofForm rfl
  · have refused : VerifierAndGoals.verify flashProveDescription files (flashProveDescription.parse files) commitment prompt output noProofForm =
      .done false := by
      unfold VerifierAndGoals.verify VerifierAndGoals.verifyAt
      exact if_neg scope
    exact (congrArg (fun check => check.evaluate hash) refused).trans rfl

/-- **The compiled verifier rejects the empty form, under every hash function, at every honest
part**, at all public files, in scope or not, and at all settings. -/
theorem rejectsNoProof_flashProve (files : PublicFiles) (settings : IntegerTransformer.Settings)
    (honest : HonestProversAndSettingsAtFiles files settings) :
    Compilable.RejectsNoProof (flashProveAtFiles files settings honest) noProofForm := by
  intro hash commitment prompt output
  have same := congrFun (congrFun (congrFun (congrFun
    (compile_flashProve_verify_eq files settings honest) commitment) prompt) output) noProofForm
  exact (congrArg (fun check => check.evaluate hash) same).trans
    (verify_rejects_noProofForm files hash commitment prompt output)

/-- **The same of the final system at the honest part**, at all public files, in scope or not, and
at all settings. -/
theorem rejectsNoProof_value (files : PublicFiles) (settings : IntegerTransformer.Settings) (hash : Hash)
    (commitment : Commitment)
    (prompt output : List Token) :
    ((finalSystem honestProversAndSettings files settings).verify commitment prompt output
        noProofForm).evaluate hash = false :=
  rejectsNoProof_flashProve files settings (honestProversAndSettings files settings) hash commitment prompt
      output

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.verify_rejects_noProofForm
#print axioms VerifiableInference.Compilation.rejectsNoProof_flashProve
#print axioms VerifiableInference.Compilation.rejectsNoProof_value
