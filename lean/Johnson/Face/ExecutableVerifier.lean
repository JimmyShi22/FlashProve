-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/ExecutableVerifier.lean: the verifier at BLAKE2b, and what lean-verify computes.

 1. The command lean-verify calls claimOf, stepsOf and verdictAt; PV.Program.verdictOf ties them into
    one verdict (verdictOf_at), made by a text of its own.
 2. Where its claim reads, that verdict is finalVerifierProgram at that claim: two texts, one answer.
 3. The verifier tests no policy: an accept at another policy than exact match is outside FinalSound.
 4. The five parsed files come from a parser outside Lean, and no theorem says that the claim is cut
    as the format says.
 5. No theorem speaks of the command's run, or of compiled or interpreted code.
-/
import Johnson.Face.FinalStatement
import Johnson.PVR.ProgramTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open IntegerTransformer (Settings)

/-- One description at two names gives one decision, on a proof in bytes. -/
theorem evaluate_verify_of_eq {D D' : Description} (same : D = D')
    (form : D.Form = FlashProve.FormBytes) (form' : D'.Form = FlashProve.FormBytes) (Z : PublicFiles)
    (bytes : FlashProve.FormBytes) (commitment : Commitment) (prompt output : List Token)
    (hash : Hash) :
    (verify D Z (D.parse Z) commitment prompt output (cast form.symm bytes)).evaluate hash =
      (verify D' Z (D'.parse Z) commitment prompt output (cast form'.symm bytes)).evaluate hash := by
  subst same
  rfl

/-- **The verdict of the function that lean-verify evaluates is finalVerifierProgram**, where the claim
reads, at every settings. -/
theorem verdictOf_eq_finalVerifierProgram (g : PV.Program.Given) (c : PV.Program.Claim)
    (reads : PV.Program.claimOf g = some c) (settings : Settings) :
    PV.Program.verdictOf g =
      some (finalVerifierProgram (PV.Program.pubOf g) settings c.commitment c.prompt c.output
        (PV.Program.formOf g c)) := by
  rw [PV.Program.verdictOf_eq g c reads]
  unfold finalVerifierProgram PV.Program.verifyValue
  rw [finalVerifier_eq]
  exact congrArg some (evaluate_verify_of_eq theDescription_eq rfl rfl (PV.Program.pubOf g)
    (PV.Program.formOf g c) c.commitment c.prompt c.output blake2bHash)

/-- The final system's verifier at BLAKE2b is finalVerifierProgram. -/
theorem finalSystem_verifier_at_blake2b (honest : HonestProversAndSettings) (files : PublicFiles) (settings : Settings)
    (commitment : Commitment) (prompt output : List Token) (form : flashProveDescription.Form) :
    ((finalSystem honest files settings).verify commitment prompt output form).evaluate
        blake2bHash =
      finalVerifierProgram files settings commitment prompt output form := by
  unfold finalVerifierProgram
  rw [compile_flashProve_verify]

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalSystem_verifier_at_blake2b
#print axioms VerifiableInference.Compilation.verdictOf_eq_finalVerifierProgram
