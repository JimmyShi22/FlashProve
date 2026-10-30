-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/ExecutableVerifierIsLeanVerifier.lean: the executable verifier equals leanVerifier.

 1. executableVerifier is a computable function. It maps the public files, the commitment, the
    prompt, the output tokens and the parsed proof to a decision.
 2. executableVerifier_eq_leanVerifier: at the files of a public setup, executableVerifier returns
    the decision of leanVerifier.
 3. PV.Program.verdictOf (Johnson/PVR/Program.lean) maps the bytes of eleven files to a decision.
    The command lean-verify calls its parts. It reads the claim from the user's files and applies
    executableVerifier to it. If the claim can be read and the three public files are those of a
    public setup, then it returns the decision of leanVerifier.
 4. executableVerifier_eq_leanVerifier_stored is the equality at the stored public files.

Remarks.
 * executableVerifier is defined for all public files. It tests that they are in the verifier's
   scope, can be read and are well formed. It does not test that they state the exact-match policy.
   leanVerifier is defined only for a public setup.
 * The parsed proof consists of five parsed files and the request's tokens after the checked
   positions. The parser that produces the five files is outside Lean.
 * The run of the command and compiled code are not covered by any theorem.
-/
import AtFullSide.Face.TheSixLines
import Johnson.Face.ExecutableVerifier
import Johnson.PVR.ProgramTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference
open VerifierAndGoals VerifiableInference.Compilation

/-- The executable verifier, with BLAKE2b as the hash function. Its last argument is the parsed
proof: five files that a parser outside Lean produces, and the request's tokens after the checked
positions. It returns a decision or nothing. -/
def executableVerifier (files : PublicFiles) (commitment : Commitment) (prompt output : List Token)
    (proof : FlashProve.FormBytes) : Option Bool :=
  PV.Ride.verdictThe files _root_.Fmt.oracle proof
    (PV.Ride.rideThe files _root_.Fmt.oracle proof commitment prompt output)

/-- **The executable verifier equals the Lean verifier.** For every public setup, commitment,
prompt, output and parsed proof, the executable verifier returns the decision of leanVerifier. -/
theorem executableVerifier_eq_leanVerifier (setup : PublicSetup) (commitment : Commitment)
    (prompt output : List Token) (proof : FlashProve.FormBytes) :
    executableVerifier setup.files commitment prompt output proof =
      some (leanVerifier setup commitment prompt output proof) := by
  rw [leanVerifier_eq]
  unfold executableVerifier finalVerifierProgram
  rw [finalVerifier_eq]
  exact (PV.Ride.verdictThe_eq setup.files _root_.Fmt.oracle _root_.Fmt.size_oracle proof commitment
    prompt output).trans (congrArg some (evaluate_verify_of_eq theDescription_eq rfl rfl setup.files
      proof commitment prompt output blake2bHash))

/-- PV.Program.verdictOf reads the claim from the user's files and applies the executable verifier
to the claim and the parsed proof. -/
theorem verdictOf_eq_executableVerifier (given : PV.Program.Given) :
    PV.Program.verdictOf given =
      (PV.Program.claimOf given).bind fun claim =>
        executableVerifier (PV.Program.pubOf given) claim.commitment claim.prompt claim.output
          (PV.Program.formOf given claim) := rfl

/-- Suppose that the three public files among the given files are those of a public setup, and that
the claim can be read from the user's files. Then PV.Program.verdictOf returns the decision of
leanVerifier on that claim and the parsed proof. -/
theorem verdictOf_eq_leanVerifier (setup : PublicSetup) (given : PV.Program.Given)
    (claim : PV.Program.Claim) (sameFiles : PV.Program.pubOf given = setup.files)
    (reads : PV.Program.claimOf given = some claim) :
    PV.Program.verdictOf given =
      some (leanVerifier setup claim.commitment claim.prompt claim.output
        (PV.Program.formOf given claim)) := by
  rw [verdictOf_eq_finalVerifierProgram given claim reads (settingsOfRead setup.readParameters),
    sameFiles, leanVerifier_eq]

/-- At the stored public files, the executable verifier returns the decision of leanVerifier. -/
theorem executableVerifier_eq_leanVerifier_stored (commitment : Commitment)
    (prompt output : List Token) (proof : FlashProve.FormBytes) :
    executableVerifier storedPublicFiles commitment prompt output proof =
      some (leanVerifier storedSetup commitment prompt output proof) :=
  executableVerifier_eq_leanVerifier storedSetup commitment prompt output proof

end VerifiableInference

#print axioms VerifiableInference.executableVerifier
#print axioms VerifiableInference.executableVerifier_eq_leanVerifier
#print axioms VerifiableInference.verdictOf_eq_executableVerifier
#print axioms VerifiableInference.verdictOf_eq_leanVerifier
#print axioms VerifiableInference.executableVerifier_eq_leanVerifier_stored
