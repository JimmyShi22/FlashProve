-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/DeadParser.lean: where the test on the public files says no, the verifier
says no AT EVERY PARSER, every form and every hash function, at every function o in the second
hash function's place.
`verifyBy_never_all`: at every record of letters L and every further public reading: where L's
entry decision never says yes, `VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z parse …` evaluates to no. No
premise on the scope: out of scope the verifier refuses by its own text. By `verify_evaluate`
(Johnson/Goal/Tie/VerifyEval.lean: the value at every parser) and `innerCompiledVerifierAtFullSize_never`
(Johnson/Goal/Tie/NeverEvery.lean: no at every typed proof).
`theDescriptionO_dead_all`: at every o: where `protocolDataWellFormedAt o` says no.
`theDescriptionO_no_of_plan_all`, `…_key_all`, `…_proof_all`: where a seat refuses at o.
`theDescription_dead_all`: the same under the name `theDescription`, which is that function.
`proof_written_or_no_all`: at `atSecondHashFunction theDescription`, in scope: no to all, or the data of the
proof file's seat, and the letter DP that the verifier reads, are the written data.
Why. The goals range over every parser and draw a hash function on bit strings; Dead.lean's laws
stand at the description's own parser and at `hashOf O`.
At which o: in scope `publicOfO o` returns only at an o whose digests of the four public tables are
the format's: at every other o the seats refuse, and a law at every o holds there by the verifier's
refusal. One o stands in premise and term: nothing is said across two.
Limits. The branch that refuses alone. `verifyBy_never_all` speaks of the entry's decision alone: a
record of letters whose entry's decision can say yes is not covered, whatever its other two do. In
scope no files are known at which `protocolDataWellFormed` says no: there
these laws may be empty; they serve a split by cases. Nothing on soundness.

-/
import Johnson.Goal.Tie.NeverEvery
import Johnson.Goal.Description.AtSecondHashFunction
import Johnson.Goal.Description.ProofWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat

/-- **No, at every parser, every form and every hash function**, where the entry's decision never
says yes. -/
theorem verifyBy_never_all
    (more : PublicFiles → Digest → DeterministicAlgorithm (List (_root_.Iop.Dig 256))) (L : DescriptionData) (Z : PublicFiles)
    (never : ∀ rr v, L.dec (asDescriptionFiles Z) rr v = false) {Form : Type}
    (parse : Parser (descriptionOfDataWithReading more L) Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (descriptionOfDataWithReading more L) Z parse commitment prompt output form).evaluate hash =
      false := by
  cases scope : VerifierAndGoals.InScope Z with
  | false => exact verify_evaluate_out _ Z parse scope hash commitment prompt output form
  | true =>
    rw [verify_evaluate _ Z parse scope hash]
    exact innerCompiledVerifierAtFullSize_never never ((dataAtFiles L Z).inputFieldsAtReadings _ _) hash commitment prompt output _

end FlashProve

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat

/-- The gate is shut where `protocolDataWellFormedAt o` says no. -/
theorem theLayAt_dec_dead (o : SecondHashFunctionType) (Zk : OnBytes.K.Pub) (dead : protocolDataWellFormedAt o Zk = false)
    (rr : RecFull × RecFull) (v : _root_.Run.PQ.View) : (flashProveDataAtSecondHash o).dec Zk rr v = false :=
  gate1_dead dead (linkDecisionAtFiles Zk) rr v

/-- **At every o: where `protocolDataWellFormedAt o` says no: no to all.** -/
theorem theDescriptionO_dead_all (o : SecondHashFunctionType) (Z : PublicFiles) (dead : protocolDataWellFormedAt o (asDescriptionFiles Z) = false)
    {Form : Type} (parse : Parser (theDescriptionO o) Z Form) (hash : Hash)
    (commitment : Commitment) (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (theDescriptionO o) Z parse commitment prompt output form).evaluate hash =
      false :=
  verifyBy_never_all _ (flashProveDataAtSecondHash o) Z (theLayAt_dec_dead o (asDescriptionFiles Z) dead) parse hash commitment
    prompt output form

theorem theDescriptionO_no_of_plan_all (o : SecondHashFunctionType) (Z : PublicFiles) (e : String)
    (h : filesParametersOrRefusalAt o (asDescriptionFiles Z) = .error e) {Form : Type}
    (parse : Parser (theDescriptionO o) Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (theDescriptionO o) Z parse commitment prompt output form).evaluate hash =
      false :=
  theDescriptionO_dead_all o Z (theLiveAt_no_of_plan o _ e h) parse hash commitment prompt output
    form

theorem theDescriptionO_no_of_key_all (o : SecondHashFunctionType) (Z : PublicFiles) (e : String)
    (h : keyDataAndDecisionOrRefusalAt o (asDescriptionFiles Z) = .error e) {Form : Type}
    (parse : Parser (theDescriptionO o) Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (theDescriptionO o) Z parse commitment prompt output form).evaluate hash =
      false :=
  theDescriptionO_dead_all o Z (theLiveAt_no_of_key o _ e h) parse hash commitment prompt output
    form

theorem theDescriptionO_no_of_proof_all (o : SecondHashFunctionType) (Z : PublicFiles) (e : String)
    (h : proofDataAndDecisionOrRefusalAt o (asDescriptionFiles Z) = .error e) {Form : Type}
    (parse : Parser (theDescriptionO o) Z Form) (hash : Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (theDescriptionO o) Z parse commitment prompt output form).evaluate hash =
      false :=
  theDescriptionO_dead_all o Z (theLiveAt_no_of_proof o _ e h) parse hash commitment prompt output
    form

/-- **At the name, at every o.** `theDescription` is `theDescriptionO`. -/
theorem theDescription_dead_all (o : SecondHashFunctionType) (Z : PublicFiles) (dead : protocolDataWellFormedAt o (asDescriptionFiles Z) = false)
    {Form : Type} (parse : Parser (theDescription o) Z Form) (hash : Hash)
    (commitment : Commitment) (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (theDescription o) Z parse commitment prompt output form).evaluate hash =
      false :=
  theDescriptionO_dead_all o Z dead parse hash commitment prompt output form

/-- **At the name, where the goals read it, in scope: no to all, or the written data.** -/
theorem proof_written_or_no_all (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) :
    (∀ (Form : Type) (parse : Parser (atSecondHashFunction theDescription) Z Form) (hash : Hash)
        (commitment : Commitment) (prompt output : List Token) (form : Form),
        (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z parse commitment prompt output form).evaluate
          hash = false) ∨
      (theProofData (asDescriptionFiles Z) = Johnson.G.writtenPFull ∧
        (dataAtFiles flashProveData Z).DP = Johnson.G.writtenPFull) := by
  cases hl : protocolDataWellFormed (asDescriptionFiles Z) with
  | false =>
    exact Or.inl fun _ parse hash c p out form =>
      theDescription_dead_all OnBytes.secondHashFunction Z hl parse hash c p out form
  | true => exact Or.inr ⟨proof_written_of_live Z scope hl, proof_built_written Z scope hl⟩

end FlashProve

#print axioms FlashProve.verifyBy_never_all
#print axioms FlashProve.theDescriptionO_dead_all
#print axioms FlashProve.theDescriptionO_no_of_plan_all
#print axioms FlashProve.theDescriptionO_no_of_key_all
#print axioms FlashProve.theDescriptionO_no_of_proof_all
#print axioms FlashProve.theDescription_dead_all
#print axioms FlashProve.proof_written_or_no_all
