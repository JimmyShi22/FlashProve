-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SoundAtCommittedExact.lean: SOUNDNESS AFTER AN HONEST COMMITMENT AT EXACT MATCH:
AFTER A COMMITMENT BY THE COMMITTER OF theCpp (theTwin g) TO WEIGHTS w, AN ACCEPTED OUTPUT IS THE
MODEL'S OUTPUT AT w, BUT WITH A SMALL PROBABILITY: the library's own SoundAfterHonestCommitment
(VerifiableInference/MoreStatements.lean), with no extractor in the statement, at every set of
public files in scope that is read and whose policy is exact match; and at the named full-size files
with no premise. Calls alone.
NOTHING HERE SPEAKS OF A COMMITMENT THAT THE RELEASE'S COMMITTING PROGRAM MAKES: "the committer" is
the Lean text of Johnson/Bind/Twin.lean, which no theorem ties to that program.
NOTHING HERE SAYS THAT AN OUTPUT ACCEPTED UNDER A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM IS
THE MODEL'S AT THE WEIGHTS THAT THE PROGRAM WAS GIVEN. verify IS THE LEAN VERIFIER, NOT THE
RELEASE'S VERIFYING PROGRAM.

What it says, in plain words. As Johnson/Bind/Cpp/SoundAtCommitted.lean, with the claim "is the
model's output" in the place of "meets the files' policy": the probability that verify accepts while
some output token is not the integer model's next token at w, after the prompt and the output tokens
before it, is at most soundnessErrorInQueries (c + p) n + bindingErrorInQueries (2^35 + 2). In numbers, at c = 2^35 + 2 and n up
to 2^23: about 2^-88 at p = 0, about 2^-60 at p = 2^64, below 1 up to p of about 2^123: 124 bits for
each query of the prover, never below about 2^-88, since the committer's own 2^35 queries are
charged in both summands. No figure here is 128 bits.

Why it follows. At the policy of exact match "meets the policy" says: the output is not empty, and
it is the model's (Policy.meetsPolicy_exact_iff, Policy/Front/MeetsPolicyGuards.lean). A statement
of this kind for a claim gives the same for every weaker claim
(SoundAfterHonestCommitmentFor.weaken, Johnson/Bind/WeakerClaim.lean). That the named full-size
files state exact match is a theorem (VerifierAndGoals.filesRead.full,
Johnson/Goal/Files/FilesReadProof.lean).

Main names (namespace Bind.Cpp).
  **soundAtCommitted_exact_nonempty**: in scope, read, exact match: the claim is "not empty, and the
    model's" (ArgumentSystem.IsModelOutputNonEmpty, VerifiableInference/StatementsNonEmpty.lean).
  **soundAtCommitted_exact**: the same in the library's own form. There an accepted empty output is
    no bad event: the empty output is the model's at all weights (isModelOutput_nil, the same file).
  **soundAtCommitted_exact_zFull**: both forms at the named full-size files storedPublicFiles: no premise.
Limits. ALL THOSE OF Johnson/Bind/Cpp/SoundAtCommitted.lean HOLD. First among them:
- The premise on the description's tests on the public files (protocolDataWellFormed) is shed there BY CASES: where
  these tests fail, verify rejects everything and the statement holds for that poorest of reasons.
  The theorem does not tell which arm holds at any files: that the tests pass at storedPublicFiles is evaluated:
  it is no theorem of the main library. At storedPublicFiles they pass by theorems of a side library, outside
  the main library and with that library's own limits: so of the two arms the live one, where the
  tests pass, is the one that holds there (AtFullSide/Bind/LiveAtNamed.lean). So the instance holds
  with no premise; but no case in which it FORBIDS anything is shown by theorems alone: that hangs
  on the tests' passing there, and on an accept.
- NOTHING SAYS THAT verify ACCEPTS ANY PROOF UNDER A COMMITMENT OF THIS COMMITTER's MAKE: it makes
  no key file, and no honest prover is written for this variant (theCpp).
- AS A STATEMENT ON THE COMMITTER THE FORM IS ONE-SIDED: IT IS NO TEST OF THE COMMITTER: a committer
  under whose commitments verify accepts nothing meets it too (the description's own hollow
  committer; a constant one); no theorem of this library shows that a committer that does not read
  the weights fails it; it has teeth on the committer only beside an accept (that "only" is an
  argument, no theorem). (The hollow committer: hollow_meets_join,
  Johnson/Bind/Cpp/JoinControls.lean; the constant one: argued, no theorem.) What parts this
  committer from such ones is correctness of extraction, which a committer that does not read the
  weights fails by a theorem (blind_extracts, Johnson/Bind/Cpp/Controls.lean); and such a committer
  cannot have both this form and completeness at small errors (blind_exact_join_and_complete,
  JoinControls.lean). Teeth are shown against committers that do not read the weights alone. The two
  theorems do not meet: the hollow committer stands at the description's own system, not at theCpp.
  No negative test shows that a blind committer FAILS this statement: without an accept none can;
  the two theorems say what the form does and does not test (Johnson/Bind/Cpp/JoinControls.lean).
- AT THE FULL-SIZE SHAPE ALONE, WHERE THIS COMMITTER CAN NEVER BE RUN (about 2^72 multiplications):
  "running" says that Lean has code for it; it has run at small shapes, and verify stands at the
  full size alone, so no run at any size tries this statement.
- "At w" means: at Lean's integer weights, laid into the table by the library's own digits
  (entryOf); that this is the programs' placement or quantization is compared nowhere. "The model"
  is the integer model at the public scale and parameter files.
- storedPublicFiles is the bytes written in Ladder/Stored.lean; that these are the bytes of the folder examples/
  is not said here.
- The weights, the public files, the generator and the prover's strategy are fixed before the hash
  function is sampled. An average over seeds; one commitment, one proof. That a given commitment was
  made by this committer is outside the statement. The generator g and both provers in the
  statements (prove, prv) are free variables: the statements hold whatever they are. g is a
  function: it is handed two answers of the hash function and may ask it nothing.
- Both probabilities are other files': soundness under the policy stands on files on coding theory
  adapted from third-party Lean (lean/LIMITS.md, L15); correctness of
  extraction on bindsWith_plain_law (Johnson/Goal/Conditions/BindsTold.lean).
  The format's second hash function is a fixed function.
- This is none of the goals of Ladder.lean and Ladder/Bits.lean: no goal is stated here. No theorem
  ties this committer to the program; what evaluations have compared stands in
  Johnson/Bind/README.md ("What is run, not proved"). No completeness, no index privacy.
Terms: lean/TERMS.md, lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.SoundAtCommitted
import Johnson.Bind.WeakerClaim
import Policy.Front.MeetsPolicyGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Bind.Twin (Shape Table)

/- Lean compares these by their names. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget theTwin
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan
  FlashProve.theItem LayoutsByPublicReading.commitAtCoins

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **Soundness after an honest commitment at exact match, with the claim as the policy has it**:
the output is not empty, and it is the model's at the committed weights. In scope, read, exact
match.
-/
theorem soundAtCommitted_exact_nonempty (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (he : pp.pol = Inst.Model.AcceptancePolicy.exact) (Form : Type)
    (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
      List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) Z Form) (n : ℕ) (hn : parse.Within n) :
    SoundAfterHonestCommitmentFor
      (system (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp) Form prv parse)
      (system (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp) Form prv
        parse).IsModelOutputNonEmpty
      fun committerQueries proverQueries =>
        soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) := by
  have h := soundAtCommitted prove g Z pp hs hr Form prv parse n hn
  rw [he] at h
  exact h.weaken fun w prompt output hm => (Policy.meetsPolicy_exact_iff w prompt output).1 hm

/-- **The same in the library's own form**: soundness after an honest commitment: an accepted output
is the model's at the committed weights. An accepted empty output is no bad event here. -/
theorem soundAtCommitted_exact (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (he : pp.pol = Inst.Model.AcceptancePolicy.exact) (Form : Type)
    (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
      List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) Z Form) (n : ℕ) (hn : parse.Within n) :
    SoundAfterHonestCommitment
      (system (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp) Form prv parse)
      fun committerQueries proverQueries =>
        soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) :=
  (soundAtCommitted_exact_nonempty prove g Z pp hs hr he Form prv parse n hn).weaken
    fun _ _ _ hm => hm.2

/-- **Both forms at the named full-size files storedPublicFiles, which state exact match: no premise.** Which
arm of the split in soundAtCommitted holds there is not told: that protocolDataWellFormed passes there is
evaluated: it is no theorem of the main library. -/
theorem soundAtCommitted_exact_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    InScope storedPublicFiles = true ∧ ∃ pp, readFiles storedPublicFiles = .ok pp ∧ pp.pol = Inst.Model.AcceptancePolicy.exact ∧
      ∀ (Form : Type)
        (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
          List Token → List Token → RandomizedAlgorithm Form)
        (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles Form) (n : ℕ), parse.Within n →
        SoundAfterHonestCommitmentFor
            (system (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp) Form prv parse)
            (system (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp) Form prv
              parse).IsModelOutputNonEmpty
            (fun committerQueries proverQueries =>
              soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2)) ∧
          SoundAfterHonestCommitment
            (system (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp) Form prv parse)
            fun committerQueries proverQueries =>
              soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) :=
  let ⟨sc, pp, hr, he⟩ := VerifierAndGoals.filesRead.full
  ⟨sc, pp, hr, he, fun Form prv parse n hn =>
    ⟨soundAtCommitted_exact_nonempty prove g storedPublicFiles pp sc hr he Form prv parse n hn,
      soundAtCommitted_exact prove g storedPublicFiles pp sc hr he Form prv parse n hn⟩⟩

end Bind.Cpp

end

#print axioms Bind.Cpp.soundAtCommitted_exact_nonempty
#print axioms Bind.Cpp.soundAtCommitted_exact
#print axioms Bind.Cpp.soundAtCommitted_exact_zFull
