-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SoundAtCommitted.lean: AFTER A COMMITMENT BY THE COMMITTER OF theCpp (theTwin g) TO
WEIGHTS w, AN ACCEPTED OUTPUT MEETS THE FILES' POLICY AT w, BUT WITH A SMALL PROBABILITY: soundness
after an honest commitment (SoundAfterHonestCommitmentFor, VerifiableInference/MoreStatements.lean),
with no extractor in the statement, at every set of public files in scope that is read. Calls, and
one split by cases.
NOTHING HERE SPEAKS OF A COMMITMENT THAT THE RELEASE'S COMMITTING PROGRAM MAKES: "the committer" is
the Lean text of Johnson/Bind/Twin.lean, which no theorem ties to that program.
NOTHING HERE SAYS THAT AN OUTPUT ACCEPTED UNDER A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM
MEETS THE POLICY, OR IS THE MODEL'S, AT THE WEIGHTS THAT THE PROGRAM WAS GIVEN. verify IS THE LEAN
VERIFIER, NOT THE RELEASE'S VERIFYING PROGRAM.

What it says, in plain words. Fix the public files Z (in scope, read), a generator g, a parser that
asks the hash function at most n times, weights w, and then a prover, which may know all of these.
Then the hash function is sampled. The committer samples a seed and commits to w. The prover is
given the commitment ID and the seed, asks at most p queries and names a prompt, an output and a
proof. The probability that verify accepts while the output does not meet the files' policy AT w
(Policy.MeetsPolicy) is at most soundnessErrorInQueries (c + p) n + bindingErrorInQueries (2^35 + 2), where c bounds the
committer's own queries (2^35 + 2 serves: honest_count). In numbers, at c = 2^35 + 2 and n up to
2^23: about 2^-88 at p = 0, about 2^-60 at p = 2^64, below 1 up to p of about 2^123: 124 bits for
each query of the prover, never below about 2^-88, since the committer's own 2^35 queries are
charged in both summands (with the second summand at the square form, soundAtCommitted_square: about
2^-89). No figure here is 128 bits. It is an average over seeds (g is any function: at a constant g
it is the statement at one fixed setting of coins; at each single seed or coins:
Johnson/Bind/Cpp/SoundAtCommittedAt.lean), and a joint probability, not a conditional one.

Why. Soundness under the files' policy (g8bits_cpp, Johnson/Bind/Cpp/OfTie.lean) says that an
accepted output meets the policy at the weights that the extractor gives. Correctness of extraction
(extractsCommitted_salt, Johnson/Bind/Cpp/TheTie.lean) says that after this committer's run the same
extractor gives the committed weights. The library's SoundForWith.soundAfterHonestCommitmentFor
(VerifiableInference/AgreementWith.lean) joins two such statements at one system and one extractor.
Here it is called. It adds to soundness exactly what correctness of extraction adds: "the weights
that the extractor gives" becomes "w", and the extractor leaves the statement.

Main names (namespace Bind.Cpp).
  extracts_anyForm: correctness of extraction reads neither the form, nor the prover, nor the
    parser: by definition.
  honest_count: the committer, its sampler before it, asks at most 2^35 + 2 queries.
  **soundAtCommitted_salt**: in scope, read, where the frame's salts have 40 bytes.
  live_of_accept_cpp, rejects_of_dead: an accept of verify at theCpp, at any parser and any hash
    function, gives that the description's tests on the public files (protocolDataWellFormed) pass; so where they
    fail, verify accepts nothing.
  **soundAtCommitted**: AT EVERY Z IN SCOPE THAT IS READ: neither protocolDataWellFormed nor the salts among the
    premises. soundAtCommitted_square: the same with the second summand at the square form.
  **soundAtCommitted_zFull**, **soundAtCommitted_zGap**: at the goals' two named sets of public
    files: no premise at all.
  **soundAtCommitted_own**, soundAtCommitted_own_zFull, soundAtCommitted_own_zGap: THE EXPERIMENT
    WRITTEN OUT, at the description's own form and parser (which asks at most one query) and the
    committer's own count: no variable stands for verify.
Limits. HOW THE PREMISE ON protocolDataWellFormed IS SHED: BY CASES. WHERE protocolDataWellFormed FAILS, THE STATEMENT HOLDS
BECAUSE verify REJECTS EVERYTHING (SoundAfterHonestCommitmentFor.of_rejects,
Johnson/Bind/RejectsAll.lean): THE POOREST OF REASONS. THE THEOREM DOES NOT TELL WHICH ARM HOLDS AT
ANY FILES: that protocolDataWellFormed passes at storedPublicFiles and zGap is evaluated; it is no theorem of the main library.
At both it passes by theorems of a side library, outside the main library and with that library's
own limits: so of the two arms the live one, where protocolDataWellFormed passes, is the one that holds there
(AtFullSide/Bind/LiveAtNamed.lean).
So the two instances hold with no premise; but no case in which they FORBID anything is shown by
theorems alone: that hangs on protocolDataWellFormed's passing there, and on an accept. No files in scope are known
at which protocolDataWellFormed fails.
NOTHING SAYS THAT verify ACCEPTS ANY PROOF UNDER A COMMITMENT OF THIS COMMITTER's MAKE: the
committer makes no key file, and no honest prover is written for this variant (theCpp). If verify
accepted none, this theorem would hold for that reason too.
AS A STATEMENT ON THE COMMITTER THE FORM IS ONE-SIDED: IT IS NO TEST OF
THE COMMITTER: a committer under whose commitments verify accepts nothing meets it too (the
description's own hollow committer; a constant one); no theorem of this library shows that a
committer that does not read the weights fails it; it has teeth on the committer only beside an
accept (that "only" is an argument, no theorem). In more words: the hollow committer (a commitment
of zeros, no query) meets it at soundnessErrorInQueries (c + p) n and for every claim (hollow_meets_join,
Johnson/Bind/Cpp/JoinControls.lean); a constant one likewise (argued: an accept would need a key
whose code the hash function sends to that constant); where protocolDataWellFormed fails, every committer meets it.
No negative test shows that a blind committer FAILS this statement: without an accept none can
(argued); two tests say what the form does and does not test (Johnson/Bind/Cpp/JoinControls.lean).
The two do not meet: hollow_meets_join stands at the description's own system, whose committer is no
theCpp T; the negative tests on a blind committer stand at theCpp T. The negative tests of
Johnson/Bind/Cpp/Controls.lean stand at correctness of extraction and at the opening forms, which a
committer that does not read the weights (blindTwin) fails by theorems. Beside completeness the
statement would tell them apart: a committer that does not read the weights and keeps the count
(CountAt) cannot meet this form at an error ε and completeness at an error α unless 1 ≤ α + ε(c, p)
at c = 2^35 + 2, p the honest prover's queries (ε is a function of the two counts: no product): for
any claim, given a request that is served at some weights and fails the claim at others
(blind_join_and_complete, there); for the claim "is the model's output", where such a request is
shown (blind_exact_join_and_complete); for the second named policy no such request is shown. These
teeth are shown against committers that do not read the weights alone: one that reads them and lays
them wrongly, or reads some of them, is not covered.
AT THE FULL-SIZE SHAPE ALONE, WHERE THIS COMMITTER CAN NEVER BE RUN (about 2^72 multiplications):
"running" says that Lean has code for it; it has run at small shapes, and verify stands at the full
size alone, so no run at any size tries this statement. "AT w" means: at Lean's integer weights,
laid into the table by the library's own digits (entryOf); that this is the programs' placement or
quantization is compared nowhere.
That a given commitment was made by this committer is outside the statement. One commitment, one
proof. The weights, the public files and the prover are fixed before the hash function is sampled.
The claim is "meets the files' policy", not "is the model's output" (at exact match:
Johnson/Bind/Cpp/SoundAtCommittedExact.lean); at some policies in scope it leaves every counted
token free (the docstring of G8, Ladder.lean). storedPublicFiles and zGap are the bytes written in
Ladder/Stored.lean. The generator g and both provers in the statements (prove, prv) are free
variables: the statements hold whatever they are, and the experiment runs neither prover; g is a
function of the shape, the seed and two answers: it asks the hash function nothing itself. No
theorem ties this committer to the program. Evaluations have compared it with runs of the program at
the small stored example's public files, on synthetic weights, and nowhere else; what was compared,
and what was not, stands in Johnson/Bind/README.md ("What is run, not proved").
Both probabilities are other files': soundness under the policy (g8bits_of_verify,
Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean) stands on files on coding theory
adapted from third-party Lean (lean/LIMITS.md, L15); correctness of extraction on
bindsWith_plain_law (Johnson/Goal/Conditions/BindsTold.lean).
The format's second hash function is a fixed function. This is none of the goals of
Ladder.lean and Ladder/Bits.lean: no goal is stated here. All limits of OfTie.lean, TheTie.lean and
SoundOfVerifyPolicy.lean hold. No completeness, no index privacy.
Sources. The experiment in soundAtCommitted_own and in its two instances is written out as two other
files of this library have it: it is the one in the body of SoundAfterHonestCommitmentFor
(VerifiableInference/MoreStatements.lean), unfolded at this system, and it stands likewise in the
statement of SoundForWith.afterHonestCommitment (VerifiableInference/HonestCommitment.lean).







Terms: lean/TERMS.md, lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.TheTie
import Johnson.Bind.RejectsAll
import Johnson.Goal.Description.AcceptGivesLive
import VerifiableInference.AgreementWith

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

/-- Correctness of extraction reads neither the form, nor the prover, nor the parser. -/
theorem extracts_anyForm {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {E : Commitment → QueryLog → Option (ModelWeights s)} {α : ℝ≥0∞}
    (h : ExtractsCommittedWeights (systemOfRecord D Z s) E α) (Form : Type)
    (prv : ModelWeights s → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser D Z Form) : ExtractsCommittedWeights (system D Z s Form prv parse) E α := h

/- Lean compares these by their names. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget theTwin
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan
  FlashProve.theItem LayoutsByPublicReading.commitAtCoins

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- The committer, its sampler before it, asks at most 2^35 + 2 queries. -/
theorem honest_count (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    ((atSecondHashFunction (theCpp (theTwin g) prove)).sample.bind fun ρ =>
      ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z s w ρ).toRandomized).QueryBound
        (twinBudget + 2) :=
  fun t => commit_count (theTwin g) Z (count_theTwin g Z) s w (.inl t)

/-- **Soundness after an honest commitment, for the files' policy, where the frame's salts have 40
bytes**: in scope, read. -/
theorem soundAtCommitted_salt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp) (h40 : SaltAt Z)
    (Form : Type)
    (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
      List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) Z Form) (n : ℕ) (hn : parse.Within n) :
    SoundAfterHonestCommitmentFor
      (system (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp) Form prv parse)
      (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
      fun committerQueries proverQueries =>
        soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) :=
  SoundForWith.soundAfterHonestCommitmentFor
    (system (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp) Form prv parse)
    ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp))
    (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) (fun t => soundnessErrorInQueries t n)
    (bindingErrorInQueries (twinBudget + 2))
    (((g8bits_cpp (theTwin g) prove).2 Z pp hs hr).2 Form prv parse n hn)
    (extracts_anyForm (extractsCommitted_salt prove g Z pp hr h40) Form prv parse)

/-- An accept of verify at descriptionOfDataOnBytes flashProveData, at any parser and any hash function, gives that
protocolDataWellFormed passes: live_of_accept (Johnson/Goal/Description/AcceptGivesLive.lean) under that name. -/
theorem live_of_accept_D₀ (Z : PublicFiles) {Form : Type} (parse : Parser flashProveDescription Z Form) (hash : Hash)
    (commitment : Commitment) (prompt output : List Token) (form : Form)
    (h : (VerifierAndGoals.verify flashProveDescription Z parse commitment prompt output form).evaluate hash = true) :
    protocolDataWellFormed (asDescriptionFiles Z) = true := by
  have key := @live_of_accept Z Form
  rw [VerifierAndGoals.AtTheName.the_description_is] at key
  exact key parse hash commitment prompt output form h

/-- The same at theCpp, whose verifier is that one. -/
theorem live_of_accept_cpp (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles) {Form : Type}
    (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) Z Form) (hash : Hash)
    (commitment : Commitment) (prompt output : List Token) (form : Form)
    (h : (VerifierAndGoals.verify (atSecondHashFunction (theCpp (theTwin g) prove)) Z parse commitment prompt output
      form).evaluate hash = true) : protocolDataWellFormed (asDescriptionFiles Z) = true :=
  live_of_accept_D₀ Z parse hash commitment prompt output form h

/-- Where protocolDataWellFormed fails, verify at theCpp accepts nothing. -/
theorem rejects_of_dead (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (hd : protocolDataWellFormed (asDescriptionFiles Z) = false) {Form : Type}
    (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) Z Form) (hash : Hash)
    (commitment : Commitment) (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (atSecondHashFunction (theCpp (theTwin g) prove)) Z parse commitment prompt output
      form).evaluate hash = false := by
  cases h : (VerifierAndGoals.verify (atSecondHashFunction (theCpp (theTwin g) prove)) Z parse commitment prompt output
      form).evaluate hash with
  | false => rfl
  | true =>
    have hl := live_of_accept_cpp prove g Z parse hash commitment prompt output form h
    rw [hd] at hl
    exact absurd hl Bool.false_ne_true

/-- **The same at every Z in scope that is read.** By cases on the description's tests on the public
files (protocolDataWellFormed): where they pass, the frame's salts have 40 bytes and soundAtCommitted_salt serves;
WHERE THEY FAIL, verify REJECTS EVERYTHING AND THE BAD EVENT IS EMPTY. The theorem does not tell
which arm holds. -/
theorem soundAtCommitted (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (Form : Type)
    (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
      List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) Z Form) (n : ℕ) (hn : parse.Within n) :
    SoundAfterHonestCommitmentFor
      (system (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp) Form prv parse)
      (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
      fun committerQueries proverQueries =>
        soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) := by
  cases hl : protocolDataWellFormed (asDescriptionFiles Z) with
  | true =>
    exact soundAtCommitted_salt prove g Z pp hs hr (saltAt_of_live hs hl) Form prv parse n hn
  | false =>
    exact SoundAfterHonestCommitmentFor.of_rejects _ _ _ fun hash commitment prompt output form =>
      rejects_of_dead prove g Z hl parse hash commitment prompt output form

/-- Correctness of extraction at the square form, where the frame's salts have 40 bytes:
3 (2^35 + 4 + 2 · 2^48 + 2)² / 2^256, about 2^-156. -/
theorem extractsCommitted_square_salt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (h40 : SaltAt Z) :
    ExtractsCommittedWeights
      (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp))
      (epsBind honestBudget (twinBudget + 2 + 2)) :=
  (bindsWith_of_tieAt (theTwin g) prove Z pp hr (tieAt Z h40 g)).extractsDrawn (2 ^ 256 - 1)
    (fun t => .inl t) rfl (twinBudget + 2)
    fun w ρ => commit_count (theTwin g) Z (count_theTwin g Z) (settingsOfRead pp) w ρ

/-- **The same with the second summand at the square form**, about 2^-156: at every Z in scope that
is read; by the same split. -/
theorem soundAtCommitted_square (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (Form : Type)
    (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
      List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) Z Form) (n : ℕ) (hn : parse.Within n) :
    SoundAfterHonestCommitmentFor
      (system (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp) Form prv parse)
      (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
      fun committerQueries proverQueries =>
        soundnessErrorInQueries (committerQueries + proverQueries) n + epsBind honestBudget (twinBudget + 2 + 2) := by
  cases hl : protocolDataWellFormed (asDescriptionFiles Z) with
  | true =>
    exact SoundForWith.soundAfterHonestCommitmentFor
      (system (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp) Form prv parse)
      ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp))
      (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) (fun t => soundnessErrorInQueries t n)
      (epsBind honestBudget (twinBudget + 2 + 2))
      (((g8bits_cpp (theTwin g) prove).2 Z pp hs hr).2 Form prv parse n hn)
      (extracts_anyForm (extractsCommitted_square_salt prove g Z pp hr (saltAt_of_live hs hl))
        Form prv parse)
  | false =>
    exact SoundAfterHonestCommitmentFor.of_rejects _ _ _ fun hash commitment prompt output form =>
      rejects_of_dead prove g Z hl parse hash commitment prompt output form

/-- **At the goals' first named set of public files, whose policy is exact match: no premise.**
Which arm of the split holds there is not told: that protocolDataWellFormed passes there is evaluated: it is no
theorem of the main library. With the claim "is the model's output":
Johnson/Bind/Cpp/SoundAtCommittedExact.lean. -/
theorem soundAtCommitted_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    InScope storedPublicFiles = true ∧ ∃ pp, readFiles storedPublicFiles = .ok pp ∧ pp.pol = Inst.Model.AcceptancePolicy.exact ∧
      ∀ (Form : Type)
        (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
          List Token → List Token → RandomizedAlgorithm Form)
        (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles Form) (n : ℕ), parse.Within n →
        SoundAfterHonestCommitmentFor
          (system (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp) Form prv parse)
          (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
          fun committerQueries proverQueries =>
            soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) :=
  let ⟨sc, pp, hr, hp⟩ := VerifierAndGoals.filesRead.full
  ⟨sc, pp, hr, hp,
    fun Form prv parse n hn => soundAtCommitted prove g storedPublicFiles pp sc hr Form prv parse n hn⟩

/-- **At the goals' second named set of public files, whose policy is (25856, 512, 1): no premise.**
Which arm of the split holds there is not told. -/
theorem soundAtCommitted_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    InScope zGap = true ∧ ∃ pp, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩ ∧
      ∀ (Form : Type)
        (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
          List Token → List Token → RandomizedAlgorithm Form)
        (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) zGap Form) (n : ℕ), parse.Within n →
        SoundAfterHonestCommitmentFor
          (system (atSecondHashFunction (theCpp (theTwin g) prove)) zGap (settingsOfRead pp) Form prv parse)
          (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
          fun committerQueries proverQueries =>
            soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) :=
  let ⟨sc, pp, hr, hp⟩ := VerifierAndGoals.filesRead.other
  ⟨sc, pp, hr, hp,
    fun Form prv parse n hn => soundAtCommitted prove g zGap pp sc hr Form prv parse n hn⟩

/-- **THE EXPERIMENT WRITTEN OUT, at the description's own form and parser** (which asks the hash
function at most once: descriptionOfDataOnBytes_within, Johnson/Goal/Tie/DescriptionOfData.lean) **and the committer's
own count**: at every Z in scope that is read. soundAtCommitted at these. -/
theorem soundAtCommitted_own (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (p : ℕ)
    (prover : Commitment → Rand → RandomizedAlgorithm (List Token × List Token × flashProveDescription.Form))
    (hp : ∀ commitment ρ, (prover commitment ρ).QueryBound p) :
    Prob (do
        let ρ ← (atSecondHashFunction (theCpp (theTwin g) prove)).sample
        let commitment ←
          ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z (settingsOfRead pp) w
            ρ).toRandomized
        let (prompt, output, form) ← prover commitment ρ
        let accepted ←
          (VerifierAndGoals.verify (atSecondHashFunction (theCpp (theTwin g) prove)) Z
            ((atSecondHashFunction (theCpp (theTwin g) prove)).parse Z) commitment prompt output
            form).toRandomized
        pure (prompt, output, accepted))
      {(prompt, output, accepted) | accepted = true ∧
        ¬ Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output}
      ≤ soundnessErrorInQueries (twinBudget + 2 + p) 1 + bindingErrorInQueries (twinBudget + 2) :=
  soundAtCommitted prove g Z pp hs hr flashProveDescription.Form
    ((atSecondHashFunction (theCpp (theTwin g) prove)).prove Z (settingsOfRead pp))
    ((atSecondHashFunction (theCpp (theTwin g) prove)).parse Z) 1
    (fun prompt output form => descriptionOfDataOnBytes_within flashProveData Z prompt output form) w (twinBudget + 2) p
    (honest_count prove g Z (settingsOfRead pp) w) prover hp

/-- **That at the goals' first named set of public files, whose policy is exact match: no premise.**
Which arm of the split holds there is not told. -/
theorem soundAtCommitted_own_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    InScope storedPublicFiles = true ∧ ∃ pp, readFiles storedPublicFiles = .ok pp ∧ pp.pol = Inst.Model.AcceptancePolicy.exact ∧
      ∀ (w : ModelWeights (settingsOfRead pp)) (p : ℕ)
        (prover : Commitment → Rand → RandomizedAlgorithm (List Token × List Token × flashProveDescription.Form)),
        (∀ commitment ρ, (prover commitment ρ).QueryBound p) →
        Prob (do
            let ρ ← (atSecondHashFunction (theCpp (theTwin g) prove)).sample
            let commitment ←
              ((atSecondHashFunction (theCpp (theTwin g) prove)).commit storedPublicFiles (settingsOfRead pp) w
                ρ).toRandomized
            let (prompt, output, form) ← prover commitment ρ
            let accepted ←
              (VerifierAndGoals.verify (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles
                ((atSecondHashFunction (theCpp (theTwin g) prove)).parse storedPublicFiles) commitment prompt output
                form).toRandomized
            pure (prompt, output, accepted))
          {(prompt, output, accepted) | accepted = true ∧
            ¬ Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output}
          ≤ soundnessErrorInQueries (twinBudget + 2 + p) 1 + bindingErrorInQueries (twinBudget + 2) :=
  let ⟨sc, pp, hr, hpol⟩ := VerifierAndGoals.filesRead.full
  ⟨sc, pp, hr, hpol,
    fun w p prover hp => soundAtCommitted_own prove g storedPublicFiles pp sc hr w p prover hp⟩

/-- **That at the goals' second named set of public files, whose policy is (25856, 512, 1): no
premise.** Which arm of the split holds there is not told. -/
theorem soundAtCommitted_own_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    InScope zGap = true ∧ ∃ pp, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩ ∧
      ∀ (w : ModelWeights (settingsOfRead pp)) (p : ℕ)
        (prover : Commitment → Rand → RandomizedAlgorithm (List Token × List Token × flashProveDescription.Form)),
        (∀ commitment ρ, (prover commitment ρ).QueryBound p) →
        Prob (do
            let ρ ← (atSecondHashFunction (theCpp (theTwin g) prove)).sample
            let commitment ←
              ((atSecondHashFunction (theCpp (theTwin g) prove)).commit zGap (settingsOfRead pp) w
                ρ).toRandomized
            let (prompt, output, form) ← prover commitment ρ
            let accepted ←
              (VerifierAndGoals.verify (atSecondHashFunction (theCpp (theTwin g) prove)) zGap
                ((atSecondHashFunction (theCpp (theTwin g) prove)).parse zGap) commitment prompt output
                form).toRandomized
            pure (prompt, output, accepted))
          {(prompt, output, accepted) | accepted = true ∧
            ¬ Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output}
          ≤ soundnessErrorInQueries (twinBudget + 2 + p) 1 + bindingErrorInQueries (twinBudget + 2) :=
  let ⟨sc, pp, hr, hpol⟩ := VerifierAndGoals.filesRead.other
  ⟨sc, pp, hr, hpol,
    fun w p prover hp => soundAtCommitted_own prove g zGap pp sc hr w p prover hp⟩

end Bind.Cpp

end

#print axioms Bind.Cpp.extracts_anyForm
#print axioms Bind.Cpp.honest_count
#print axioms Bind.Cpp.soundAtCommitted_salt
#print axioms Bind.Cpp.live_of_accept_D₀
#print axioms Bind.Cpp.live_of_accept_cpp
#print axioms Bind.Cpp.rejects_of_dead
#print axioms Bind.Cpp.soundAtCommitted
#print axioms Bind.Cpp.extractsCommitted_square_salt
#print axioms Bind.Cpp.soundAtCommitted_square
#print axioms Bind.Cpp.soundAtCommitted_zFull
#print axioms Bind.Cpp.soundAtCommitted_zGap
#print axioms Bind.Cpp.soundAtCommitted_own
#print axioms Bind.Cpp.soundAtCommitted_own_zFull
#print axioms Bind.Cpp.soundAtCommitted_own_zGap
