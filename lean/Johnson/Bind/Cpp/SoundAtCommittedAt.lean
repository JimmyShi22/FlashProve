-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SoundAtCommittedAt.lean: SOUNDNESS AFTER AN HONEST COMMITMENT, FOR THE FILES'
POLICY, AT EACH SINGLE RANDOMNESS OF THE COMMITTER: the statement of
Johnson/Bind/Cpp/SoundAtCommitted.lean with the sampler that always gives ρ, a seed or coins, in the
place of the sampler that samples a seed. Calls, and the same split by cases.
NOTHING HERE SPEAKS OF A COMMITMENT THAT THE RELEASE'S COMMITTING PROGRAM MAKES: "the committer" is
the Lean text of Johnson/Bind/Twin.lean, which no theorem ties to that program.
NOTHING HERE SAYS THAT AN OUTPUT ACCEPTED UNDER A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM
MEETS THE POLICY, OR IS THE MODEL'S, AT THE WEIGHTS THAT THE PROGRAM WAS GIVEN. verify IS THE LEAN
VERIFIER, NOT THE RELEASE'S VERIFYING PROGRAM.

Why. SoundAfterHonestCommitmentFor (VerifiableInference/MoreStatements.lean) is an average over the
committer's randomness: by its own docstring it "says nothing of a single one". Correctness of
extraction holds here at every randomness, so the average can be dropped: fix ρ as well, before the
hash function is sampled; the probability is over the hash function (and the prover's coins) alone.
At coins the generator g is not read.

Main names (namespace Bind.Cpp).
  always ρ: the sampler that always gives ρ. It is written as a sample of one number out of one, the
    form that BindsWith.extractsDrawn (Johnson/Bind/ExtractsDrawn.lean) takes.
  extractsCommitted_at: correctness of extraction at theCppWith (always ρ) (theTwin g) prove
    (Johnson/Bind/Cpp/WithSampler.lean), where the frame's salts have 40 bytes.
  **soundAtCommitted_at**: at every ρ, at every Z in scope that is read, every form and parser.
Limits. ALL THOSE OF Johnson/Bind/Cpp/SoundAtCommitted.lean HOLD, among them: WHERE THE
DESCRIPTION's TESTS ON THE PUBLIC FILES (protocolDataWellFormed) FAIL, THE STATEMENT HOLDS BECAUSE verify REJECTS
EVERYTHING, and the theorem does not tell which arm holds; NOTHING SAYS THAT verify ACCEPTS ANY
PROOF UNDER A COMMITMENT OF THIS COMMITTER's MAKE. AS A STATEMENT ON THE COMMITTER THE FORM IS
ONE-SIDED: IT IS NO TEST OF THE COMMITTER: a committer under whose commitments verify accepts
nothing meets it too (the description's own hollow committer; a constant one); no theorem of this
library shows that a committer that does not read the weights fails it; it has teeth on the
committer only beside an accept (that "only" is an argument, no theorem). What the form does and
does not test: Johnson/Bind/Cpp/JoinControls.lean. ρ is fixed before the hash function is sampled:
randomness that is picked with the hash function in hand is not covered. The description is
theCppWith (always ρ) …, one for each ρ: it has theCpp's committer, verifier, parser and extractor
by definition, and another sampler. The committer's count c stays a premise: no theorem of this file
proves it (2^35 + 2 serves, by commit_count, Johnson/Bind/Cpp/OfTie.lean: argued). No written-out
form and no instance at named files stand here. No goal is stated here.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.SoundAtCommitted
import Johnson.Bind.Cpp.WithSampler

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

/-- The committer's sampler that always gives the randomness ρ (a seed or coins): a sample of one
number out of one; it asks the hash function nothing. -/
def always (ρ : Rand) : RandomizedAlgorithm Rand := .sample 0 fun _ => .done ρ

/- Lean compares these by their names. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget theTwin
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan
  FlashProve.theItem LayoutsByPublicReading.commitAtCoins

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- Correctness of extraction at the sampler that always gives ρ, where the frame's salts have 40
bytes. -/
theorem extractsCommitted_at (g : Shape → Seed → Digest → Digest → Coins) (ρ : Rand) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (h40 : SaltAt Z) :
    ExtractsCommittedWeights
      (systemOfRecord (atSecondHashFunction (theCppWith (always ρ) (theTwin g) prove)) Z
        (settingsOfRead pp))
      ((atSecondHashFunction (theCppWith (always ρ) (theTwin g) prove)).extractor Z (settingsOfRead pp))
      (bindingErrorInQueries (twinBudget + 2)) :=
  (bindsAtZ_cppWith (always ρ) (theTwin g) prove Z pp hr (tieAt Z h40 g)
    (count_theTwin g Z)).2.extractsDrawn 0 (fun _ => ρ) rfl (twinBudget + 2)
    fun w r => commit_count (theTwin g) Z (count_theTwin g Z) (settingsOfRead pp) w r

/-- **Soundness after an honest commitment, for the files' policy, at each single randomness ρ**, a
seed or coins: at every Z in scope that is read. By cases on the description's tests on the public
files (protocolDataWellFormed): WHERE THEY FAIL, verify REJECTS EVERYTHING AND THE BAD EVENT IS EMPTY. The theorem
does not tell which arm holds. -/
theorem soundAtCommitted_at (g : Shape → Seed → Digest → Digest → Coins) (ρ : Rand) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp) (Form : Type)
    (prv : ModelWeights (settingsOfRead pp) →
      (atSecondHashFunction (theCppWith (always ρ) (theTwin g) prove)).Rand →
      List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction (theCppWith (always ρ) (theTwin g) prove)) Z Form) (n : ℕ)
    (hn : parse.Within n) :
    SoundAfterHonestCommitmentFor
      (system (atSecondHashFunction (theCppWith (always ρ) (theTwin g) prove)) Z (settingsOfRead pp) Form prv
        parse)
      (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
      fun committerQueries proverQueries =>
        soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) := by
  cases hl : protocolDataWellFormed (asDescriptionFiles Z) with
  | true =>
    exact SoundForWith.soundAfterHonestCommitmentFor
      (system (atSecondHashFunction (theCppWith (always ρ) (theTwin g) prove)) Z (settingsOfRead pp) Form prv
        parse)
      ((atSecondHashFunction (theCppWith (always ρ) (theTwin g) prove)).extractor Z (settingsOfRead pp))
      (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) (fun t => soundnessErrorInQueries t n)
      (bindingErrorInQueries (twinBudget + 2))
      (((g8bits_cppWith (always ρ) (theTwin g) prove).2 Z pp hs hr).2 Form prv parse n hn)
      (extracts_anyForm (extractsCommitted_at prove g ρ Z pp hr (saltAt_of_live hs hl)) Form prv
        parse)
  | false =>
    refine SoundAfterHonestCommitmentFor.of_rejects _ _ _
      fun hash commitment prompt output form => ?_
    cases h : (VerifierAndGoals.verify (atSecondHashFunction (theCppWith (always ρ) (theTwin g) prove)) Z parse commitment
        prompt output form).evaluate hash with
    | false => exact h
    | true =>
      have hy := live_of_accept_D₀ Z parse hash commitment prompt output form h
      rw [hl] at hy
      exact absurd hy Bool.false_ne_true

end Bind.Cpp

end

#print axioms Bind.Cpp.extractsCommitted_at
#print axioms Bind.Cpp.soundAtCommitted_at
