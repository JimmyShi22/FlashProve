-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Bind/LiveAtNamed.lean: AT THE LIBRARY's WRITTEN COPIES OF THE TWO STORED SETS OF PUBLIC
FILES (storedPublicFiles, zGap: Ladder/Stored.lean) THE DESCRIPTION's TEST protocolDataWellFormed ON THE PUBLIC FILES PASSES:
SO OF THE TWO ARMS OF SOUNDNESS AFTER AN HONEST COMMITMENT THE LIVE ONE HOLDS THERE, AND THE
STATEMENTS THAT TAKE "protocolDataWellFormed PASSES" AS A PREMISE HAVE MEMBERS; the like at storedPublicFiles's files under
every policy within four bounds. No other premise in any statement.
Every proof here is calls alone, of theorems of other files.
NOTHING HERE SAYS THAT verify ACCEPTS ANY PROOF UNDER A COMMITMENT OF THIS COMMITTER's MAKE. NOTHING
HERE SAYS ANYTHING OF THE RELEASE'S COMMITTING PROGRAM.

Why. Johnson/Bind/Cpp/SoundAtCommitted.lean proves soundness after an honest commitment at every Z
in scope that is read, by cases on protocolDataWellFormed: where it passes, by the tie and soundness; where it
fails, because verify then rejects everything: the poorest of reasons. That theorem does not tell
which arm holds at any files. That protocolDataWellFormed passes at the named files is a theorem of the side
library (theLive_zFull: AtFullSide/Top/LiveAtFull.lean; theLive_zGap, theLive_zAt:
AtFullSide/Top/LiveAtPolicies.lean). Here the two are said in one statement, so that a reader sees
by theorem that the dead arm is not the one that holds there.

Main names (namespace AtFullSide.Tie).
  `premises_zFull`, `premises_zGap`: in scope, read, protocolDataWellFormed passes: the three premises of
    extractsCommitted and bindsAt (Johnson/Bind/Cpp/TheTie.lean) hold together: these have members.
  `extractsCommitted_called_…`, `bindsAt_called_…`, `policy_and_binding_called_zGap`: these theorems
    called there. Each is the same statement as its namesake without "_called" in
    AtFullSide/Bind/TheTieAtNamed.lean, which has it without the premise that protocolDataWellFormed passes: by
    another road. So the two files' 41 theorems are 36 different statements.
  **`soundAtCommitted_live_zFull`**, **`soundAtCommitted_live_zGap`**: "protocolDataWellFormed passes" AND the
    form of soundAtCommitted_zFull | _zGap, in one statement.
  `soundAtCommitted_live_own_zFull`, `soundAtCommitted_live_own_zGap`: with the experiment written
    out.
  `soundAtCommitted_live_exact_zFull`: with the claim "is the model's output"
    (Johnson/Bind/Cpp/SoundAtCommittedExact.lean).
  **`soundAtCommitted_live_zAt`**, `soundAtCommitted_live_own_zAt`: the same at zAt C theta cap
    (Johnson/Goal/Files/ScopeAtPolicies.lean: storedPublicFiles's files under the policy of these three
    numbers), under four bounds alone: C < 2^32, theta ≤ C, cap ≤ 1024, 2^8 ≤ theta.
Limits. ALL LIMITS OF SoundAtCommitted.lean, SoundAtCommittedExact.lean, TheTie.lean AND
TheTieAtNamed.lean TRAVEL WHOLE, BUT THE ONE ON WHICH ARM HOLDS AT THE NAMED FILES; and those of
AtFullSide/Top/LiveAtFull.lean and LiveAtPolicies.lean. By reference alone, to be read in these
files' heads, among them: the stored example's weights are synthetic; protocolDataWellFormed is taken at the
format's second hash function by name and at a constant in the digest's place; all is at the full
size's shape, where this committer can never be run; soundness stands on files on coding theory
adapted from third-party Lean (lean/LIMITS.md, L15).
- ALL FOURTEEN HANG ON "protocolDataWellFormed PASSES AT storedPublicFiles", another file's theorem (theLive_zFull,
  AtFullSide/Top/LiveAtFull.lean): what it rests on stands in that file's head.
- Where files of Johnson/Bind/ and that folder's README.md say "evaluated, not proved", "is no
  theorem" or "which arm holds is not told" of SaltAt, or of "protocolDataWellFormed passes", at the two stored
  copies, that is true OF THE MAIN LIBRARY: the leaves of this side library are where it is a
  theorem.
- protocolDataWellFormed IS A TEST ON THE PUBLIC FILES: that it passes says that verify does not reject everything
  for that test's sake. verify makes further tests on these files (InScope is one, and is a conjunct
  of ten of the fourteen); that protocolDataWellFormed and these are all of them is no theorem. IT IS NO ACCEPT:
  nothing says that verify accepts any proof at these files, under any commitment. If verify
  accepted none under this committer's commitments, the form would hold for that reason too: it is
  no test of the committer (hollow_meets_join, Johnson/Bind/Cpp/JoinControls.lean).
- THIS FILE LIES IN THE SIDE LIBRARY AtFullSide, outside the main library, as the proof that protocolDataWellFormed
  passes does.
- AT THE PUBLIC FILES AS Ladder/Stored.lean SPELLS THEM: no Lean ties these terms to the top-level
  example folders. At storedPublicFiles, zGap and zAt C theta cap alone. That the policy which the reader
  returns at zAt C theta cap is (C, theta, cap) is not said here. Some policies within the four
  bounds leave every counted token free (theta = C with cap = 1,024: the docstring of InScope,
  Ladder.lean): there the claim "meets the files' policy" says little. And where 257 ≤ theta and
  257 ≤ C (zGap's policy is such) every well-formed request meets the policy at the all-zero weights
  (the head of Ladder.lean, 6): at such weights the forms on the policy forbid nothing.
- The generator g and the prover are parameters: every theorem here holds at every g and every
  prover and reads nothing of either. No completeness, no index privacy (hiding of the weights). No
  figure here is 128 bits: the error of the forms on soundness after an honest commitment, soundnessErrorInQueries (c +
  p) n + bindingErrorInQueries (2^35 + 2), is 124 bits per query of the prover, never below about 2^-88 at the
  committer's own count c = 2^35 + 2.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.SoundAtCommittedExact
import AtFullSide.Bind.TheTieAtNamed
import AtFullSide.Top.LiveAtPolicies

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace AtFullSide.Tie
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Bind.Cpp
open _root_.Bind.Twin (Shape Table)

/- Lean compares these by their names. -/
attribute [local irreducible] _root_.Bind.Twin.twinID _root_.Bind.Twin.calls
  _root_.Bind.Cpp.shapeFull _root_.Bind.Cpp.twinBudget _root_.Bind.Cpp.theTwin theCoding theKeyData
  theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate theProvers theNamed
  LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan FlashProve.theItem
  LayoutsByPublicReading.commitAtCoins storedPublicFiles zGap zAt

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-! ## The statements that take "protocolDataWellFormed passes" as a premise have members -/

/-- **In scope, read, protocolDataWellFormed passes: together, at storedPublicFiles.** -/
theorem premises_zFull :
    InScope storedPublicFiles = true ∧ (∃ pp, readFiles storedPublicFiles = .ok pp) ∧ protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true :=
  let ⟨sc, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨sc, ⟨pp, hr⟩, AtFullSide.Top.theLive_zFull⟩

/-- extractsCommitted (Johnson/Bind/Cpp/TheTie.lean), called at storedPublicFiles: the same statement as
extractsCommitted_zFull in TheTieAtNamed.lean, by another road. -/
theorem extractsCommitted_called_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      ExtractsCommittedWeights
        (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor storedPublicFiles (settingsOfRead pp))
        (bindingErrorInQueries (twinBudget + 2)) :=
  let ⟨sc, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, extractsCommitted prove g storedPublicFiles pp sc hr AtFullSide.Top.theLive_zFull⟩

/-- bindsAt (Johnson/Bind/Cpp/TheTie.lean), called at storedPublicFiles: the same statement as bindsAt_zFull in
TheTieAtNamed.lean, by another road. -/
theorem bindsAt_called_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit storedPublicFiles (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor storedPublicFiles (settingsOfRead pp)) bindingErrorInQueries :=
  let ⟨sc, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, bindsAt prove g storedPublicFiles pp sc hr AtFullSide.Top.theLive_zFull⟩

/-- **In scope, read, protocolDataWellFormed passes: together, at zGap.** -/
theorem premises_zGap :
    InScope zGap = true ∧ (∃ pp, readFiles zGap = .ok pp) ∧ protocolDataWellFormed (asDescriptionFiles zGap) = true :=
  let ⟨sc, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨sc, ⟨pp, hr⟩, AtFullSide.Top.theLive_zGap⟩

/-- extractsCommitted (Johnson/Bind/Cpp/TheTie.lean), called at zGap: the same statement as
extractsCommitted_zGap in TheTieAtNamed.lean, by another road. -/
theorem extractsCommitted_called_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles zGap = .ok pp ∧
      ExtractsCommittedWeights
        (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) zGap (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor zGap (settingsOfRead pp))
        (bindingErrorInQueries (twinBudget + 2)) :=
  let ⟨sc, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, hr, extractsCommitted prove g zGap pp sc hr AtFullSide.Top.theLive_zGap⟩

/-- bindsAt (Johnson/Bind/Cpp/TheTie.lean), called at zGap: the same statement as bindsAt_zGap in
TheTieAtNamed.lean, by another road. -/
theorem bindsAt_called_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles zGap = .ok pp ∧
      (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit zGap (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) zGap (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor zGap (settingsOfRead pp)) bindingErrorInQueries :=
  let ⟨sc, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, hr, bindsAt prove g zGap pp sc hr AtFullSide.Top.theLive_zGap⟩

/-- policy_and_binding_at_zGap (Johnson/Bind/Cpp/TheTie.lean), called: the same statement as
policy_and_binding_zGap in TheTieAtNamed.lean, by another road. -/
theorem policy_and_binding_called_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    InScope zGap = true ∧ ∃ pp, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩ ∧
      (∀ (Form : Type)
        (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
          List Token → List Token → RandomizedAlgorithm Form)
        (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) zGap Form) (n : ℕ), parse.Within n →
        SoundForWith
          (system (atSecondHashFunction (theCpp (theTwin g) prove)) zGap (settingsOfRead pp) Form prv parse)
          ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor zGap (settingsOfRead pp))
          (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) fun t => soundnessErrorInQueries t n) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) zGap (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor zGap (settingsOfRead pp)) bindingErrorInQueries :=
  policy_and_binding_at_zGap prove g AtFullSide.Top.theLive_zGap

/-! ## Which arm holds: the live one -/

/-- **AT storedPublicFiles protocolDataWellFormed PASSES, AND SOUNDNESS AFTER AN HONEST COMMITMENT HOLDS**: so of the two arms
of soundAtCommitted (Johnson/Bind/Cpp/SoundAtCommitted.lean) the live one is the one that holds
there: it is not by the dead arm (protocolDataWellFormed fails, so verify rejects everything) that the statement is
had there. -/
theorem soundAtCommitted_live_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true ∧
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
  ⟨AtFullSide.Top.theLive_zFull, soundAtCommitted_zFull prove g⟩

/-- **The same at zGap**, whose policy is (25856, 512, 1). -/
theorem soundAtCommitted_live_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    protocolDataWellFormed (asDescriptionFiles zGap) = true ∧
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
  ⟨AtFullSide.Top.theLive_zGap, soundAtCommitted_zGap prove g⟩

/-- **The same with the experiment written out**, at the description's own form and parser and the
committer's own count, at storedPublicFiles. -/
theorem soundAtCommitted_live_own_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true ∧
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
  ⟨AtFullSide.Top.theLive_zFull, soundAtCommitted_own_zFull prove g⟩

/-- **The same with the experiment written out**, at zGap. -/
theorem soundAtCommitted_live_own_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    protocolDataWellFormed (asDescriptionFiles zGap) = true ∧
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
  ⟨AtFullSide.Top.theLive_zGap, soundAtCommitted_own_zGap prove g⟩

/-- **The same with the claim "is the model's output"**, in both forms, at storedPublicFiles, which states exact
match. -/
theorem soundAtCommitted_live_exact_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true ∧
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
  ⟨AtFullSide.Top.theLive_zFull, soundAtCommitted_exact_zFull prove g⟩

/-- **The same at storedPublicFiles's files under every policy within the four bounds**: protocolDataWellFormed passes, the
files are in scope and read, and soundness after an honest commitment holds for the policy that the
files state. -/
theorem soundAtCommitted_live_zAt (g : Shape → Seed → Digest → Digest → Coins) {C theta cap : ℕ}
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    protocolDataWellFormed (asDescriptionFiles (zAt C theta cap)) = true ∧ InScope (zAt C theta cap) = true ∧
      ∃ pp, readFiles (zAt C theta cap) = .ok pp ∧
      ∀ (Form : Type)
        (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp (theTwin g) prove)).Rand →
          List Token → List Token → RandomizedAlgorithm Form)
        (parse : Parser (atSecondHashFunction (theCpp (theTwin g) prove)) (zAt C theta cap) Form) (n : ℕ),
        parse.Within n →
        SoundAfterHonestCommitmentFor
          (system (atSecondHashFunction (theCpp (theTwin g) prove)) (zAt C theta cap) (settingsOfRead pp) Form
            prv parse)
          (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
          fun committerQueries proverQueries =>
            soundnessErrorInQueries (committerQueries + proverQueries) n + bindingErrorInQueries (twinBudget + 2) :=
  let ⟨pp, hr⟩ := read_zAt h1 h2 h3 h4
  ⟨AtFullSide.Top.theLive_zAt h1 h2 h3 h4, VerifierAndGoals.inScope_zAt h1 h2 h3 h4, pp, hr,
    fun Form prv parse n hn =>
      soundAtCommitted prove g _ pp (VerifierAndGoals.inScope_zAt h1 h2 h3 h4) hr Form prv parse n hn⟩

/-- **The same with the experiment written out**, there. -/
theorem soundAtCommitted_live_own_zAt (g : Shape → Seed → Digest → Digest → Coins) {C theta cap : ℕ}
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    protocolDataWellFormed (asDescriptionFiles (zAt C theta cap)) = true ∧ InScope (zAt C theta cap) = true ∧
      ∃ pp, readFiles (zAt C theta cap) = .ok pp ∧
      ∀ (w : ModelWeights (settingsOfRead pp)) (p : ℕ)
        (prover : Commitment → Rand → RandomizedAlgorithm (List Token × List Token × flashProveDescription.Form)),
        (∀ commitment ρ, (prover commitment ρ).QueryBound p) →
        Prob (do
            let ρ ← (atSecondHashFunction (theCpp (theTwin g) prove)).sample
            let commitment ←
              ((atSecondHashFunction (theCpp (theTwin g) prove)).commit (zAt C theta cap) (settingsOfRead pp) w
                ρ).toRandomized
            let (prompt, output, form) ← prover commitment ρ
            let accepted ←
              (VerifierAndGoals.verify (atSecondHashFunction (theCpp (theTwin g) prove)) (zAt C theta cap)
                ((atSecondHashFunction (theCpp (theTwin g) prove)).parse (zAt C theta cap)) commitment prompt
                output form).toRandomized
            pure (prompt, output, accepted))
          {(prompt, output, accepted) | accepted = true ∧
            ¬ Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output}
          ≤ soundnessErrorInQueries (twinBudget + 2 + p) 1 + bindingErrorInQueries (twinBudget + 2) :=
  let ⟨pp, hr⟩ := read_zAt h1 h2 h3 h4
  ⟨AtFullSide.Top.theLive_zAt h1 h2 h3 h4, VerifierAndGoals.inScope_zAt h1 h2 h3 h4, pp, hr,
    fun w p prover hp =>
      soundAtCommitted_own prove g _ pp (VerifierAndGoals.inScope_zAt h1 h2 h3 h4) hr w p prover hp⟩

end AtFullSide.Tie

end

#print axioms AtFullSide.Tie.premises_zFull
#print axioms AtFullSide.Tie.extractsCommitted_called_zFull
#print axioms AtFullSide.Tie.bindsAt_called_zFull
#print axioms AtFullSide.Tie.premises_zGap
#print axioms AtFullSide.Tie.extractsCommitted_called_zGap
#print axioms AtFullSide.Tie.bindsAt_called_zGap
#print axioms AtFullSide.Tie.policy_and_binding_called_zGap
#print axioms AtFullSide.Tie.soundAtCommitted_live_zFull
#print axioms AtFullSide.Tie.soundAtCommitted_live_zGap
#print axioms AtFullSide.Tie.soundAtCommitted_live_own_zFull
#print axioms AtFullSide.Tie.soundAtCommitted_live_own_zGap
#print axioms AtFullSide.Tie.soundAtCommitted_live_exact_zFull
#print axioms AtFullSide.Tie.soundAtCommitted_live_zAt
#print axioms AtFullSide.Tie.soundAtCommitted_live_own_zAt
