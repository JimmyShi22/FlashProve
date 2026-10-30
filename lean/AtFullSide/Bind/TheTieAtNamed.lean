-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Bind/TheTieAtNamed.lean: THE TIE AND WHAT FOLLOWS FROM IT, AT THE LIBRARY's WRITTEN
COPIES OF THE TWO STORED SETS OF PUBLIC FILES (storedPublicFiles, zGap: Ladder/Stored.lean), WITH NO PREMISE AT
ALL; and at storedPublicFiles's files under every policy within four bounds. Every proof here but
read_of_inScope's (six lines on InScope's text) is calls alone, of theorems of other files or of
this one.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
The extractor is that of the theorem on soundness (cpp_is_of_verify, Johnson/Bind/Cpp/OfTie.lean);
it picks by choice: it is no algorithm.
"The opening form" is BindsWith (VerifiableInference/MoreStatements.lean): nobody opens a
commitment, by naming weights and randomness from which the committer gives it, to weights that the
extractor does not give; at fixed randomness it yields that the extractor gives the committed
weights back (BindsWith.atRandomness).

Why. Johnson/Bind/Cpp/TheTie.lean and TwinFeels.lean prove their statements at every Z that is read
and whose frame has salts of 40 bytes (SaltAt Z). Both facts are theorems at storedPublicFiles and at zGap:
"read" is VerifierAndGoals.filesRead (Johnson/Goal/Files/FilesReadProof.lean), by which both are in scope too;
SaltAt is AtFullSide.Planner.saltAt_zFull and saltAt_zGap (AtFullSide/Planner/SaltAtFull.lean). So
these statements have members by theorems alone.

Main names (namespace AtFullSide.Tie), each at storedPublicFiles and at zGap:
  tieKeyAt_…, tieAt_…: the tie at the key and at the commitment ID.
  **extractsCommitted_…**: correctness of extraction (ExtractsCommittedWeights).
  **bindsAt_…**: the body of G9bits: the opening form (BindsWith) at bindingErrorInQueries.
  noTwoOpenings_…: nobody opens one commitment ID to two different weights.
  extracts_…: correctness of extraction at every randomness, at both errors.
  **commit_parts_weights_…**: the commit field's value feels the weights: any two different weights,
    at every seed or coins, are parted by some hash function. commit_feels_weights_…,
    twin_not_blindAt_…: weaker forms, which say less (their docstrings).
  At zAt C theta cap (Johnson/Goal/Files/ScopeAtPolicies.lean: storedPublicFiles's files under the policy of
  these three numbers), UNDER FOUR BOUNDS ALONE: C < 2^32, theta ≤ C, cap ≤ 1024, 2^8 ≤ theta:
  tieAt_zAt, read_zAt, extractsCommitted_zAt, bindsAt_zAt, noTwoOpenings_zAt,
  commit_parts_weights_zAt. Under these bounds the files are in scope (VerifierAndGoals.inScope_zAt, the same
  file), and files in scope are read (`read_of_inScope`, by InScope's text). At (25856, 512, 1)
  these files are zGap (VerifierAndGoals.zGap_eq, the same file); at (256, 256, 0) they are storedPublicFiles, by
  unfolding: no theorem says it.
  And: `twin_not_blind_named`; **`policy_and_binding_zGap`**: at zGap, soundness under the files'
  policy and the opening form at one description and one extractor: a conjunction, no join.
"There is pp with readFiles Z = .ok pp" stands in the statements because the settings of the weights
are what the reader returns.

Limits. ALL LIMITS OF Johnson/Bind/Cpp/TheTie.lean TRAVEL WHOLE BUT THE ONE ON THE MEMBER (by
reference alone, to be read in that file's head: THE KEY FILE, THE SHAPE, the seed's road, the
format's second hash function, WHAT THE TIE CANNOT SEE), AND THOSE OF TwinFeels.lean: "parted by
some hash function" names no hash function and counts none; this is not the proposition Feels
(Johnson/Bind/Cpp/Guards.lean). No index privacy (hiding of the weights),
no completeness. THIS IS NOT G9bits: it does not reach all files in scope that are read. It is none
of the goals of Ladder.lean and Ladder/Bits.lean: no goal is stated here. THE
VERIFIER IS IDLE: nothing says that verify accepts a proof under a commitment of this committer's
make. How weights become the table's entries is the library's own (entryOf); that it is the
programs' is compared nowhere. At this shape the running committer (Johnson/Bind/Twin.lean:
executable text, run at small shapes alone) cannot be run (about 2^72 multiplications): what has
been run are small shapes. The public files are fixed before the hash function is sampled. No figure
here is 128 bits: bindingErrorInQueries t is 124 bits per hash query, never below about 2^-101.
Beside these:
- 25 OF THE 27 HANG ON ONE THEOREM OF ANOTHER FILE, saltAt_zFull
  (AtFullSide/Planner/SaltAtFull.lean): saltAt_zGap and saltAt_zAt are had from it, and all but
  read_of_inScope and read_zAt call one of the three (twin_not_blind_named through a neighbour). The
  six at zAt hang on Johnson/Goal/Files/ScopeAtPolicies.lean too.
- THE MEMBER. Of the forms under SaltAt, members are shown here by theorems alone, at these two sets
  of files and at zAt C theta cap under the four bounds: never "at all files in scope". Of
  extractsCommitted, bindsAt and policy_and_binding_at_zGap in TheTie.lean, which take as a premise
  that the description's test protocolDataWellFormed on the public files passes, members are shown in
  AtFullSide/Bind/LiveAtNamed.lean: that protocolDataWellFormed passes at these files is a theorem of the side
  library (AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean). "THE PLANNER RETURNS" (what SaltAt
  says) IS NOT "protocolDataWellFormed PASSES": the forms here need the first alone. Their conclusions at storedPublicFiles and
  zGap are had here without the second. Where protocolDataWellFormed fails, verify accepts nothing
  (rejects_of_dead, Johnson/Bind/Cpp/SoundAtCommitted.lean), and the first half of
  policy_and_binding_zGap is idle (at zGap it passes: LiveAtNamed.lean).
- THIS FILE LIES IN THE SIDE LIBRARY AtFullSide, outside the main library, as the proofs of SaltAt
  at the named files do.
- Where files of Johnson/Bind/ and that folder's README.md say "evaluated, not proved" or "is no
  theorem" of SaltAt, or of "protocolDataWellFormed passes", at the two stored copies, that is true OF THE MAIN
  LIBRARY: the leaves of this side library are where it is a theorem.
- AT THE PUBLIC FILES AS Ladder/Stored.lean SPELLS THEM: no Lean ties these terms to the top-level
  example folders. They are the files of an example of which that file's head says: "The example's
  weights are synthetic". The theorems hold at all weights of the settings that the reader returns.
- THE POLICY AT zGap AND AT zAt. Where 257 ≤ theta and 257 ≤ C (zGap's policy is such) the part on
  policies, alone, is met by an extractor that always returns the all-zero weights and a verifier
  that only tests the form of a request; and a committer may itself commit to such weights (the head
  of Ladder.lean, 6). The second half of policy_and_binding_zGap rules that extractor out for
  commitments of this committer's make, and for no other.
- The running committer is a model of one part of the committing program. No theorem ties it to
  the program. Evaluations have compared it with runs of the program at the small stored example's
  public files, on synthetic weights, and nowhere else; what was compared, and what was not, stands
  in Johnson/Bind/README.md ("What is run, not proved").
- The generator g and the prover are parameters: every theorem here holds at every g and every
  prover and reads nothing of either; a constant g passes.
Terms: lean/TERMS.md, lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.TheTie
import Johnson.Bind.Cpp.TwinFeels
import AtFullSide.Planner.SaltAtFull

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

/-! ## At storedPublicFiles -/

/-- **The tie at the key, at storedPublicFiles.** -/
theorem tieKeyAt_zFull : TieKeyAt storedPublicFiles := tieKeyAt storedPublicFiles AtFullSide.Planner.saltAt_zFull

/-- **The tie, at storedPublicFiles.** The statement does not read the generator g. -/
theorem tieAt_zFull (g : Shape → Seed → Digest → Digest → Coins) : TieAt (theTwin g) storedPublicFiles :=
  tieAt storedPublicFiles AtFullSide.Planner.saltAt_zFull g

/-- **Correctness of extraction for the committer of theCpp (theTwin g), at storedPublicFiles.** The error,
bindingErrorInQueries (2^35 + 2), is about 2^-89. -/
theorem extractsCommitted_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      ExtractsCommittedWeights
        (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor storedPublicFiles (settingsOfRead pp))
        (bindingErrorInQueries (twinBudget + 2)) :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, extractsCommitted_salt prove g storedPublicFiles pp hr AtFullSide.Planner.saltAt_zFull⟩

/-- **The body of G9bits, at storedPublicFiles**: the committer's count, and the opening form at bindingErrorInQueries
(bindingErrorInQueries t: 124 bits per hash query, never below about 2^-101). This is not G9bits: the goal
asks it at all files in scope that are read. -/
theorem bindsAt_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit storedPublicFiles (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor storedPublicFiles (settingsOfRead pp)) bindingErrorInQueries :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, bindsAt_salt prove g storedPublicFiles pp hr AtFullSide.Planner.saltAt_zFull⟩

/-- **Nobody opens one commitment ID to two different weights, at storedPublicFiles**, but with probability
2 · bindingErrorInQueries t. -/
theorem noTwoOpenings_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      NoTwoOpenings (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) storedPublicFiles (settingsOfRead pp))
        fun t => 2 * bindingErrorInQueries t :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, noTwoOpenings_salt prove g storedPublicFiles pp hr AtFullSide.Planner.saltAt_zFull⟩

/-- **Correctness of extraction at every randomness, at storedPublicFiles**: at bindingErrorInQueries (2^35 + 2), and at
the written committer's own square form, about 2^-156. -/
theorem extracts_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧ ∀ (w : ModelWeights (settingsOfRead pp)) (ρ : Rand),
      Prob ((atSecondHashFunction (theCpp (theTwin g) prove)).commit storedPublicFiles (settingsOfRead pp) w
          ρ).toRandomized.withQueryLog
          {o | (atSecondHashFunction (theCpp (theTwin g) prove)).extractor storedPublicFiles (settingsOfRead pp) o.1 o.2 ≠
            some w}
        ≤ bindingErrorInQueries (twinBudget + 2) ∧
      Prob ((atSecondHashFunction (theCpp (theTwin g) prove)).commit storedPublicFiles (settingsOfRead pp) w
          ρ).toRandomized.withQueryLog
          {o | (atSecondHashFunction (theCpp (theTwin g) prove)).extractor storedPublicFiles (settingsOfRead pp) o.1 o.2 ≠
            some w}
        ≤ epsBind honestBudget (twinBudget + 2 + 2) :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, fun w ρ => ⟨extracts_salt prove g storedPublicFiles pp hr AtFullSide.Planner.saltAt_zFull w ρ,
    extracts_square_salt prove g storedPublicFiles pp hr AtFullSide.Planner.saltAt_zFull w ρ⟩⟩

/-- **The commit field's value feels the weights at the full size, at storedPublicFiles**: any two different
weights, at every seed or coins, are parted by some hash function. -/
theorem commit_parts_weights_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      ∀ (w w' : ModelWeights (settingsOfRead pp)), w ≠ w' → ∀ ρ : Rand,
        ¬ ∀ hash : Hash, (cppCommit (theTwin g) storedPublicFiles (settingsOfRead pp) w ρ).evaluate hash =
          (cppCommit (theTwin g) storedPublicFiles (settingsOfRead pp) w' ρ).evaluate hash :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, fun w w' hne ρ =>
    commit_parts_weights g storedPublicFiles pp hr AtFullSide.Planner.saltAt_zFull w w' hne ρ⟩

/-- So its value is not one and the same at all weights, at storedPublicFiles. -/
theorem commit_feels_weights_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      ¬ ∀ (w w' : ModelWeights (settingsOfRead pp)) (ρ : Rand) (hash : Hash),
        (cppCommit (theTwin g) storedPublicFiles (settingsOfRead pp) w ρ).evaluate hash =
          (cppCommit (theTwin g) storedPublicFiles (settingsOfRead pp) w' ρ).evaluate hash :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨pp, hr, commit_feels_weights g storedPublicFiles pp hr AtFullSide.Planner.saltAt_zFull⟩

/-- At the full size's shape and storedPublicFiles's files the running committer is not blind to the table's
plain entries: some two tables with the same coins give two algorithms. The strong form is
commit_parts_weights_zFull. -/
theorem twin_not_blindAt_zFull (g : Shape → Seed → Digest → Digest → Coins) :
    ¬ BlindAt (theTwin g) _root_.Bind.Cpp.shapeFull storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  twin_not_blindAt g storedPublicFiles pp hr AtFullSide.Planner.saltAt_zFull

/-! ## At zGap -/

/-- **The tie at the key, at zGap.** -/
theorem tieKeyAt_zGap : TieKeyAt zGap := tieKeyAt zGap AtFullSide.Planner.saltAt_zGap

/-- **The tie, at zGap.** The statement does not read the generator g. -/
theorem tieAt_zGap (g : Shape → Seed → Digest → Digest → Coins) : TieAt (theTwin g) zGap :=
  tieAt zGap AtFullSide.Planner.saltAt_zGap g

/-- **Correctness of extraction for the committer of theCpp (theTwin g), at zGap.** The error,
bindingErrorInQueries (2^35 + 2), is about 2^-89. -/
theorem extractsCommitted_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles zGap = .ok pp ∧
      ExtractsCommittedWeights
        (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) zGap (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor zGap (settingsOfRead pp))
        (bindingErrorInQueries (twinBudget + 2)) :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, hr, extractsCommitted_salt prove g zGap pp hr AtFullSide.Planner.saltAt_zGap⟩

/-- **The body of G9bits, at zGap**: the committer's count, and the opening form at bindingErrorInQueries
(bindingErrorInQueries t: 124 bits per hash query, never below about 2^-101). This is not G9bits: the goal
asks it at all files in scope that are read. -/
theorem bindsAt_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles zGap = .ok pp ∧
      (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit zGap (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) zGap (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor zGap (settingsOfRead pp)) bindingErrorInQueries :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, hr, bindsAt_salt prove g zGap pp hr AtFullSide.Planner.saltAt_zGap⟩

/-- **Nobody opens one commitment ID to two different weights, at zGap**, but with probability
2 · bindingErrorInQueries t. -/
theorem noTwoOpenings_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles zGap = .ok pp ∧
      NoTwoOpenings (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) zGap (settingsOfRead pp))
        fun t => 2 * bindingErrorInQueries t :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, hr, noTwoOpenings_salt prove g zGap pp hr AtFullSide.Planner.saltAt_zGap⟩

/-- **Correctness of extraction at every randomness, at zGap**: at bindingErrorInQueries (2^35 + 2), and at
the written committer's own square form, about 2^-156. -/
theorem extracts_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles zGap = .ok pp ∧ ∀ (w : ModelWeights (settingsOfRead pp)) (ρ : Rand),
      Prob ((atSecondHashFunction (theCpp (theTwin g) prove)).commit zGap (settingsOfRead pp) w
          ρ).toRandomized.withQueryLog
          {o | (atSecondHashFunction (theCpp (theTwin g) prove)).extractor zGap (settingsOfRead pp) o.1 o.2 ≠
            some w}
        ≤ bindingErrorInQueries (twinBudget + 2) ∧
      Prob ((atSecondHashFunction (theCpp (theTwin g) prove)).commit zGap (settingsOfRead pp) w
          ρ).toRandomized.withQueryLog
          {o | (atSecondHashFunction (theCpp (theTwin g) prove)).extractor zGap (settingsOfRead pp) o.1 o.2 ≠
            some w}
        ≤ epsBind honestBudget (twinBudget + 2 + 2) :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, hr, fun w ρ => ⟨extracts_salt prove g zGap pp hr AtFullSide.Planner.saltAt_zGap w ρ,
    extracts_square_salt prove g zGap pp hr AtFullSide.Planner.saltAt_zGap w ρ⟩⟩

/-- **The commit field's value feels the weights at the full size, at zGap**: any two different
weights, at every seed or coins, are parted by some hash function. -/
theorem commit_parts_weights_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles zGap = .ok pp ∧
      ∀ (w w' : ModelWeights (settingsOfRead pp)), w ≠ w' → ∀ ρ : Rand,
        ¬ ∀ hash : Hash, (cppCommit (theTwin g) zGap (settingsOfRead pp) w ρ).evaluate hash =
          (cppCommit (theTwin g) zGap (settingsOfRead pp) w' ρ).evaluate hash :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, hr, fun w w' hne ρ =>
    commit_parts_weights g zGap pp hr AtFullSide.Planner.saltAt_zGap w w' hne ρ⟩

/-- So its value is not one and the same at all weights, at zGap. -/
theorem commit_feels_weights_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ∃ pp, readFiles zGap = .ok pp ∧
      ¬ ∀ (w w' : ModelWeights (settingsOfRead pp)) (ρ : Rand) (hash : Hash),
        (cppCommit (theTwin g) zGap (settingsOfRead pp) w ρ).evaluate hash =
          (cppCommit (theTwin g) zGap (settingsOfRead pp) w' ρ).evaluate hash :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  ⟨pp, hr, commit_feels_weights g zGap pp hr AtFullSide.Planner.saltAt_zGap⟩

/-- At the full size's shape and zGap's files the running committer is not blind to the table's
plain entries: some two tables with the same coins give two algorithms. The strong form is
commit_parts_weights_zGap. -/
theorem twin_not_blindAt_zGap (g : Shape → Seed → Digest → Digest → Coins) :
    ¬ BlindAt (theTwin g) _root_.Bind.Cpp.shapeFull zGap.pol zGap.lay zGap.KL :=
  let ⟨_, pp, hr, _⟩ := VerifierAndGoals.filesRead.other
  twin_not_blindAt g zGap pp hr AtFullSide.Planner.saltAt_zGap

/-! ## At storedPublicFiles's files under every policy within four bounds

`zAt C theta cap` (Johnson/Goal/Files/ScopeAtPolicies.lean) is storedPublicFiles with these three numbers as its
policy. Under the four bounds it is in scope (VerifierAndGoals.inScope_zAt), so it is read. -/

/-- **Files in scope are read**: by its text InScope is false where the reader rejects. -/
theorem read_of_inScope {Z : PublicFiles} (h : InScope Z = true) : ∃ pp, readFiles Z = .ok pp := by
  unfold InScope at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  split at h2
  · exact ⟨_, by assumption⟩
  · cases h2

/-- storedPublicFiles's files under a policy within the four bounds are read. -/
theorem read_zAt {C theta cap : ℕ}
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    ∃ pp, readFiles (zAt C theta cap) = .ok pp :=
  read_of_inScope (VerifierAndGoals.inScope_zAt h1 h2 h3 h4)

/-- **The tie, at storedPublicFiles's files under a policy within the four bounds.** -/
theorem tieAt_zAt (g : Shape → Seed → Digest → Digest → Coins) {C theta cap : ℕ}
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    TieAt (theTwin g) (zAt C theta cap) :=
  tieAt _ (AtFullSide.Planner.saltAt_zAt h1 h2 h3 h4) g

/-- **Correctness of extraction there.** -/
theorem extractsCommitted_zAt (g : Shape → Seed → Digest → Digest → Coins) {C theta cap : ℕ}
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    ∃ pp, readFiles (zAt C theta cap) = .ok pp ∧
      ExtractsCommittedWeights
        (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) (zAt C theta cap) (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor (zAt C theta cap) (settingsOfRead pp))
        (bindingErrorInQueries (twinBudget + 2)) :=
  let ⟨pp, hr⟩ := read_zAt h1 h2 h3 h4
  ⟨pp, hr, extractsCommitted_salt prove g _ pp hr (AtFullSide.Planner.saltAt_zAt h1 h2 h3 h4)⟩

/-- **The body of G9bits there.** This is not G9bits: the goal asks it at all files in scope that
are read. -/
theorem bindsAt_zAt (g : Shape → Seed → Digest → Digest → Coins) {C theta cap : ℕ}
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    ∃ pp, readFiles (zAt C theta cap) = .ok pp ∧
      (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit (zAt C theta cap) (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith
        (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) (zAt C theta cap) (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor (zAt C theta cap) (settingsOfRead pp))
        bindingErrorInQueries :=
  let ⟨pp, hr⟩ := read_zAt h1 h2 h3 h4
  ⟨pp, hr, bindsAt_salt prove g _ pp hr (AtFullSide.Planner.saltAt_zAt h1 h2 h3 h4)⟩

/-- **Nobody opens one commitment ID to two different weights there**, but with probability
2 · bindingErrorInQueries t. -/
theorem noTwoOpenings_zAt (g : Shape → Seed → Digest → Digest → Coins) {C theta cap : ℕ}
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    ∃ pp, readFiles (zAt C theta cap) = .ok pp ∧
      NoTwoOpenings
        (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) (zAt C theta cap) (settingsOfRead pp))
        fun t => 2 * bindingErrorInQueries t :=
  let ⟨pp, hr⟩ := read_zAt h1 h2 h3 h4
  ⟨pp, hr, noTwoOpenings_salt prove g _ pp hr (AtFullSide.Planner.saltAt_zAt h1 h2 h3 h4)⟩

/-- **The commit field's value feels the weights there**: any two different weights, at every seed
or coins, are parted by some hash function. -/
theorem commit_parts_weights_zAt (g : Shape → Seed → Digest → Digest → Coins) {C theta cap : ℕ}
    (h1 : C < 2 ^ 32) (h2 : theta ≤ C) (h3 : cap ≤ 1024) (h4 : 2 ^ 8 ≤ theta) :
    ∃ pp, readFiles (zAt C theta cap) = .ok pp ∧
      ∀ (w w' : ModelWeights (settingsOfRead pp)), w ≠ w' → ∀ ρ : Rand,
        ¬ ∀ hash : Hash,
          (cppCommit (theTwin g) (zAt C theta cap) (settingsOfRead pp) w ρ).evaluate hash =
            (cppCommit (theTwin g) (zAt C theta cap) (settingsOfRead pp) w' ρ).evaluate hash :=
  let ⟨pp, hr⟩ := read_zAt h1 h2 h3 h4
  ⟨pp, hr, fun w w' hne ρ =>
    commit_parts_weights g _ pp hr (AtFullSide.Planner.saltAt_zAt h1 h2 h3 h4) w w' hne ρ⟩

/-! ## Beside them -/

/-- There are a shape and files at which the running committer is not blind: those of
twin_not_blindAt_zFull, of which this is the weaker form. -/
theorem twin_not_blind_named (g : Shape → Seed → Digest → Digest → Coins) : ¬ Blind (theTwin g) :=
  fun hB => twin_not_blindAt_zFull g (hB _root_.Bind.Cpp.shapeFull storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL)

/-- **Both halves at zGap, with no premise.** In scope; read; the policy (25856, 512, 1); but with
probability at most soundnessErrorInQueries t n nobody has an output accepted for which the extractor gives no weights,
or which does not meet that policy at the weights that it gives; and but with probability at most
bindingErrorInQueries t nobody opens a commitment of this committer's make to weights that the same extractor
does not give. A conjunction at one extractor, no join: nothing says that a commitment under which
verify accepts is of this committer's make. Where protocolDataWellFormed fails, verify accepts nothing and the
first half is idle; that it passes at zGap is shown in AtFullSide/Bind/LiveAtNamed.lean. -/
theorem policy_and_binding_zGap (g : Shape → Seed → Digest → Digest → Coins) :
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
  policy_and_binding_at_zGap_cpp (theTwin g) prove (tieAt zGap AtFullSide.Planner.saltAt_zGap g)
    (count_theTwin g zGap)

end AtFullSide.Tie

end

#print axioms AtFullSide.Tie.tieKeyAt_zFull
#print axioms AtFullSide.Tie.tieAt_zFull
#print axioms AtFullSide.Tie.extractsCommitted_zFull
#print axioms AtFullSide.Tie.bindsAt_zFull
#print axioms AtFullSide.Tie.noTwoOpenings_zFull
#print axioms AtFullSide.Tie.extracts_zFull
#print axioms AtFullSide.Tie.commit_parts_weights_zFull
#print axioms AtFullSide.Tie.commit_feels_weights_zFull
#print axioms AtFullSide.Tie.twin_not_blindAt_zFull
#print axioms AtFullSide.Tie.tieKeyAt_zGap
#print axioms AtFullSide.Tie.tieAt_zGap
#print axioms AtFullSide.Tie.extractsCommitted_zGap
#print axioms AtFullSide.Tie.bindsAt_zGap
#print axioms AtFullSide.Tie.noTwoOpenings_zGap
#print axioms AtFullSide.Tie.extracts_zGap
#print axioms AtFullSide.Tie.commit_parts_weights_zGap
#print axioms AtFullSide.Tie.commit_feels_weights_zGap
#print axioms AtFullSide.Tie.twin_not_blindAt_zGap
#print axioms AtFullSide.Tie.read_of_inScope
#print axioms AtFullSide.Tie.read_zAt
#print axioms AtFullSide.Tie.tieAt_zAt
#print axioms AtFullSide.Tie.extractsCommitted_zAt
#print axioms AtFullSide.Tie.bindsAt_zAt
#print axioms AtFullSide.Tie.noTwoOpenings_zAt
#print axioms AtFullSide.Tie.commit_parts_weights_zAt
#print axioms AtFullSide.Tie.twin_not_blind_named
#print axioms AtFullSide.Tie.policy_and_binding_zGap
