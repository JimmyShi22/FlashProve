-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalBindingStatement.lean: binding and extraction at compile's own committer, with the
extractor named.

STATEMENTS ONLY: NOTHING IS PROVED IN THIS FILE. The proof's files: FinalBindingProof.lean of this
folder and what it imports. What the lines say:

With S := compile (flashProveAtFiles files settings part), the compiled system, at one set of public files
and one honest part there (BindingOf S finalExtractor):
  SoundForWith S finalExtractor IsModelOutput finalSoundnessError
  BindsWith S finalExtractor finalOpeningError
  SoundAndBinding S finalBindingError
  SoundOpened S (2 finalBindingError)
  NoTwoOpenings S (2 finalOpeningError)
  ExtractsCommittedWeights S finalExtractor (finalOpeningError N)
FinalBindingGoal: these six, at all public files that the verifier takes and every honest part there
whose tables' salts have one length. FinalBindingLabelled: the same of labelled S label, the system
with a word beside each proof, at every rule for the word: its committer is S's, and its verifier
drops the word.

finalOpeningError q = 3 (q + 8 + 2 * 2^48 + 2)^2 / 2^256: about 2^-156.4 at q = 0, about 2^-155.2 at
q = 2^48, about 2^-126.4 at q = 2^64.
finalBindingError q = max (bits q 2^23) (bindingErrorInQueries q), about q / 2^124 + 2^-100: about 2^-60 at
q = 2^64. That is about 124 bits for each hash query. No figure here is 128 bits.

 1. The committer is compile's own: (compile (flashProveAtFiles files settings part)).commit. It is a Lean
    term; no theorem ties it to a program. compile flashProveAtFiles is no closed term: it stands at public
    files, settings and an honest part.
 2. The commitment has 256 bits: the hash of the first table's root and out-of-domain sample, with
    the part of the public reading that the key's code tells. The key's proofs, the copies and their
    link proofs, so the key file, are not under it.
 3. Binding is stated in the opening form: to open is to name weights and the committer's randomness
    from which the committer gives the commitment. The line says: but for the error nobody opens a
    commitment, whoever made it, to weights that the extractor does not give from the commitment and
    its maker's queries.
 4. The committer's randomness is one number from 0 to coinBound, and every coinBound is let in. Of
    the number the first two digits alone reach the commitment: the first table's encoding
    randomness, and the free bits of its salts behind their public start. So an opener names fewer
    openings than one who may name any coins: nothing is said of an opening at salts with another
    start or another length. At a small coinBound binding says next to nothing: at 0 there is one
    setting of coins. Which number names which coins is fixed by enumerations that are chosen, not
    computed (pickAll): no program runs the committer at a number.
 5. finalExtractor is the extractor of the description of the soundness theorem. It is the one
    extractor of the first, second and sixth line. The third line says only that an extractor
    exists; the fourth and fifth name none.
 6. q counts the queries of whoever made the commitment and of the opener. The committer's own run,
    by which an opening is tested, is not among them, and no line bounds it. What the error prices
    (2^48, twice) is a run of a committer that makes the first table alone; the offline proof, the
    copies and the searches for nonces do not reach the commitment's value.
 7. Extraction is stated on average over the sampled number: from an honest commitment and that
    run's queries the extractor gives the committed weights, but for the error at N, where N bounds
    the committer's own queries on every path. There the honest committer is the maker, so its count
    enters. It searches for nonces, and a search counts at its full limit.
 8. N is a premise. No number is claimed for it here, and no theorem in this file's road says that
    any N meets it, at any honest part. A case is stated in FinalBindingAtTheSettings.lean, which
    stands on another road's count of compile's committer.
 9. The honest part is free but for one law: the salts of a table's leaves have one length, whatever
    the public reading returns (TableSaltsHaveLength). The law reads two letters of the honest part,
    the public start and the number of free bits; compile BUILDS a table's salts of these two, by
    definition (honestSide, Compiler.lean: saltsPre), so it is a law on the salts themselves:
    length_firstSalts (FinalBindingProof.lean). No prover, no search limit, no number of copies and
    no bound on the coins is read. Without that law the lines are not proved; they are not known to
    fail.
10. The six lines ask FilesTaken: in scope, read, at exact match. In scope is narrow: the layout
    file is fixed, and the parameter file but for eight numbers; the scale file is free. They do not
    ask the test on the public files. Where that test fails the verifier rejects all, the lines on soundness are idle,
    and the committer stands over the dead plan and the empty data that the description lays in the
    place of the files' own.
11. The fifth line: nobody opens one commitment to two different weights. Nothing is said of two
    openings to the same weights at different randomness; the committer's two runs are not among q.
    Nothing is said of several commitments, and nothing bounds the extractor's work: it is a function.
12. Who made a commitment is outside these lines. Nothing says that the verifier accepts anything
    under a commitment of this committer's make: that is completeness.
13. In FinalBindingLabelled the word beside a proof is read by no line: a rule that lies meets all
    six.
14. The public files are fixed before the hash function is drawn. The format's second, fixed hash
    function stands inside the description.
-/
import Johnson.Face.FinalStatement
import VerifiableInference.Labelled
import Ladder.FitBinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve VerifierAndGoals.Fit VerifiableInference.OnPublicFiles OnBytes.FrontRoad
open IntegerTransformer (Settings)
open scoped ENNReal

/-! ## 1. The six lines, of any argument system and extractor -/

/-- The error of binding in the opening form: 3 (queries + 8 + 2 * 2^48 + 2)^2 / 2^256. The 8 are
the public reading's queries; 2^48, which stands twice, bounds one run of a committer that makes the
first table alone. -/
abbrev finalOpeningError (queries : ℕ) : ℝ≥0∞ := epsBind honestBudget (queries + 8)

/-- The committer asks at most so many queries, at all weights and randomness, on every path. -/
def CommitterWithin (system : ArgumentSystem) (queries : ℕ) : Prop :=
  ∀ weights randomness, (system.commit weights randomness).toRandomized.QueryBound queries

/-- **Binding and extraction**, of an argument system, at one extractor. -/
structure BindingOf (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) : Prop where
  /-- Soundness, at the extractor. -/
  sound : SoundForWith system extractor system.IsModelOutput finalSoundnessError
  /-- Binding in the opening form, at the same extractor. -/
  binds : BindsWith system extractor finalOpeningError
  /-- The two as the top line has them. -/
  soundAndBinding : SoundAndBinding system finalBindingError
  /-- Soundness for an opened commitment. -/
  soundOpened : SoundOpened system fun queries => 2 * finalBindingError queries
  /-- Nobody opens one commitment to two different weights. -/
  noTwoOpenings : NoTwoOpenings system fun queries => 2 * finalOpeningError queries
  /-- Correctness of extraction, at the same extractor, at every bound on the committer's queries.
  -/
  extracts : ∀ queries, CommitterWithin system queries →
    ExtractsCommittedWeights system extractor (finalOpeningError queries)

/-! ## 2. The extractor, and the one law on the honest part -/

/-- **The extractor**: that of the description of the soundness theorem. From a commitment and its
maker's queries, weights or none. -/
def finalExtractor (files : PublicFiles) (settings : Settings) :
    Commitment → QueryLog → Option (ModelWeights settings) :=
  flashProveDescription.extractor files settings

/-- The salts of a table's leaves, the public start with the free bits, have this length at every
value of the public reading. -/
def TableSaltsHaveLength {files : PublicFiles} {settings : Settings}
    (part : HonestProversAndSettingsAtFiles files settings) (length : ℕ) : Prop :=
  ∀ reading, (part.compiledSettings reading).coinNumbers.pre₀.length +
    (part.compiledSettings reading).coinNumbers.ℓ = length

/-! ## 3. What is to prove -/

/-- **The goal**: the six lines of the compiled system. -/
def FinalBindingGoal : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesTaken files parameters →
    ∀ (part : HonestProversAndSettingsAtFiles files (settingsOfRead parameters)) (length : ℕ),
      TableSaltsHaveLength part length →
        BindingOf (compile (flashProveAtFiles files (settingsOfRead parameters) part))
          (finalExtractor files (settingsOfRead parameters))

/-- The same of the compiled system with a word beside each proof, whatever the rule for the word. -/
def FinalBindingLabelled : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesTaken files parameters →
    ∀ (part : HonestProversAndSettingsAtFiles files (settingsOfRead parameters)) (length : ℕ),
      TableSaltsHaveLength part length →
        ∀ (Label : Type)
          (label : ModelWeights (settingsOfRead parameters) → List Token × List Token → Label),
          BindingOf (labelled (compile (flashProveAtFiles files (settingsOfRead parameters) part)) label)
            (finalExtractor files (settingsOfRead parameters))

end VerifiableInference.Compilation
