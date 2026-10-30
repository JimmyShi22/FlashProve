-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/TheTie.lean: THE TIE BETWEEN THE WRITTEN COMMITTER AND THE RUNNING COMMITTER, WITH
NO HYPOTHESIS BUT THE FACT ON THE FRAME (SaltAt Z: the frame's salts have 40 bytes), and the
headline forms with no tie among their premises. Every proof here is one call.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO: the
running committer (Johnson/Bind/Twin.lean) is a model of one part of that program. No theorem ties
it to the program. Evaluations have compared it with runs of the program at the small stored
example's public files, on synthetic weights, and nowhere else; what was compared, and what was not,
stands in Johnson/Bind/README.md ("What is run, not proved").
The extractor is that of the theorem on soundness (cpp_is_of_verify, Johnson/Bind/Cpp/OfTie.lean).
"The opening form" is BindsWith (VerifiableInference/MoreStatements.lean): nobody opens a
commitment, by naming weights and randomness from which the committer gives it, to weights that the
extractor does not give; at fixed randomness it yields that the extractor gives the committed
weights back (BindsWith.atRandomness).

Why. Johnson/Bind/Cpp/TieGathered.lean gathers what is proved of the tie and leaves two equations on
typed queries as a hypothesis (OwedAt Z): a leaf's and the OOD seed's. They are proved in
Johnson/Bind/Spell/Leaf.lean (spellsLeaf_of: where the frame's salts have 40 bytes) and
Johnson/Bind/Spell/Seed.lean (spellsSeed_of: at every Z). Here they are laid in.
What the whole rests on, by its parts (the files that each of these imports are not listed; all
under Johnson/Bind/ but where a longer path stands):
  the five equations on typed queries   Cpp/SpellsC.lean, Cpp/SpellsNode.lean, Cpp/SpellsId.lean,
                                        Spell/Leaf.lean, Spell/Seed.lean;
  the encoder and the digits            Cpp/ColumnAt.lean;
  the OOD answers                       Cpp/AnswersAre.lean;
  the two trees                         TwinTree.lean;
  the joint                             CoreValue.lean, CoreJoin.lean, CoreTie.lean, Cpp/Join.lean;
  the frame's salts; the count          Cpp/SaltAt.lean; Cpp/AtTwin.lean;
  from the tie to the headline forms    Cpp/OfTie.lean, Cpp/Extracts.lean, Cpp/AtLive.lean,
                                        Cpp/Guards.lean, Johnson/Goal/HonestSideFree.lean;
  the written committer's own theorem   bindsWith_plain_law, Johnson/Goal/Conditions/BindsTold.lean.
Every probability in the headline forms is that last theorem's: the tie carries it over, by equal
values at every hash function.

Main names (namespace Bind.Cpp).
  owedAt: OwedAt Z, where the frame's salts have 40 bytes.
  **tieKeyAt**, **tieAt**: the tie at the key, and at the commitment ID, at such a Z.
  tie, tieLive: Tie (theTwin g) and TieLive (theTwin g) (Johnson/Bind/Cpp/Defs.lean, AtLive.lean).
  **extractsCommitted_salt**, **bindsAt_salt**, noTwoOpenings_salt: at every Z that is read and
    whose frame has salts of 40 bytes: correctness of extraction (ExtractsCommittedWeights,
    VerifiableInference/MoreStatements.lean) for the committer of theCpp (theTwin g); the body of
    G9bits (Ladder/Bits.lean): the opening form (BindsWith), at bindingErrorInQueries; nobody opens one
    commitment ID to two different weights (NoTwoOpenings), at twice that error.
  extracts_salt, extracts_square_salt: correctness of extraction AT EVERY RANDOMNESS, a seed or
    coins, at such a Z: at bindingErrorInQueries (2^35 + 2), and at the written committer's own square form,
    about 2^-156.
  **extractsCommitted**, **bindsAt**: the first two at every Z in scope that is read and at which
    the verifier's tests on the public files pass (protocolDataWellFormed): there the frame's salts have 40 bytes
    (saltAt_of_live).
  policy_and_binding_at_zGap: at the named files zGap, under the one premise that protocolDataWellFormed passes
    there: soundness under the files' policy and the opening form, at one description and one
    extractor: a conjunction, no join.
Limits. Those of Johnson/Bind/Cpp/Defs.lean, OfTie.lean and AtLive.lean travel whole. No index
privacy (hiding of the weights), no completeness. THIS IS NOT G9bits: it does not reach all files in
scope that are read. It is none of the goals of Ladder.lean and Ladder/Bits.lean: no goal is stated
here. THE VERIFIER IS IDLE: nothing says that verify accepts a proof under a
commitment of this committer's make. How weights become the table's entries is the library's own
(entryOf); that it is the programs' is compared nowhere. At this shape the running committer cannot
be run (about 2^72 multiplications): what has been run are small shapes. The public files are fixed
before the hash function is sampled. No figure here is 128 bits.
Beside these:
- THE MEMBER. THAT SaltAt Z HOLDS AT ANY Z, AND THAT protocolDataWellFormed PASSES AT ANY FILES, IS NO THEOREM OF
  THE MAIN LIBRARY. At the two named sets of files (storedPublicFiles, zGap) "in scope" and "read" are theorems
  (VerifierAndGoals.filesRead); in the main library that protocolDataWellFormed passes and the 40 bytes there are
  evaluations: runs of code, which Lean's kernel has not checked; protocolDataWellFormed's stands in no file of
  that library (too heavy for it). So in the main library no member of tieAt and of the forms under
  SaltAt is shown by theorems alone, and none of extractsCommitted, bindsAt and
  policy_and_binding_at_zGap. At both sets, which are the library's written copies of the two stored
  sets of public files, the frame's salts have 40 bytes and protocolDataWellFormed passes, by theorems of a side
  library, outside the main library and with that library's own limits: there all these have members
  by theorems (AtFullSide/Bind/TheTieAtNamed.lean, AtFullSide/Bind/LiveAtNamed.lean).
- THE KEY FILE. The committer returns the commitment ID alone, no key file and nothing that a prover
  could read; nor does anything here say that an ID under which verify accepts is of this
  committer's make.
- THE SHAPE. At the full-size shape alone; at the shapes at which the running committer has run
  nothing here is proved: the two are joined only in that it is one text, general in the shape.
- FROM A SEED TO THE COINS: not modelled: the generator g is a letter: no theorem reads what it is.
  With the weights' road to the table, both halves of what the committing program does before the
  modelled part hashes are outside these statements. The prover is a letter too.
- The description names the second hash function.
- WHAT THE TIE CANNOT SEE: the encoder's symbol function, the frame of the strings and the weights'
  digits are ONE Lean text on both sides of the tie's equation, so an error in them shows on neither
  side. Of these only the first two are reached from outside, by the evaluations against the program
  at a small shape; the weights' digits are compared with the programs' nowhere. (By name:
  Fmt.M1.symF; Fmt.oStr, Fmt.colBytes, Fmt.leafPlace; indexOfWeights.) What the tie compares is how
  the two committers put them together: the order and places of entries, pads and tails, the tree,
  the start and the salt of a leaf, the seeds' chain, the OOD answers, the name and the ID's string.
Terms: lean/TERMS.md, lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.TieGathered
import Johnson.Bind.Cpp.Guards
import Johnson.Bind.Spell.Leaf
import Johnson.Bind.Spell.Seed

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

/-- What TieGathered.lean leaves as a hypothesis, proved, where the frame's salts have 40 bytes. -/
theorem owedAt (Z : PublicFiles) (hs : SaltAt Z) : OwedAt Z :=
  fun hash => ⟨Bind.Spell.spellsLeaf_of Z hs hash (spellsC Z hash),
    Bind.Spell.spellsSeed_of Z hash (spellsC Z hash)⟩

/-- **THE TIE AT THE KEY**, where the frame's salts have 40 bytes. -/
theorem tieKeyAt (Z : PublicFiles) (hs : SaltAt Z) : TieKeyAt Z := tieKeyAt_of_owed Z hs (owedAt Z hs)

/-- **THE TIE**, where the frame's salts have 40 bytes, at the running committer of
Johnson/Bind/Twin.lean. The statement does not read the generator g. -/
theorem tieAt (Z : PublicFiles) (hs : SaltAt Z) (g : Shape → Seed → Digest → Digest → Coins) :
    TieAt (theTwin g) Z :=
  tieAt_of_owed Z hs (owedAt Z hs) g

/-- The tie, whole. -/
theorem tie (g : Shape → Seed → Digest → Digest → Coins) : Tie (theTwin g) :=
  fun Z hs => tieAt Z hs g

/-- The tie at all files in scope at which protocolDataWellFormed passes. -/
theorem tieLive (g : Shape → Seed → Digest → Digest → Coins) : TieLive (theTwin g) :=
  tieLive_of_tie (theTwin g) (tie g)

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **Correctness of extraction for the committer of theCpp (theTwin g)**, at every Z that is read
and whose frame has salts of 40 bytes. The generator is a letter: no theorem reads what it is. No
theorem of the main library says that any frame has such salts. The error, bindingErrorInQueries (2^35 + 2),
is about 2^-89. -/
theorem extractsCommitted_salt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z) :
    ExtractsCommittedWeights
      (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp))
      (bindingErrorInQueries (twinBudget + 2)) :=
  extractsCommitted_cpp (theTwin g) prove Z pp hr (tieAt Z hs g) (count_theTwin g Z)

/-- **The body of G9bits**, at every Z that is read and whose frame has salts of 40 bytes. The
generator is a letter. This is not G9bits: the goal asks it at all files in scope that are read. -/
theorem bindsAt_salt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z) :
    (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  bindsAtZ_cpp (theTwin g) prove Z pp hr (tieAt Z hs g) (count_theTwin g Z)

/-- **Nobody opens one commitment ID to two different weights**, each at a seed or coins of its own
pick, but with probability 2 · bindingErrorInQueries t, at every Z that is read and whose frame has salts of
40 bytes. -/
theorem noTwoOpenings_salt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z) :
    NoTwoOpenings (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
      fun t => 2 * bindingErrorInQueries t :=
  noTwoOpenings_cpp (theTwin g) prove Z pp hr (tieAt Z hs g) (count_theTwin g Z)

/-- **Correctness of extraction at every randomness**: at all weights and every seed or coins, from
the commitment ID and that run's queries the extractor gives the committer's own weights back, but
with probability bindingErrorInQueries (2^35 + 2), at every Z that is read and whose frame has salts of 40
bytes. -/
theorem extracts_salt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z)
    (w : ModelWeights (settingsOfRead pp)) (ρ : Rand) :
    Prob ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z (settingsOfRead pp) w
        ρ).toRandomized.withQueryLog
        {o | (atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp) o.1 o.2 ≠ some w}
      ≤ bindingErrorInQueries (twinBudget + 2) :=
  extracts_cpp (theTwin g) prove Z pp hr (tieAt Z hs g) (count_theTwin g Z) w ρ

/-- The same at the square form: 3 (2^35 + 4 + 2 · 2^48 + 2)² / 2^256, about 2^-156. -/
theorem extracts_square_salt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (hs : SaltAt Z)
    (w : ModelWeights (settingsOfRead pp)) (ρ : Rand) :
    Prob ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z (settingsOfRead pp) w
        ρ).toRandomized.withQueryLog
        {o | (atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp) o.1 o.2 ≠ some w}
      ≤ epsBind honestBudget (twinBudget + 2 + 2) :=
  extracts_cpp_square (theTwin g) prove Z pp hr (tieAt Z hs g) (count_theTwin g Z) w ρ

/-- **Correctness of extraction for the committer of theCpp (theTwin g)**, at every Z in scope that
is read and at which protocolDataWellFormed passes. The generator is a letter: no theorem reads what it is. No
theorem of the main library says that protocolDataWellFormed passes at any files. The error, bindingErrorInQueries
(2^35 + 2), is about 2^-89. -/
theorem extractsCommitted (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ExtractsCommittedWeights
      (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp))
      (bindingErrorInQueries (twinBudget + 2)) :=
  extractsCommitted_salt prove g Z pp hr (saltAt_of_live hs hl)

/-- **The body of G9bits**, at every Z in scope that is read and at which protocolDataWellFormed passes. The
generator is a letter. The files are fewer than the goal's ("in scope, read"): this is not G9bits.
-/
theorem bindsAt (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  bindsAt_salt prove g Z pp hr (saltAt_of_live hs hl)

/-- **Both halves at zGap, under the one premise that protocolDataWellFormed passes there.** In scope; read; the
policy (25856, 512, 1); but with probability at most soundnessErrorInQueries t n nobody has an output accepted for
which the extractor gives no weights, or which does not meet that policy at the weights that it
gives; and but with probability at most bindingErrorInQueries t nobody opens a commitment of this committer's
make to weights that the same extractor does not give. A conjunction at one extractor, no join:
nothing says that a commitment under which verify accepts is of this committer's make. No theorem of
the main library says that protocolDataWellFormed passes at zGap. (SaltAt zGap would do for the proof; where
protocolDataWellFormed fails, verify accepts nothing and the first half is idle.) -/
theorem policy_and_binding_at_zGap (g : Shape → Seed → Digest → Digest → Coins)
    (hl : protocolDataWellFormed (asDescriptionFiles zGap) = true) :
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
  policy_and_binding_at_zGap_cpp (theTwin g) prove
    (tieAt zGap (saltAt_of_live VerifierAndGoals.filesRead.other.1 hl) g) (count_theTwin g zGap)

end Bind.Cpp

end

#print axioms Bind.Cpp.owedAt
#print axioms Bind.Cpp.tieKeyAt
#print axioms Bind.Cpp.tieAt
#print axioms Bind.Cpp.tie
#print axioms Bind.Cpp.tieLive
#print axioms Bind.Cpp.extractsCommitted_salt
#print axioms Bind.Cpp.bindsAt_salt
#print axioms Bind.Cpp.noTwoOpenings_salt
#print axioms Bind.Cpp.extracts_salt
#print axioms Bind.Cpp.extracts_square_salt
#print axioms Bind.Cpp.extractsCommitted
#print axioms Bind.Cpp.bindsAt
#print axioms Bind.Cpp.policy_and_binding_at_zGap
