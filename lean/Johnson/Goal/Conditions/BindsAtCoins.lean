-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsAtCoins.lean: "THE OPENER MAY PICK ANY COINS" AS ONE STATEMENT: binding
(`BindsWith`, VerifiableInference/MoreStatements.lean) of the system whose committer's randomness IS
the coins (pads with tails, and salts) and whose committer is this folder's `fixedCommit` at these
coins (by reading: the description's committer with its coins fixed: limits 1 and 2): at the
description's own extractor and at the goals' error. Definitions, statements and proofs.

Why. At `theWideDigits` (Johnson/Goal/Conditions/WideDigits.lean) the
sentence is had by two statements and an argument: G9bits holds at every K and W, at enumerations
with one member too, and says "to open is to name a number ρ"; `coins_enumerated_own` says how far ρ
reaches. Here the two are joined.

Main names.
  `ArgumentSystem.withRandomness`, **`BindsWith.mapRandomness`** (namespace
    `VerifiableInference`): A TOOL, general in the argument system: where for all weights and new
    coins there is old randomness at which the old committer gives, AT EVERY HASH FUNCTION, what the
    new committer gives, binding goes over: same extractor, same error. After the proof of
    `BindsWith.mapWeights` (VerifiableInference/MapWeightsBinding.lean): the new opener followed by
    that choice is an old opener with the same queries; the recomputation enters the event by its
    value alone.
  `CoinsOf K W Z` (namespace `FlashProve`, as all below): pads with tails r, and salts σ WITH A
    FENCE: at the tree's places each has the salts' length. All three sizes are read at the
    description's own input `Rw K W Z`. `coinsOf_nonempty`: there are such coins, at every K, W, Z.
  `coinsSystem K W Z s sample prove`: `systemOfRecord (atSecondHashFunction (theWide K W)) Z s` with `CoinsOf K
    W Z` for the randomness and `fixedCommit (theWideTerms K W) Z s w r σ` for the committer.
  **`bindsWith_coins`**: at every Z in scope whose files are read, where K covers the coins and
    toNat is onto below the product of the two lengths: `BindsWith (coinsSystem …)` at `theWide`'s
    own extractor and at `bindingErrorInQueries` (Ladder/Bits.lean). From `G9bits_theWide` and
    `coins_enumerated_own`.
  `fixedCommit_count` (namespace `VerifierAndGoals.Fit`): the count of the committer with the coins fixed.
    `extracts_at_coins_of`, **`extracts_at_coins`**: IT IS NOT EMPTY (given a Z in scope that is
    read): from a commitment at any coins, and the queries of that run, the extractor gives the
    weights back, but with probability `bindingErrorInQueries q`, q that committer's count: within the honest
    side's budget, where `bindingErrorInQueries` is at most the ceiling (one quarter).
  `bindsWith_coins_at_digits`: at `K.digits`, which covers. **`bindsWith_coins_digits`**,
    **`extracts_at_coins_digits`**: AT THE CLOSED `theWideDigits`: no premise but "in scope" and
    "the files are read".
  `weights_and_coins`: where the files are read there are weights and coins.
    **`read_weights_and_coins`**: A NAMED PREMISE: from `FilesRead` (`VerifierAndGoals.filesRead`,
    Johnson/Goal/Files/FilesReadProof.lean): the full set's files are in scope and read, and there
    are weights and coins there: so, given `FilesRead`, the two "it is not empty" speak of
    something.
  **`noTwoOpenings_coins_digits`**: nobody opens one commitment to two different weights, each at
    coins of its own pick, but with probability twice `bindingErrorInQueries`: by
    `BindsWith.noTwoOpenings` (VerifiableInference/NoTwoOpenings.lean). ONE BIT LESS: the linear
    term is 32 / 2^128 for each query (2^-123), where `bindingErrorInQueries`'s is 16 / 2^128 (2^-124;
    Ladder/Bits.lean). Nothing on two openings to the same weights at different coins.

Every "there is", walked. In conclusions: none but three `Nonempty` (`coinsOf_nonempty`,
`weights_and_coins`, `read_weights_and_coins`: their witnesses: any pads with tails, salts of zeros,
the weights of the all-zero index) and `read_weights_and_coins`' pp, tied by `readFiles storedPublicFiles = .ok
pp`. In premises: "K covers" (`TheCoins.Covers`, Johnson/Goal/Conditions/CoinsEnumeratedAt.lean: K's
first list is onto the pads with tails; for all salts of the right length at the tree's places there
is a number in K's second list whose salts are these at those places) and "toNat is onto below the
product": both are proved at the digits (`covers_digits`; toNat the identity), so the closed
statements have neither. In the proof of `bindsWith_coins` the old randomness is picked by choice
out of `coins_enumerated_own`'s "there is ρ such that at every hash function": it is part of the
adversary that the proof builds, of no term that runs.
Limits. (1) THE COMMITTER IS THIS FOLDER's OWN NAME: no statement here unfolds `fixedCommit` to "the
public reading; the tree over the coding at (r, σ); the told part beside; the key's digest": that is
typed in Johnson/Goal/Conditions/BindsPlain.lean (`fixedCommit_theWide`; `bindsWith_plain`: binding
with the committer written out, at the named error). (2) VALUES, NOT ALGORITHMS: by reading, the
description's committer asks two queries more than `fixedCommit`: enough for binding, where the
recomputation is in nobody's count; nothing on a count or a log of the description's own committer:
`extracts_at_coins` speaks of the log of `fixedCommit`. (3) sample and prove are letters: binding
reads neither; nothing on completeness or hiding. (4) THE VERIFIER IS IDLE: to open is to name
weights and coins at which the committer, run again, gives the commitment. Not in the experiment:
salts of another length at a place of the tree; a word that is no code word; a record that is not
the honest one; a told part other than the public reading's. (The filling b₀ is not read: the tree
has no leaf beyond the word: BindsPlain.lean.) (5) The salts' length is 256 + 8 times the plan's
salt: it hangs on the public files' plan. (6) At `settingsOfRead pp` alone, as the goals. (7)
`coinsSystem` is the system of record of no description (a description's type of randomness cannot
hang on Z): so these statements stand BESIDE G9bits, as what it means; they are no goal of
Ladder.lean in the goal's form. (8) All limits of WideDigits.lean: the honest side at the closed
term is hollow; no program's commitment is spoken of. (9) THE HASH FUNCTION: in every experiment
here it is drawn at random and asked as an oracle; no premise and no axiom asks anything of a
concrete hash function. BUT THE CLOSED TERM REACHES A CONCRETE HASH FUNCTION BY NAME:
`theWideDigits` stands over `flashProveData`, the lay at `OnBytes.secondHashFunction` (`theLayAt_older`,
Johnson/Goal/Description/Lay.lean), and over the public reading `pub8`, which calls the planner's
`publicOf`; what else is reached hangs on what sits in the lay's seats. A walk over the environment
(a rough check's print, no theorem) finds such names from `theWideDigits`, from `theWideTerms`,
and from `fixedCommit` and the extractor at the closed terms (from `fixedCommit` at letters: none).
Such a walk cannot part a record's fields: whether one of them lies on the committer's path is not
settled.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.WideDigits
import VerifiableInference.BindsAtRandomness
import VerifiableInference.NoTwoOpenings
import Ladder.BitsTies
import Ladder.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal
open MeasureTheory

namespace VerifiableInference
open RandomizedAlgorithm

/-- The system with another type of committer's randomness, and a sampler, a committer and a prover
for it. All else is the old system's. -/
def ArgumentSystem.withRandomness (system : ArgumentSystem) (Coins : Type)
    (sample : RandomizedAlgorithm Coins)
    (commit : system.Weights → Coins → DeterministicAlgorithm Commitment)
    (prove : system.Weights → Coins → List Token → List Token →
      RandomizedAlgorithm system.Proof) : ArgumentSystem where
  Weights := system.Weights
  PublicParameters := system.PublicParameters
  publicParameters := system.publicParameters
  CommitmentRandomness := Coins
  Proof := system.Proof
  nextToken := system.nextToken
  sampleCommitmentRandomness := sample
  commit := commit
  prove := prove
  verify := system.verify

/-- **Binding for a given extractor carries over to another committer's randomness**, where every
new commitment is an old one: for all weights and new coins there is old randomness (`pick`) at
which the old committer gives, at every hash function, what the new committer gives. The extractor
and the error are the same. An opener of the new system, followed by `pick`, is an opener of the
old one with the same queries. -/
theorem BindsWith.mapRandomness (system : ArgumentSystem)
    (extractor : Commitment → QueryLog → Option system.Weights) (ε : ℕ → ℝ≥0∞)
    (binds : BindsWith system extractor ε) (Coins : Type) (sample : RandomizedAlgorithm Coins)
    (commit : system.Weights → Coins → DeterministicAlgorithm Commitment)
    (prove : system.Weights → Coins → List Token → List Token →
      RandomizedAlgorithm system.Proof)
    (pick : system.Weights → Coins → system.CommitmentRandomness)
    (h : ∀ weights coins hash,
      (commit weights coins).evaluate hash = (system.commit weights (pick weights coins)).evaluate
        hash) :
    BindsWith (system.withRandomness Coins sample commit prove) extractor ε := by
  intro committerQueries proverQueries State committer committerBound opener openerBound
  refine le_trans ?_ (binds committerQueries proverQueries State committer committerBound
    (fun state => (opener state).bind fun y => RandomizedAlgorithm.done (y.1, pick y.1 y.2))
    (fun state => queryBound_map (fun y : system.Weights × Coins => (y.1, pick y.1 y.2))
      (opener state) proverQueries (openerBound state)))
  unfold Prob
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (opener c.1.2).bind fun y =>
        (commit y.1 y.2).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, y.1, recomputed)).run hash) _
    ≤ ZKCP.prob ((committer.withQueryLog.bind fun c =>
        ((opener c.1.2).bind fun y => RandomizedAlgorithm.done (y.1, pick y.1 y.2)).bind fun z =>
          (system.commit z.1 z.2).toRandomized.bind fun recomputed =>
            RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, z.1, recomputed)).run hash) _
  rw [run_bind, run_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [run_bind, run_bind, run_bind, PMF.bind_bind, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  rw [run_done, PMF.pure_bind]
  show ZKCP.prob (((commit y.1 y.2).toRandomized.bind fun recomputed =>
        RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, y.1, recomputed)).run hash) _
    ≤ ZKCP.prob (((system.commit y.1 (pick y.1 y.2)).toRandomized.bind fun recomputed =>
        RandomizedAlgorithm.done (extractor c.1.1 c.2, c.1.1, y.1, recomputed)).run hash) _
  rw [run_bind, run_bind, DeterministicAlgorithm.run_toRandomized,
    DeterministicAlgorithm.run_toRandomized, h y.1 y.2 hash]
  exact le_refl _

end VerifiableInference

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

variable {D : Description} {Q : HonestTerms D}

/-- **The count of the committer with the coins fixed**: the told committer's, with the query for
the key's code: the description's own committer's count less the coins' algorithm's. -/
theorem fixedCommit_count {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (w : ModelWeights s) (r : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness)
    (σ : ℕ → Rom.Bits) : (fixedCommit Q Z s w r σ).toRandomized.QueryBound (Q.tCommit Z tP + 1) :=
  queryBound_commit_systemOn (Q.T Z) (enumOne r) (enumOne σ) (Q.b₀ Z) (Q.proveT Z) (Q.back Z s)
    (modelNextToken s) tP h.reading w _

end VerifierAndGoals.Fit

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF descriptionOfDataOnBytes riDigits fieldRows
  FlashProve.thePlan FlashProve.theItem

/-- **The committer's coins at Z**: pads with tails, and salts that have the salts' length at the
tree's places: all three read at the description's own input. -/
def CoinsOf (K : TheCoins) (W : WideCoins K) (Z : PublicFiles) : Type :=
  { x : (Rw K W Z).protocol.EncodingRandomness × (ℕ → Rom.Bits) //
    ∀ j, j < 2 ^ (Rw K W Z).queryLayout.depth → (x.2 j).length = (Rw K W Z).compilerParameters.sMT }

/-- There are such coins, at every K, W and Z: any pads with tails, and salts of zeros. -/
theorem coinsOf_nonempty (K : TheCoins) (W : WideCoins K) (Z : PublicFiles) : Nonempty (CoinsOf K W Z) :=
  ⟨⟨(Classical.arbitrary _, fun _ => List.replicate (Rw K W Z).compilerParameters.sMT false),
    fun _ _ => List.length_replicate⟩⟩

/-- The description's system of record (at the second hash function, as the goals on binding take
it) with these coins for the committer's randomness and the committer with the coins fixed
(`fixedCommit`, Johnson/Goal/Conditions/CoinsEnumerated.lean) for its committer. sample, prove: any:
binding reads neither. -/
def coinsSystem (K : TheCoins) (W : WideCoins K) (Z : PublicFiles) (s : IntegerTransformer.Settings)
    (sample : RandomizedAlgorithm (CoinsOf K W Z))
    (prove : ModelWeights s → CoinsOf K W Z → List Token → List Token →
      RandomizedAlgorithm (systemOfRecord (atSecondHashFunction (theWide K W)) Z s).Proof) : ArgumentSystem :=
  (systemOfRecord (atSecondHashFunction (theWide K W)) Z s).withRandomness (CoinsOf K W Z) sample
    (fun w x => fixedCommit (theWideTerms K W) Z s w x.1.1 x.1.2) prove

variable (K : TheCoins)

/-- **BINDING WITH THE COINS IN THE OPENER's HAND**, at every K that covers the coins. -/
theorem bindsWith_coins (toNat : K.Rand → ℕ) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hs : InScope Z = true) (hr : readFiles Z = .ok pp) (hK : K.Covers Z)
    (onto : ∀ n, n < ((K.ri Z).n + 1) * ((K.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (sample : RandomizedAlgorithm (CoinsOf K (WideCoins.full K toNat) Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsOf K (WideCoins.full K toNat) Z →
      List Token → List Token → RandomizedAlgorithm
        (systemOfRecord (atSecondHashFunction (theWide K (WideCoins.full K toNat))) Z
          (settingsOfRead pp)).Proof) :
    BindsWith (coinsSystem K (WideCoins.full K toNat) Z (settingsOfRead pp) sample prove)
      ((atSecondHashFunction (theWide K (WideCoins.full K toNat))).extractor Z (settingsOfRead pp))
      bindingErrorInQueries := by
  have hb := (G9bits_theWide K (WideCoins.full K toNat) Z pp hs hr).2
  exact BindsWith.mapRandomness
    (systemOfRecord (atSecondHashFunction (theWide K (WideCoins.full K toNat))) Z (settingsOfRead pp)) _
    bindingErrorInQueries hb (CoinsOf K (WideCoins.full K toNat) Z) sample
    (fun w x => fixedCommit (theWideTerms K (WideCoins.full K toNat)) Z (settingsOfRead pp) w
      x.1.1 x.1.2) prove
    (fun w x => Classical.choose
      (coins_enumerated_own K toNat OnBytes.secondHashFunction Z pp hr hK onto w x.1.1 x.1.2 x.2))
    (fun w x hash => (Classical.choose_spec
      (coins_enumerated_own K toNat OnBytes.secondHashFunction Z pp hr hK onto w x.1.1 x.1.2 x.2) hash).symm)

/-- From a commitment at any coins, and the queries of that run, the extractor gives the weights
back, but with probability `bindingErrorInQueries` at a bound q on these queries. By
`BindsWith.atRandomness` (VerifiableInference/BindsAtRandomness.lean). -/
theorem extracts_at_coins_of (toNat : K.Rand → ℕ) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hs : InScope Z = true) (hr : readFiles Z = .ok pp) (hK : K.Covers Z)
    (onto : ∀ n, n < ((K.ri Z).n + 1) * ((K.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (w : ModelWeights (settingsOfRead pp)) (x : CoinsOf K (WideCoins.full K toNat) Z) (q : ℕ)
    (bound : (fixedCommit (theWideTerms K (WideCoins.full K toNat)) Z (settingsOfRead pp) w x.1.1
      x.1.2).toRandomized.QueryBound q) :
    Prob (fixedCommit (theWideTerms K (WideCoins.full K toNat)) Z (settingsOfRead pp) w x.1.1
        x.1.2).toRandomized.withQueryLog
        {c | (atSecondHashFunction (theWide K (WideCoins.full K toNat))).extractor Z (settingsOfRead pp) c.1 c.2
          ≠ some w}
      ≤ bindingErrorInQueries q := by
  obtain ⟨ρ₀, -⟩ := onto 0 (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  exact (bindsWith_coins K toNat Z pp hs hr hK onto (.done x) fun w' _ =>
    (systemOfRecord (atSecondHashFunction (theWide K (WideCoins.full K toNat))) Z (settingsOfRead pp)).prove w'
      ρ₀).atRandomness w x q bound

/- From here on Lean compares that committer by its name. -/
attribute [local irreducible] fixedCommit

/-- **IT IS NOT EMPTY**: the same at that committer's own count (`fixedCommit_count`), which is
within the honest side's budget; there `bindingErrorInQueries` is at most the ceiling
(`bitsBinding_le_ceiling`, Ladder/BitsTies.lean). -/
theorem extracts_at_coins (toNat : K.Rand → ℕ) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hs : InScope Z = true) (hr : readFiles Z = .ok pp) (hK : K.Covers Z)
    (onto : ∀ n, n < ((K.ri Z).n + 1) * ((K.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (w : ModelWeights (settingsOfRead pp)) (x : CoinsOf K (WideCoins.full K toNat) Z) :
    (theWideTerms K (WideCoins.full K toNat)).tCommit Z 8 + 1 ≤ honestBudget ∧
      bindingErrorInQueries ((theWideTerms K (WideCoins.full K toNat)).tCommit Z 8 + 1) ≤ ceiling ∧
      Prob (fixedCommit (theWideTerms K (WideCoins.full K toNat)) Z (settingsOfRead pp) w x.1.1
          x.1.2).toRandomized.withQueryLog
          {c | (atSecondHashFunction (theWide K (WideCoins.full K toNat))).extractor Z (settingsOfRead pp) c.1
            c.2 ≠ some w}
        ≤ bindingErrorInQueries ((theWideTerms K (WideCoins.full K toNat)).tCommit Z 8 + 1) := by
  have laws := bindLaws_wide K (WideCoins.full K toNat) Z pp hr
  have hq := le_trans (Nat.le_add_left _ 2) laws.number
  exact ⟨hq,
    bitsBinding_le_ceiling _ (le_trans hq (by unfold honestBudget queryBudget; norm_num)),
    extracts_at_coins_of K toNat Z pp hs hr hK onto w x
      ((theWideTerms K (WideCoins.full K toNat)).tCommit Z 8 + 1)
      (fixedCommit_count laws w x.1.1 x.1.2)⟩

/-- The same at `K.digits`: it covers at every Z. -/
theorem bindsWith_coins_at_digits (toNat : K.digits.Rand → ℕ) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (onto : ∀ n, n < ((K.digits.ri Z).n + 1) * ((K.digits.sl Z).n + 1) → ∃ ρ, toNat ρ = n)
    (sample : RandomizedAlgorithm (CoinsOf K.digits (WideCoins.full K.digits toNat) Z))
    (prove : ModelWeights (settingsOfRead pp) →
      CoinsOf K.digits (WideCoins.full K.digits toNat) Z → List Token → List Token →
      RandomizedAlgorithm (systemOfRecord (atSecondHashFunction (theWide K.digits
        (WideCoins.full K.digits toNat))) Z (settingsOfRead pp)).Proof) :
    BindsWith
      (coinsSystem K.digits (WideCoins.full K.digits toNat) Z (settingsOfRead pp) sample prove)
      ((atSecondHashFunction (theWide K.digits (WideCoins.full K.digits toNat))).extractor Z
        (settingsOfRead pp)) bindingErrorInQueries :=
  bindsWith_coins K.digits toNat Z pp hs hr (covers_digits K Z) onto sample prove

/-! ## At the closed term -/

/-- **AT THE CLOSED DESCRIPTION: NO PREMISE BUT "IN SCOPE" AND "THE FILES ARE READ".** -/
theorem bindsWith_coins_digits (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (sample : RandomizedAlgorithm (CoinsOf digitCoins digitWide Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsOf digitCoins digitWide Z → List Token →
      List Token → RandomizedAlgorithm
        (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)).Proof) :
    BindsWith (coinsSystem digitCoins digitWide Z (settingsOfRead pp) sample prove)
      ((atSecondHashFunction theWideDigits).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  bindsWith_coins_at_digits placeHolderNumberCoins (fun n : ℕ => n) Z pp hs hr
    (fun n _ => ⟨n, rfl⟩) sample prove

/-- **AND IT IS NOT EMPTY THERE.** -/
theorem extracts_at_coins_digits (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp))
    (x : CoinsOf digitCoins digitWide Z) :
    (theWideTerms digitCoins digitWide).tCommit Z 8 + 1 ≤ honestBudget ∧
      bindingErrorInQueries ((theWideTerms digitCoins digitWide).tCommit Z 8 + 1) ≤ ceiling ∧
      Prob (fixedCommit (theWideTerms digitCoins digitWide) Z (settingsOfRead pp) w x.1.1
          x.1.2).toRandomized.withQueryLog
          {c | (atSecondHashFunction theWideDigits).extractor Z (settingsOfRead pp) c.1 c.2 ≠ some w}
        ≤ bindingErrorInQueries ((theWideTerms digitCoins digitWide).tCommit Z 8 + 1) :=
  extracts_at_coins placeHolderNumberCoins.digits (fun n : ℕ => n) Z pp hs hr
    (covers_digits placeHolderNumberCoins Z) (fun n _ => ⟨n, rfl⟩) w x

/-- Where the files are read there are weights and coins. -/
theorem weights_and_coins (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) :
    Nonempty (ModelWeights (settingsOfRead pp) × CoinsOf digitCoins digitWide Z) :=
  ⟨(nonempty_modelWeights (valid_of_read hr)).some, (coinsOf_nonempty _ _ Z).some⟩

/-- **A named premise**: given `FilesRead`, the full set's files are in scope and
read, and there are weights and coins there. -/
theorem read_weights_and_coins (h : FilesRead) :
    ∃ pp, InScope storedPublicFiles = true ∧ readFiles storedPublicFiles = .ok pp ∧
      Nonempty (ModelWeights (settingsOfRead pp) × CoinsOf digitCoins digitWide storedPublicFiles) :=
  let ⟨hs, pp, hr, _⟩ := h.full
  ⟨pp, hs, hr, weights_and_coins _ _ hr⟩

/-- **NOBODY OPENS ONE COMMITMENT TO TWO DIFFERENT WEIGHTS, EACH AT COINS OF ITS OWN PICK**, but
with probability twice `bindingErrorInQueries`: one bit under it. -/
theorem noTwoOpenings_coins_digits (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (sample : RandomizedAlgorithm (CoinsOf digitCoins digitWide Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsOf digitCoins digitWide Z → List Token →
      List Token → RandomizedAlgorithm
        (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)).Proof) :
    NoTwoOpenings (coinsSystem digitCoins digitWide Z (settingsOfRead pp) sample prove)
      fun q => 2 * bindingErrorInQueries q :=
  (bindsWith_coins_digits Z pp hs hr sample prove).noTwoOpenings

end FlashProve

#print axioms VerifiableInference.BindsWith.mapRandomness
#print axioms VerifierAndGoals.Fit.fixedCommit_count
#print axioms FlashProve.coinsOf_nonempty
#print axioms FlashProve.bindsWith_coins
#print axioms FlashProve.extracts_at_coins_of
#print axioms FlashProve.extracts_at_coins
#print axioms FlashProve.bindsWith_coins_at_digits
#print axioms FlashProve.bindsWith_coins_digits
#print axioms FlashProve.extracts_at_coins_digits
#print axioms FlashProve.weights_and_coins
#print axioms FlashProve.read_weights_and_coins
#print axioms FlashProve.noTwoOpenings_coins_digits
