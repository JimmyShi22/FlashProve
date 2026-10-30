-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsPlain.lean: OPENING-FORM BINDING OF THE WRITTEN COMMITTER
(written in Lean beside the IOP: a placeholder that corresponds to no program of the release)
OVER THE DESCRIPTION'S
TOLD RECORD: the coins are in the opener's hand; the statement names no enumeration, no number of
coins, no K and no W; the error is the named one, which has no term linear in the queries beside the
square (whose cross term is about 2^-204 a query). THE COMMITTER IS LAID BESIDE `descriptionOfDataOnBytes flashProveData`,
WHOSE OWN HONEST SIDE IS HOLLOW (limit 7). Definitions, statements and proofs.

Why. `bindsWith_coins_digits` (Johnson/Goal/Conditions/BindsAtCoins.lean) says "the opener may pick
any coins" of a committer that is this pack's own name at the digits, `fixedCommit (theWideTerms
digitCoins digitWide)`. No statement of that file unfolds it, and "the same at every K
and W" is not typed there. And it stands at the goal's line `bindingErrorInQueries` (Ladder/Bits.lean), whose
linear term is 16 / 2^128 a query: the statement here is at the square form alone.

Main names. General in D and Q (namespace `VerifierAndGoals.Fit`):
  `fixedCommit_plain`: `fixedCommit Q Z s w r σ` IS `(Q.T Z).commitAtCoins (Q.b₀ Z) (Q.back Z s w) r
    σ` (Johnson/Top/ToldCommitPlain.lean: the public reading; `committerAtFixedCoins` at (r, σ) over the coding at
    d; the told part beside; the key's digest). Premise: `BindLaws` (of it: the public reading draws
    no coin).
  `fixedCommit_reBound`: over the re-bound description the right side names neither the number of
    coins nor their algorithm; and any filling b, where the word has a symbol for each leaf.
  **`bindsWith_written`**: where the description with the terms laid in binds at an error ε, and
    each setting of coins out of a type Coins is its committer's at some randomness (reach): D's own
    system of record, with Coins for the committer's randomness and the written committer, binds at
    the extractor `(Q.T Z).extractorOn (Q.φ Z s)` and the same ε. By `BindsWith.mapRandomness`.
  `commitAtCoins_count`: the written committer's count.
  `epsBind_at_70`, `epsBind_under_line`: IN NUMBERS: `epsBind honestBudget (t + 2)` is at most
    2^-114 up to 2^70 queries, and at most (t + 1) / 2^128 up to 2^126 queries.
At the description (namespace `FlashProve`):
  `T₀ Z`: the told record of `descriptionOfDataOnBytes flashProveData` at Z. `T_the`: it is `(theTerms K).T Z` at every K.
    `T₀_fields`, `T₀_m`, `T₀_Sd`: ALL FIVE FIELDS THAT THE WRITTEN COMMITTER READS, by their names:
    the public reading, the told part, the told code; the coding at d; the seed's wire at d: each by
    definition. `leaves_R₀`: the tree has no leaf beyond the word.
  **`fixedCommit_theWide`**: at every K and W, all weights, pads with tails and salts, and EVERY
    filling b: `fixedCommit (theWideTerms K W) …` IS `(T₀ Z).commitAtCoins b (backThe Z s w) r σ`:
    the right side names neither K nor W.
  `Coins₀ Z`: pads with tails, and salts with a fence (at the tree's places each has the salts'
    length), read at `R₀ Z`; `coinsOf_eq`: they are `CoinsOf K W Z`. `plainSystem Z s b sample
    prove`: `systemOfRecord flashProveDescription Z s` with `Coins₀ Z` for the committer's randomness and the written
    committer.
  `bindsWith_plain_of`: from any K that covers the coins, at every error at which `theWide` binds: K
    IS A TOOL OF THE PROOF: the conclusion does not name it.
  **`bindsWith_plain`**: at every Z in scope whose files are read: `BindsWith (plainSystem …)` at
    the extractor `(T₀ Z).extractorOn (phiThe Z s)` and the error `fun t => epsBind honestBudget (t
    + 2)` = 3 (t + 2^49 + 4)² / 2^256 (Ladder/FitBinds.lean). `bindsWith_plain_bits`: at
    `bindingErrorInQueries`.
  `count₀`, `count₀_le`, `count₀_eq`, `plain_count`; `coins₀_nonempty`; **`extracts_plain`**: IT IS
    NOT EMPTY (given a Z in scope that is read): from a commitment at any weights and coins, and the
    queries of that run, the extractor gives the weights back, but with probability the named error
    at `count₀ Z`. `read_weights_and_coins₀`: given `FilesRead` (proved: `VerifierAndGoals.filesRead`) the
    full set's files are such a Z, and there are weights and coins.
  **`noTwoOpenings_plain`**: nobody opens one commitment to two different weights, each at coins of
    its own pick, but with probability twice the named error.

Every "there is", walked. In conclusions: `coins₀_nonempty` and `read_weights_and_coins₀` (Nonempty:
any pads with tails, salts of zeros, the weights of the all-zero index; pp is tied by `readFiles
storedPublicFiles = .ok pp`). In premises: reach of `bindsWith_written` ("there is ρ such that at every hash
function": ρ before the hash function), proved at the description by `coins_enumerated_of`; "K
covers" and "toNat is onto" of `bindsWith_plain_of`, proved at the digits (`covers_digits`; toNat
the identity). The closed statements have none.
The old randomness is picked by choice inside the proof: part of the adversary that the proof
builds, of no term that runs.
Limits. (1) `committerAtFixedCoins`, `pub8`, `cfg8`, `encF`, `LPFD.Full.mD` and `outOfDomainSampleQueryLayoutOfCode` are names of other files
and are not unfolded further: how a leaf, a node and the seed's queries are spelled as strings lies
in the last two. (2) VALUES, NOT ALGORITHMS, between `theWide`'s committer and the written one:
`theWide`'s committer asks up to two queries more (its coins' algorithm); `extracts_plain` speaks of
the written committer's log. (3) sample and prove are letters: binding reads neither; nothing on
completeness or hiding. (4) THE VERIFIER IS IDLE: to open is to name weights and coins at which the
written committer, run again, gives the commitment. Not in the experiment: salts of another length
at a place of the tree; a word that is no code word; a record that is not the honest one; a told
part other than the public reading's. (The filling is no limit: it is not read.) THE SQUARE
FORM IS THE PRICE OF THIS EVENT, where the word is a code word and the record the honest one by
construction: it is no sign that a notion in which the verifier judges an opening would be free of a
linear term: that is soundness' side. (5) The salts' length hangs on the public files' plan
(`sMT_R₀`, Johnson/Goal/Conditions/MoreAtDigits.lean). (6) At `settingsOfRead pp` alone, as the
goals. (7) BESIDE THE DESCRIPTION, NOT ITS OWN. The honest side of `flashProveDescription = descriptionOfDataOnBytes flashProveData` is
hollow (`theHonest := fixedCommitterAndProver`, Johnson/Goal/Description/Honest.lean: no randomness, a
commitment of zeros, a prover that hands empty files). Of `systemOfRecord flashProveDescription Z s` opening-form binding and `NoTwoOpenings` read the
type of weights alone. The tie to the description is its compiler's input `R₀ Z` and its told record
`T₀ Z`; and that `theWide K W`, whose committer has the written one's values, has flashProveDescription's verifier
(`verify_theWide`, Johnson/Goal/Conditions/WideAtThe.lean). `plainSystem` is the system of record of
no description (a description's type of randomness cannot hang on Z): these statements stand BESIDE
G9 and G9bits, as what they mean; they are no goal of Ladder.lean in the goal's form. (8) Where
`protocolDataWellFormed` says no, `descriptionOfDataOnBytes flashProveData` lays empty data: the statements hold there too, of that. No
program's commitment is spoken of. (9) THE HASH FUNCTION is drawn at random and asked as an oracle
in every experiment here; no premise and no axiom asks anything of a concrete hash function. BUT THE
TERMS REACH A CONCRETE HASH FUNCTION BY NAME: `T₀` stands over `flashProveData`, the lay at `OnBytes.secondHashFunction`
(`theLayAt_older`, Johnson/Goal/Description/Lay.lean), and its public reading `pub8` calls the
planner's `publicOf`: the second hash function, with which the strings that are asked are made.
What else is reached hangs on what sits in the lay's seats. `LayoutsByPublicReading.commitAtCoins`,
`LayoutsByPublicReading.extractorOn`, `committerAtFixedCoins`, `cfg8`, `encF`, `codingCells` and the coding `LPFD.Full.mD` (which
takes the request's item as a letter) name none, by a walk over the environment (a print, no
theorem). THE SAME THREE TERMS WITH THE SECOND HASH FUNCTION'S PLACE A LETTER:
Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean. "Reaches by name" is a fact on the terms' text: it does
not say that a value hangs on what is reached. (10) The two lemmas in numbers say what they say: no
security level is claimed by them. (11) BESIDE `bindsWith_written` and `bindsWith_plain` stand
`bindsWith_of_laws` and `bindsWith_plain_law` (Johnson/Goal/Conditions/BindsTold.lean): fewer
premises, no "in scope", two queries less.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.BindsAtCoins
import Johnson.Top.ToldCommitPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles

/-- The commitment at given coins does not read the number of coins. -/
theorem LayoutsByPublicReading.commitAtCoins_reBound {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (n : ℕ) (b₀ : R.LeafBody) (i : R.Index)
    (r : R.protocol.EncodingRandomness) (σ : ℕ → Rom.Bits) :
    (T.reBound n).commitAtCoins b₀ i r σ = T.commitAtCoins b₀ i r σ := rfl

end VerifiableInference.OnPublicFiles

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

variable {D : Description} {Q : HonestTerms D}

/-- **The committer with the coins fixed, written out**: general in D and Q. -/
theorem fixedCommit_plain {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q) (w : ModelWeights s) (r : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness)
    (σ : ℕ → Rom.Bits) :
    fixedCommit Q Z s w r σ = (Q.T Z).commitAtCoins (Q.b₀ Z) (Q.back Z s w) r σ :=
  commit_systemOn_plain (Q.T Z) (Q.b₀ Z) (Q.proveT Z) (Q.back Z s) (modelNextToken s) h.noCoin w r σ

variable (Q) (n : PublicFiles → ℕ)
  (coins' : (Z : PublicFiles) → Q.Rand → DeterministicAlgorithm (Fin (n Z + 1)))

/-- **Over the re-bound description**: the right side names neither the number of coins nor their
algorithm; and, where the word has a symbol for each leaf of the tree, any filling b. -/
theorem fixedCommit_reBound {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q)
    (fill : 2 ^ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout.depth ≤ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.wordLength)
    (b : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).LeafBody) (w : ModelWeights s)
    (r : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits) :
    fixedCommit (Q.reBound n coins') Z s w r σ =
      (Q.T Z).commitAtCoins b (Q.back Z s w) r σ :=
  (commit_systemOn_plain ((Q.T Z).reBound (n Z)) (Q.b₀ Z) (Q.proveT Z) (Q.back Z s)
    (modelNextToken s) h.noCoin w r σ).trans
    (commitAtCoins_filling (Q.T Z) (Q.b₀ Z) b fill (Q.back Z s w) r σ)

/-- **BINDING GOES OVER TO THE COMMITTER WRITTEN OUT, THE COINS IN THE OPENER's HAND**: general in
D and Q, at every error ε. reach: each setting of coins is the description's committer's at some
randomness. The system on the right is D's own but for the committer's side. -/
theorem bindsWith_written {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q)
    (fill : 2 ^ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout.depth ≤ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.wordLength)
    (b : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).LeafBody) (ε : ℕ → ℝ≥0∞)
    (binds : BindsWith (systemOfRecord ((D.reBound n).withTerms (Q.reBound n coins')) Z s)
      (((D.reBound n).withTerms (Q.reBound n coins')).extractor Z s) ε)
    (Coins : Type) (rOf : Coins → (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness)
    (σOf : Coins → ℕ → Rom.Bits)
    (reach : ∀ (w : ModelWeights s) (x : Coins), ∃ ρ : Q.Rand, ∀ hash : VerifiableInference.Hash,
      (((D.reBound n).withTerms (Q.reBound n coins')).commit Z s w ρ).evaluate hash =
        (fixedCommit (Q.reBound n coins') Z s w (rOf x) (σOf x)).evaluate hash)
    (sample : RandomizedAlgorithm Coins)
    (prove : ModelWeights s → Coins → List Token → List Token → RandomizedAlgorithm D.Form) :
    BindsWith ((systemOfRecord D Z s).withRandomness Coins sample
      (fun w x => (Q.T Z).commitAtCoins b (Q.back Z s w) (rOf x) (σOf x)) prove)
      ((Q.T Z).extractorOn (Q.φ Z s)) ε := by
  rw [LayoutsByPublicReading.extractorOn_eq]
  exact BindsWith.mapRandomness
    (systemOfRecord ((D.reBound n).withTerms (Q.reBound n coins')) Z s) _ ε binds Coins sample
    (fun w x => (Q.T Z).commitAtCoins b (Q.back Z s w) (rOf x) (σOf x)) prove
    (fun w x => Classical.choose (reach w x))
    (fun w x hash => ((Classical.choose_spec (reach w x) hash).trans
      (congrArg (fun A : DeterministicAlgorithm Commitment => A.evaluate hash)
        (fixedCommit_reBound Q n coins' h fill b w (rOf x) (σOf x)))).symm)

/-- The count of the committer written out: the told committer's, with the query for the key's
code. -/
theorem commitAtCoins_count {Z : PublicFiles} {s : IntegerTransformer.Settings} {tP q : ℕ}
    (h : BindLaws Q Z s tP q)
    (fill : 2 ^ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).queryLayout.depth ≤ (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.wordLength)
    (b : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).LeafBody) (w : ModelWeights s)
    (r : (D.input Z (Q.c₀ Z) (Q.m₀ Z)).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits) :
    ((Q.T Z).commitAtCoins b (Q.back Z s w) r σ).toRandomized.QueryBound (Q.tCommit Z tP + 1) := by
  rw [← commitAtCoins_filling (Q.T Z) (Q.b₀ Z) b fill (Q.back Z s w) r σ,
    ← fixedCommit_plain h w r σ]
  exact fixedCommit_count h w r σ

/-- In numbers: up to 2^70 queries the named error is at most 2^-114. -/
theorem epsBind_at_70 (t : ℕ) (ht : t ≤ 2 ^ 70) :
    epsBind honestBudget (t + 2) ≤ (2 : ℝ≥0∞)⁻¹ ^ 114 := by
  unfold epsBind honestBudget
  have h1 : t + 2 + 2 * 2 ^ 48 + 2 ≤ 2 ^ 70 + 2 ^ 50 := by
    have e1 : (2 : ℕ) ^ 50 = 4 * 2 ^ 48 := by norm_num
    have e2 : 4 ≤ (2 : ℕ) ^ 48 := by norm_num
    omega
  have h2 : 3 * (t + 2 + 2 * 2 ^ 48 + 2) ^ 2 ≤ 2 ^ 142 :=
    le_trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left h1 2)) (by norm_num)
  calc ((3 * (t + 2 + 2 * 2 ^ 48 + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256
      ≤ ((2 ^ 142 : ℕ) : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (Nat.cast_le.2 h2) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ 114 := by
      rw [← ENNReal.inv_pow,
        show (2 : ℝ≥0∞) ^ 256 = ((2 ^ 142 : ℕ) : ℝ≥0∞) * 2 ^ 114 by push_cast; norm_num,
        ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_assoc,
        mul_comm ((2 : ℝ≥0∞) ^ 114)⁻¹, ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
        one_mul]

/-- In numbers: up to 2^126 queries the named error is at most (t + 1) / 2^128. -/
theorem epsBind_under_line (t : ℕ) (ht : t ≤ 2 ^ 126) :
    epsBind honestBudget (t + 2) ≤ ((t + 1 : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  unfold epsBind honestBudget
  have h1 : 3 * t + 6 * (2 * 2 ^ 48 + 4) ≤ 2 ^ 128 := by
    have e1 : (2 : ℕ) ^ 128 = 4 * 2 ^ 126 := by norm_num
    have e2 : 6 * (2 * 2 ^ 48 + 4) ≤ (2 : ℕ) ^ 126 := by norm_num
    omega
  have h2 : 3 * (2 * 2 ^ 48 + 4) ^ 2 ≤ 2 ^ 128 := by norm_num
  have key : 3 * (t + 2 + 2 * 2 ^ 48 + 2) ^ 2 ≤ (t + 1) * 2 ^ 128 := by
    have e : 3 * (t + 2 + 2 * 2 ^ 48 + 2) ^ 2 =
        t * (3 * t + 6 * (2 * 2 ^ 48 + 4)) + 3 * (2 * 2 ^ 48 + 4) ^ 2 := by ring
    have e' : (t + 1) * 2 ^ 128 = t * 2 ^ 128 + 2 ^ 128 := by ring
    rw [e, e']
    exact Nat.add_le_add (Nat.mul_le_mul_left t h1) h2
  have e2 : ((t + 1 : ℕ) : ℝ≥0∞) / 2 ^ 128 = (((t + 1) * 2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add],
      ENNReal.mul_div_mul_right _ _ (pow_ne_zero 128 (by norm_num))
        (ENNReal.pow_ne_top (by norm_num))]
  rw [e2]
  exact ENNReal.div_le_div_right (Nat.cast_le.2 key) _

end VerifierAndGoals.Fit

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows
  FlashProve.thePlan FlashProve.theItem

/-- The tree has no leaf beyond the word. -/
theorem leaves_R₀ (Z : PublicFiles) : 2 ^ (R₀ Z).queryLayout.depth ≤ (R₀ Z).protocol.wordLength := le_of_eq rfl

/-- **The description's told record**: it names neither K nor W. -/
def T₀ (Z : PublicFiles) : LayoutsByPublicReading (R₀ Z) :=
  layoutsByPublicReadingAtDescriptionOfFields (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀) allZeroDigest [] Z

/-- It is the told record of the honest side's terms, at every K. -/
theorem T_the (K : TheCoins) (Z : PublicFiles) : (theTerms K).T Z = T₀ Z := rfl

section Fields
open VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- Lean compares these by their names. -/
attribute [local irreducible] OnBytes.K.Arm.Pub.pub8 PV.EncId.encF LPFD.Full.mD LPFD.Full.mOneAt
  PV.MFull.cfgF

/-- **Three of its fields**: the public reading is `pub8` (Johnson/Top/PreThreePub.lean) at
`recordGround` and the three public files of Z's head; the told part is `cfg8`: of the eight answers
the one at the string of these three files; the told code is `encF`. -/
theorem T₀_fields (Z : PublicFiles) :
    (T₀ Z).Pub = OnBytes.K.Arm.Pub.pub8 OnBytes.Tie.recordGround (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL
        (asDescriptionFiles Z).lay ∧
      (T₀ Z).part = OnBytes.K.Arm.Pub.cfg8 ∧
      (T₀ Z).encT = fun k => PV.EncId.encF k.1 k.2.cm k.2.rcd :=
  ⟨rfl, rfl, rfl⟩

/-- **The coding at d**: `LPFD.Full.mD` (Johnson/Flat/Told/Dec/TAt.lean) at the parts of
`dataAtFiles flashProveData Z`, the request's item among them. -/
theorem T₀_m (Z : PublicFiles) :
    (T₀ Z).m = LPFD.Full.mD (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E (dataAtFiles flashProveData Z).G
      (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).runP
      (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).P (dataAtFiles flashProveData Z).hStar (dataAtFiles flashProveData Z).it
      (dataAtFiles flashProveData Z).sR (dataAtFiles flashProveData Z).hDK (dataAtFiles flashProveData Z).hDP (dataAtFiles flashProveData Z).hK := rfl

/-- **The seed's wire at d**: `outOfDomainSampleQueryLayoutOfCode` (Johnson/Flat/SeedTwin.lean) at the letters of
`(dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []`; it hangs on d through its list of digests alone: `cfgF` at the
bytes of d's first answer. -/
theorem T₀_Sd (Z : PublicFiles) (d : D8) :
    (T₀ Z).Sd d = outOfDomainSampleQueryLayoutOfCode (R₀ Z).protocol (R₀ Z).LeafBody (R₀ Z).offlineRoundSplits (R₀ Z).linkRoundSplits (v := frS.P.v) (lg := 29) (s := 1)
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).t (PV.MFull.cfgF (digToBytes d.1))
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).shape ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).pl0
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).pl1 ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).num
      (recSeedK recT recLg recS ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).W.K
        ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []).hK) id seedEqFull := rfl

end Fields

/- From here on Lean compares these by their names. -/
attribute [local irreducible] descriptionOfDataOnBytes T₀

/-- **THE COMMITTER WITH THE COINS FIXED, AT THE DESCRIPTION: THE RIGHT SIDE NAMES NEITHER K NOR
W**, and any filling b. -/
theorem fixedCommit_theWide (K : TheCoins) (W : WideCoins K) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) (r : (R₀ Z).protocol.EncodingRandomness)
    (σ : ℕ → Rom.Bits) (b : (R₀ Z).LeafBody) :
    fixedCommit (theWideTerms K W) Z (settingsOfRead pp) w r σ =
      (T₀ Z).commitAtCoins b (backThe Z (settingsOfRead pp) w) r σ :=
  T_the K Z ▸ fixedCommit_reBound (theTerms K) W.bound
    (fun Z => coinsAnchor Z (K.shape Z) (W.gen Z)) (bindLaws_the K hE_the Z pp hr) (leaves_R₀ Z) b
    w r σ

/-- **The committer's coins at Z**: pads with tails, and salts that have the salts' length at the
tree's places. -/
def Coins₀ (Z : PublicFiles) : Type :=
  { x : (R₀ Z).protocol.EncodingRandomness × (ℕ → Rom.Bits) //
    ∀ j, j < 2 ^ (R₀ Z).queryLayout.depth → (x.2 j).length = (R₀ Z).compilerParameters.sMT }

/-- They are `CoinsOf K W Z`, at every K and W. -/
theorem coinsOf_eq (K : TheCoins) (W : WideCoins K) (Z : PublicFiles) : CoinsOf K W Z = Coins₀ Z := rfl

/-- **The system**: `descriptionOfDataOnBytes flashProveData`'s system of record with these coins for the committer's
randomness and the commitment at given coins for its committer, in the place of its own, which is
hollow. b: a filling; sample, prove: any. -/
def plainSystem (Z : PublicFiles) (s : IntegerTransformer.Settings) (b : (R₀ Z).LeafBody)
    (sample : RandomizedAlgorithm (Coins₀ Z))
    (prove : ModelWeights s → Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) : ArgumentSystem :=
  (systemOfRecord flashProveDescription Z s).withRandomness (Coins₀ Z) sample
    (fun w x => (T₀ Z).commitAtCoins b (backThe Z s w) x.1.1 x.1.2) prove

/-- From any K that covers the coins, at every error at which `theWide` binds. K is a tool of the
proof: the conclusion does not name it. -/
theorem bindsWith_plain_of (K : TheCoins) (toNat : K.Rand → ℕ) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (hr : readFiles Z = .ok pp) (hK : K.Covers Z)
    (onto : ∀ n, n < ((K.ri Z).n + 1) * ((K.sl Z).n + 1) → ∃ ρ, toNat ρ = n) (ε : ℕ → ℝ≥0∞)
    (binds : BindsWith
      (systemOfRecord (atSecondHashFunction (theWide K (WideCoins.full K toNat))) Z (settingsOfRead pp))
      ((atSecondHashFunction (theWide K (WideCoins.full K toNat))).extractor Z (settingsOfRead pp)) ε)
    (b : (R₀ Z).LeafBody) (sample : RandomizedAlgorithm (Coins₀ Z))
    (prove : ModelWeights (settingsOfRead pp) → Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) :
    BindsWith (plainSystem Z (settingsOfRead pp) b sample prove)
      ((T₀ Z).extractorOn (phiThe Z (settingsOfRead pp))) ε := by
  unfold plainSystem
  rw [← T_the K Z]
  exact bindsWith_written (theTerms K) (WideCoins.full K toNat).bound
    (fun Z => coinsAnchor Z (K.shape Z) ((WideCoins.full K toNat).gen Z))
    (bindLaws_the K hE_the Z pp hr) (leaves_R₀ Z) b ε binds (Coins₀ Z) (fun x => x.1.1)
    (fun x => x.1.2)
    (fun w x => coins_enumerated_of K toNat OnBytes.secondHashFunction Z pp hr hK onto w x.1.1 x.1.2 x.2)
    sample prove

/-- **BINDING OVER THE DESCRIPTION's TOLD RECORD, THE COINS IN THE OPENER's HAND, THE COMMITTER
WRITTEN OUT: AT THE NAMED ERROR**: 3 (t + 2 + 2 · 2^48 + 2)² / 2^256: no term that is linear in the
queries beside the square (whose cross term is about 2^-204 a query). -/
theorem bindsWith_plain (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (b : (R₀ Z).LeafBody) (sample : RandomizedAlgorithm (Coins₀ Z))
    (prove : ModelWeights (settingsOfRead pp) → Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) :
    BindsWith (plainSystem Z (settingsOfRead pp) b sample prove)
      ((T₀ Z).extractorOn (phiThe Z (settingsOfRead pp))) fun t => epsBind honestBudget (t + 2) :=
  bindsWith_plain_of placeHolderNumberCoins.digits (fun n : ℕ => n) Z pp hr
    (covers_digits placeHolderNumberCoins Z) (fun n _ => ⟨n, rfl⟩) _
    (bindsAt_withTerms (theWideTerms digitCoins digitWide) 8 2
      (fun Z pp _ h₂ => bindLaws_wide digitCoins digitWide Z pp h₂) Z pp hs hr).2 b sample prove

/-- The same at the goal's line `bindingErrorInQueries` (Ladder/Bits.lean), which is the looser. -/
theorem bindsWith_plain_bits (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (b : (R₀ Z).LeafBody) (sample : RandomizedAlgorithm (Coins₀ Z))
    (prove : ModelWeights (settingsOfRead pp) → Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) :
    BindsWith (plainSystem Z (settingsOfRead pp) b sample prove)
      ((T₀ Z).extractorOn (phiThe Z (settingsOfRead pp))) bindingErrorInQueries :=
  bindsWith_plain_of placeHolderNumberCoins.digits (fun n : ℕ => n) Z pp hr
    (covers_digits placeHolderNumberCoins Z) (fun n _ => ⟨n, rfl⟩) _
    (G9bits_theWide digitCoins digitWide Z pp hs hr).2 b sample prove

/-- The written committer's count: the public reading's eight queries, two for each leaf of the
tree, the seed's two typed queries of K + 1 digests each, one for the key's code. -/
def count₀ (Z : PublicFiles) : ℕ := 8 + (2 * 2 ^ (R₀ Z).queryLayout.depth + 2 * ((R₀ Z).queryLayout.K + 1)) + 1

theorem count₀_le (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) :
    count₀ Z ≤ honestBudget :=
  le_trans (Nat.le_add_left _ 2) (bindLaws_the placeHolderNumberCoins hE_the Z pp hr).number

/-- It is the count of the honest side's terms, at every K. -/
theorem count₀_eq (K : TheCoins) (Z : PublicFiles) : (theTerms K).tCommit Z 8 + 1 = count₀ Z := rfl

/- From here on Lean compares these by their names. -/
attribute [local irreducible] LayoutsByPublicReading.commitAtCoins count₀

theorem plain_count (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (b : (R₀ Z).LeafBody)
    (w : ModelWeights (settingsOfRead pp)) (r : (R₀ Z).protocol.EncodingRandomness) (σ : ℕ → Rom.Bits) :
    ((T₀ Z).commitAtCoins b (backThe Z (settingsOfRead pp) w) r σ).toRandomized.QueryBound
      (count₀ Z) := by
  have h := commitAtCoins_count (theTerms placeHolderNumberCoins)
    (bindLaws_the placeHolderNumberCoins hE_the Z pp hr) (leaves_R₀ Z) b w r σ
  rw [T_the, count₀_eq] at h
  exact h

/-- There is a filling of the tree's spare leaves, at every Z. -/
theorem filling₀_nonempty (Z : PublicFiles) : Nonempty (R₀ Z).LeafBody := ⟨placeHolderNumberCoins.b₀ Z⟩

/-- There are such coins, at every Z: any pads with tails, and salts of zeros. -/
theorem coins₀_nonempty (Z : PublicFiles) : Nonempty (Coins₀ Z) :=
  ⟨⟨(Classical.arbitrary _, fun _ => List.replicate (R₀ Z).compilerParameters.sMT false),
    fun _ _ => List.length_replicate⟩⟩

/-- **IT IS NOT EMPTY** (given a Z in scope that is read): from a commitment at any weights and any
coins, and the queries of that run, the extractor gives the weights back, but with probability the
named error at that run's count, which is within the honest side's budget. -/
theorem extracts_plain (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (b : (R₀ Z).LeafBody) (w : ModelWeights (settingsOfRead pp))
    (x : Coins₀ Z) :
    Prob ((T₀ Z).commitAtCoins b (backThe Z (settingsOfRead pp) w) x.1.1
        x.1.2).toRandomized.withQueryLog
        {c | (T₀ Z).extractorOn (phiThe Z (settingsOfRead pp)) c.1 c.2 ≠ some w}
      ≤ epsBind honestBudget (count₀ Z + 2) :=
  (bindsWith_plain Z pp hs hr b (.done x) fun w' _ =>
    (theTerms placeHolderNumberCoins).prove Z (settingsOfRead pp) w' (0 : ℕ)).atRandomness w x
      (count₀ Z) (plain_count Z pp hr b w x.1.1 x.1.2)

/-- **NOBODY OPENS ONE COMMITMENT TO TWO DIFFERENT WEIGHTS, EACH AT COINS OF ITS OWN PICK**, but
with probability twice the named error. -/
theorem noTwoOpenings_plain (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true)
    (hr : readFiles Z = .ok pp) (b : (R₀ Z).LeafBody) (sample : RandomizedAlgorithm (Coins₀ Z))
    (prove : ModelWeights (settingsOfRead pp) → Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) :
    NoTwoOpenings (plainSystem Z (settingsOfRead pp) b sample prove)
      fun t => 2 * epsBind honestBudget (t + 2) :=
  (bindsWith_plain Z pp hs hr b sample prove).noTwoOpenings

/-- **A named premise**: given `FilesRead`, the full set's files are in scope and
read, and there are weights and coins there. -/
theorem read_weights_and_coins₀ (h : FilesRead) :
    ∃ pp, InScope storedPublicFiles = true ∧ readFiles storedPublicFiles = .ok pp ∧
      Nonempty (ModelWeights (settingsOfRead pp) × Coins₀ storedPublicFiles) :=
  let ⟨hs, pp, hr, _⟩ := h.full
  ⟨pp, hs, hr, ⟨(nonempty_modelWeights (valid_of_read hr)).some, (coins₀_nonempty storedPublicFiles).some⟩⟩

end FlashProve

#print axioms VerifierAndGoals.Fit.commitAtCoins_count
#print axioms VerifierAndGoals.Fit.epsBind_at_70
#print axioms VerifierAndGoals.Fit.epsBind_under_line
#print axioms FlashProve.T₀_fields
#print axioms FlashProve.T₀_m
#print axioms FlashProve.T₀_Sd
#print axioms FlashProve.count₀_le
#print axioms FlashProve.count₀_eq
#print axioms FlashProve.plain_count
#print axioms FlashProve.filling₀_nonempty
#print axioms FlashProve.coins₀_nonempty
#print axioms FlashProve.extracts_plain
#print axioms FlashProve.noTwoOpenings_plain
#print axioms FlashProve.read_weights_and_coins₀
#print axioms VerifiableInference.OnPublicFiles.LayoutsByPublicReading.commitAtCoins_reBound
#print axioms VerifierAndGoals.Fit.fixedCommit_plain
#print axioms VerifierAndGoals.Fit.fixedCommit_reBound
#print axioms VerifierAndGoals.Fit.bindsWith_written
#print axioms FlashProve.leaves_R₀
#print axioms FlashProve.T_the
#print axioms FlashProve.fixedCommit_theWide
#print axioms FlashProve.coinsOf_eq
#print axioms FlashProve.bindsWith_plain_of
#print axioms FlashProve.bindsWith_plain
#print axioms FlashProve.bindsWith_plain_bits
