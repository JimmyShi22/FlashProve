-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean: BINDING OVER THE TOLD RECORD OF `VerifierAndGoals.theDescriptionO
o`, WHATEVER FUNCTION o STANDS IN THE SECOND HASH FUNCTION'S PLACE: the committer, the extractor
and the system as closed terms in which o is a letter. Definitions, statements and proofs.

Why. A rule laid on this library, no theorem: the verifier and the proofs that go with it are always
to treat the hash function as a random oracle. The closed terms of which binding of the commitment
in the opening form was stated (Johnson/Goal/Conditions/BindsPlain.lean, BindsTold.lean: the written
committer (written in Lean beside the IOP: a placeholder that corresponds to no program of the
release), the extractor,
`plainSystem`) reach concrete hash functions by name. Here the same three are written over the
description that takes o as its argument (Johnson/Goal/Description/AtSecondHashFunction.lean), over the told
record with the request's item and the parameter bytes as letters (`DescriptionDataAtFiles.layoutsByPublicReadingWithParameterBytes`,
Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean), and the law at letters (`bindsD`,
Johnson/Goal/Conditions/BindsLetters.lean) is applied.

Main names (namespace `FlashProve`). o : SecondHashFunctionType stands in front of each.
  `theLayAt_hl`, `theLayAt_hd₁`, `theLayAt_hd₂`, `fit_theLayAt`, `parts_at`: the one test on numbers
    says yes at the letters of `dataAtFiles (flashProveDataAtSecondHash o) Z`, at every o and Z: by `fit_built`
    (Johnson/Goal/Conditions/NumbersAtThe.lean) and `theLiveAt_frame`.
  `parAt o Z` := `par7O o recordGround` at the three public files
    (Johnson/Goal/Reads/ReadAtSecondHashFunction.lean): what the description's further public reading hashes.
    `RAt o Z`: the description's own input at zeros and no further digests. `TAt o Z` := `(dataAtFiles
    (flashProveDataAtSecondHash o) Z).layoutsByPublicReadingWithParameterBytes allZeroDigest [] (parAt o Z)`: THE TOLD RECORD.
  `phiAt`, `backAt`: between the extractor's matrix and weights. `CoinsAt o Z`: pads with tails, and
    salts of the wire's length at the tree's places.
  **`committerAt o Z s b w x`** := `(TAt o Z).commitAtCoins b (backAt o Z s w) x.1.1 x.1.2`.
    **`extractorAt o Z s`** := `(TAt o Z).extractorOn (phiAt o Z s)`. **`plainSystemAt o Z s b
    sample prove`**: the system of record of `theDescriptionO o` with these coins for the
    committer's randomness and `committerAt` for its committer.
  THE TIES TO THE DESCRIPTION, at every o and Z. **`TAt_at`**: the record's input at d is the
    description's own input at d. `TAt_fits`: the compiled verifier at the one is the compiled
    verifier at the other. **`TAt_reads`**: the description's two public readings return what the
    record's public reading returns (by `readBothO_reads`, Johnson/Goal/Reads/ReadAtSecondHashFunction.lean).
    **`extractor_atOlder`**: `extractorAt o Z s` IS the description's own extractor
    `(theDescriptionO o).extractor Z s`, at every s.
  `sec_at`, `back_at`, `dec_at`: φ gives w back from `backAt … w`; the decoder gives back the index
    of every w (the coding is `codingCells`: `hE_the`).
  **`bindsWith_atOlder`**: at every o, every Z whose files are read, every filling b, sample and
    prove: `BindsWith (plainSystemAt o Z (settingsOfRead pp) b sample prove) (extractorAt o Z
    (settingsOfRead pp)) (epsBind honestBudget)`: 3 (t + 2 · 2^48 + 2)² / 2^256. SO THE TWELVE
    PREMISES OF `bindsD` ARE MET TOGETHER.
  `bindsWith_atOlder_at_70`: the number in the statement: 2^-114 while t ≤ 2^70; beyond: nothing.
    `noTwoOpenings_atOlder`: nobody opens one commitment to two different weights, at twice the
    error.
  `commitAtCoins_within` (namespace `VerifiableInference.OnPublicFiles`): the written committer's count,
    general in the input and the record. `countAt`, `countAt_le`, `committerAt_count`,
    `coinsAt_nonempty`, `fillingAt_nonempty`, **`extracts_atOlder`**: IT IS NOT EMPTY: from a
    commitment at any weights and coins and that run's queries the extractor gives the weights back,
    but with probability the named error at `countAt o Z`, which is within the honest side's budget.

Every "there is": none, in premises or conclusions. o, Z, pp, b, sample, prove stand under "for
all", before the hash function is drawn.
Limits. (1) THE COMMITTER STANDS BESIDE THE DESCRIPTION, NOT IN IT: the honest side of
`theDescriptionO o` is hollow (`theHonest := fixedCommitterAndProver`, Johnson/Goal/Description/Honest.lean); of its
system of record opening-form binding and `NoTwoOpenings` read the type of weights alone. The input, the told record's input at d,
its public reading and the extractor are the description's own (`RAt` by definition; `TAt_at`,
`TAt_reads`, `extractor_atOlder`). (2) WHAT A FREE o SAYS: nothing is asked of the second hash
function. It does not make that function a random oracle, and covers no o that hangs on the drawn
function. The goals G9 and G9bits read a description at `OnBytes.secondHashFunction` (`atSecondHashFunction`,
Ladder.lean): these statements stand beside them. (3) That at `OnBytes.secondHashFunction` the told record, the
extractor and the committer are those of BindsPlain.lean is not shown here. (4) WHETHER THE THREE
TERMS REACH A CONCRETE HASH
FUNCTION BY NAME IS A WALK'S MATTER, NO THEOREM'S. This file, BindsLetters.lean, BindsLaw.lean and
the told record's files (FamilyBy.lean, TAtBy.lean) name none. Beneath `flashProveDataAtSecondHash o` it hangs on what
sits in the lay's seats (Johnson/Goal/Description/): a seat that calls plannedAt
(OnBytes/Tie/ChainsAtCfg.lean) brings `OnBytes.formatHashFastForm`, `Fmt.HF` and `OnBytes.secondHashFunction` beneath all
three; so does an extractor laid at
`DescriptionDataAtFiles.layoutsByPublicReading` (through `pub8`). (5) Those of BindsLaw.lean: the fence; the verifier is idle; values,
not algorithms. WHERE `protocolDataWellFormedAt o` SAYS NO (so wherever the planner's text at o refuses the files)
THE PLAN WITHOUT DEPTH AND EMPTY DATA ARE LAID: opening-form binding, `NoTwoOpenings` and `extracts_atOlder` hold there too, with content, OF THE
COMMITTER OVER THAT DEAD FRAME, not over the release's. That `protocolDataWellFormedAt o` says yes at the release's
files is typed nowhere here. At `settingsOfRead pp` alone. The one premise, that the files are read,
is met at no named Z in this file: that is an evaluation's matter. Nothing on soundness,
completeness or hiding; no program's commitment is spoken of; no security level is claimed.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.BindsLetters
import Johnson.Goal.Conditions.BindsTold
import Johnson.Goal.Description.AtSecondHashFunction
import Johnson.Goal.Description.AtBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **The written committer's count**, general in the input and the told record: the public
reading's queries, two for each leaf of the tree, the seed's two typed queries of K + 1 digests
each, one for the key's code. The count is a letter with an equation. It asks less than
`commitAtCoins_count` (Johnson/Goal/Conditions/BindsPlain.lean): no description, no terms, no
premise on the filling. -/
theorem commitAtCoins_within {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b : R.LeafBody) (noCoin : T.Pub.NoCoin)
    (tP : ℕ) (reading : T.Pub.QueryBound tP) (i : R.Index) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) (c : ℕ)
    (hc : tP + (2 * 2 ^ R.queryLayout.depth + 2 * (R.queryLayout.K + 1)) + 1 = c) :
    (T.commitAtCoins b i r σ).toRandomized.QueryBound c := by
  subst hc
  have e : _ = T.commitAtCoins b i r σ := commit_systemOn_plain T b
    (fun _ l => .pure ⟨l.map fun _ => T.π₀.2, List.length_map ..⟩) (id : R.Index → R.Index)
    (fun _ _ => none) noCoin i r σ
  rw [← e]
  exact queryBound_commit_systemOn T (enumOne r) (enumOne σ) b _ id (fun _ _ => none) tP reading i _

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/-! ## 1 The numbers at o -/

theorem theLayAt_hl (o : SecondHashFunctionType) (Zk : OnBytes.K.Pub) (h : (flashProveDataAtSecondHash o).live Zk = true) :
    sizeNumbersFitAtFullSize (KF ((flashProveDataAtSecondHash o).DK Zk) ((flashProveDataAtSecondHash o).DP Zk)) theQueries
      ((flashProveDataAtSecondHash o).G Zk).c.first.binding.logLeaves
      ((flashProveDataAtSecondHash o).G Zk).k.oneTime.binding.logLeaves ((flashProveDataAtSecondHash o).DK Zk) ((flashProveDataAtSecondHash o).DP Zk)
      dsFull frD.xs = true := by
  have h1 := theLiveAt_frame o Zk h
  unfold VerifiableInference.OnPublicFiles.sizeNumbersFitAtPlan at h1
  exact h1

theorem theLayAt_hd₁ (o : SecondHashFunctionType) (Zk : OnBytes.K.Pub) :
    ((flashProveDataAtSecondHash o).Gd Zk).c.first.binding.logLeaves = 0 := FilesParameters.noDepth_first (thePlanAt o Zk)

theorem theLayAt_hd₂ (o : SecondHashFunctionType) (Zk : OnBytes.K.Pub) :
    ((flashProveDataAtSecondHash o).Gd Zk).k.oneTime.binding.logLeaves = 0 := FilesParameters.noDepth_oneTime (thePlanAt o Zk)

attribute [local irreducible] flashProveDataAtSecondHash in
/-- **The one test on numbers says yes at the family's letters, at every o and every Z.** -/
theorem fit_theLayAt (o : SecondHashFunctionType) (Z : PublicFiles) :
    sizeNumbersFitAtFullSize (KF (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP) theQueries
      (dataAtFiles (flashProveDataAtSecondHash o) Z).G.c.first.binding.logLeaves
      (dataAtFiles (flashProveDataAtSecondHash o) Z).G.k.oneTime.binding.logLeaves
      (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP dsFull frD.xs = true :=
  fit_built (flashProveDataAtSecondHash o) theQueries (by unfold theQueries; norm_num) (theLayAt_hl o)
    (theLayAt_hd₁ o) (theLayAt_hd₂ o) Z

/-- What that yes says. -/
theorem parts_at (o : SecondHashFunctionType) (Z : PublicFiles) :
    FrameFitFullD (KF (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP) theQueries
      (dataAtFiles (flashProveDataAtSecondHash o) Z).G.c.first.binding.logLeaves
      (dataAtFiles (flashProveDataAtSecondHash o) Z).G.k.oneTime.binding.logLeaves
      (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP dsFull frD.xs :=
  frameFitFullD_parts (fit_theLayAt o Z)

/-! ## 2 The closed terms, o a letter -/

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF theCoding theKeyDataAt
  theProofDataAt protocolDataWellFormedAt theDeadPlanAt theKeyGateAt theProofGateAt theLinkGateAt theProversAt
  theNamedAt thePlanAt theItemAt theExtractorAt par7O

variable (o : SecondHashFunctionType)

/-- The parameter bytes at o: what the description's further public reading hashes. -/
def parAt (Z : PublicFiles) : ByteArray → List ByteArray :=
  par7O o recordGround (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay

/-- The description's own input at o, at zeros and no further digests. -/
abbrev RAt (Z : PublicFiles) : InnerCompilerInput := (theDescriptionO o).input Z allZeroDigest []

/-- **THE TOLD RECORD AT o.** -/
def TAt (Z : PublicFiles) : LayoutsByPublicReading (RAt o Z) := (dataAtFiles (flashProveDataAtSecondHash o) Z).layoutsByPublicReadingWithParameterBytes allZeroDigest [] (parAt o Z)

/-- From the extractor's matrix to weights. -/
def phiAt (Z : PublicFiles) (s : IntegerTransformer.Settings) (M : (RAt o Z).Index) :
    Option (ModelWeights s) :=
  if hv : settingsAreValid s = true then VerifierAndGoals.Fit.phiO hv M else none

/-- The matrix of given weights. -/
def backAt (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) : (RAt o Z).Index :=
  if hv : settingsAreValid s = true then VerifierAndGoals.Fit.backO hv w
  else Flat.matrixOf (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero)

/-- **The coins**: pads with tails, and salts of the wire's length at the tree's places. -/
def CoinsAt (Z : PublicFiles) : Type :=
  { x : (RAt o Z).protocol.EncodingRandomness × (ℕ → Rom.Bits) //
    ∀ j, j < 2 ^ (RAt o Z).queryLayout.depth → (x.2 j).length = (RAt o Z).compilerParameters.sMT }

/-- **THE COMMITTER AT o**, written out (`LayoutsByPublicReading.commitAtCoins`,
Johnson/Top/ToldCommitPlain.lean). -/
def committerAt (Z : PublicFiles) (s : IntegerTransformer.Settings) (b : (RAt o Z).LeafBody)
    (w : ModelWeights s) (x : CoinsAt o Z) : DeterministicAlgorithm Commitment :=
  (TAt o Z).commitAtCoins b (backAt o Z s w) x.1.1 x.1.2

/-- **THE EXTRACTOR AT o.** -/
def extractorAt (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    Commitment → QueryLog → Option (ModelWeights s) :=
  (TAt o Z).extractorOn (phiAt o Z s)

/-- **THE SYSTEM AT o**: the description's system of record with these coins for the committer's
randomness and the written committer in the place of its own, which is hollow. -/
def plainSystemAt (Z : PublicFiles) (s : IntegerTransformer.Settings) (b : (RAt o Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt o Z))
    (prove : ModelWeights s → CoinsAt o Z → List Token → List Token →
      RandomizedAlgorithm (theDescriptionO o).Form) : ArgumentSystem :=
  (systemOfRecord (theDescriptionO o) Z s).withRandomness (CoinsAt o Z) sample
    (committerAt o Z s b) prove

/-! ## 3 The ties to the description -/

/-- **The record's input at d is the description's own input at d.** -/
theorem TAt_at (Z : PublicFiles) (d : D8) : (TAt o Z).at d = (theDescriptionO o).input Z d.1 d.2 :=
  LPFD.Full.at_toldDBy (dataAtFiles (flashProveDataAtSecondHash o) Z).A (dataAtFiles (flashProveDataAtSecondHash o) Z).E (dataAtFiles (flashProveDataAtSecondHash o) Z).G
    (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP (dataAtFiles (flashProveDataAtSecondHash o) Z).runK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).runP (dataAtFiles (flashProveDataAtSecondHash o) Z).dec (dataAtFiles (flashProveDataAtSecondHash o) Z).P
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hStar (dataAtFiles (flashProveDataAtSecondHash o) Z).it (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL
    (asDescriptionFiles Z).lay (parAt o Z) (dataAtFiles (flashProveDataAtSecondHash o) Z).sR (dataAtFiles (flashProveDataAtSecondHash o) Z).hDK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hDP (dataAtFiles (flashProveDataAtSecondHash o) Z).hK (dataAtFiles (flashProveDataAtSecondHash o) Z).N
    (dataAtFiles (flashProveDataAtSecondHash o) Z).d₀ (allZeroDigest, []) d

/-- **The compiled verifier at the description's input at (c, m) is the one at the record's.** -/
theorem TAt_fits (Z : PublicFiles) (c : Digest) (m : List (Dig 256)) (commitment : Commitment)
    (prompt output : List Token)
    (proof : TypedProof ((theDescriptionO o).F Z) ((theDescriptionO o).P Z)) :
    innerCompiledVerifier ((theDescriptionO o).input Z c m) commitment prompt output proof =
      innerCompiledVerifier ((TAt o Z).at (c, m)) commitment prompt output proof :=
  LPFD.Full.fitsDBy (dataAtFiles (flashProveDataAtSecondHash o) Z).A (dataAtFiles (flashProveDataAtSecondHash o) Z).E (dataAtFiles (flashProveDataAtSecondHash o) Z).G
    (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP (dataAtFiles (flashProveDataAtSecondHash o) Z).runK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).runP (dataAtFiles (flashProveDataAtSecondHash o) Z).dec (dataAtFiles (flashProveDataAtSecondHash o) Z).P
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hStar (dataAtFiles (flashProveDataAtSecondHash o) Z).it (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL
    (asDescriptionFiles Z).lay (parAt o Z) (dataAtFiles (flashProveDataAtSecondHash o) Z).sR (dataAtFiles (flashProveDataAtSecondHash o) Z).hDK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hDP (dataAtFiles (flashProveDataAtSecondHash o) Z).hK (dataAtFiles (flashProveDataAtSecondHash o) Z).N
    (dataAtFiles (flashProveDataAtSecondHash o) Z).d₀ (allZeroDigest, []) (c, m) commitment prompt output proof

/-- **The description's two public readings return what the record's public reading returns.** -/
theorem TAt_reads (Z : PublicFiles) (hash : VerifiableInference.Hash) :
    (Fit.readBoth (theDescriptionO o) Z allZeroDigest [] (TAt o Z) Prod.mk).evaluate hash =
      (TAt o Z).Pub.det fun _ => hash := by
  refine Eq.trans ?_ (readBothO_reads o recordGround Z hash)
  rw [readBothO_evaluate]
  unfold Fit.readBoth
  rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen]
  show (_, (readMoreAtO o recordGround Z _).evaluate hash) = _
  rw [readMoreAtO_evaluate, readConfig_evaluate]

/-- **`extractorAt` is the description's own extractor**, at every setting. -/
theorem extractor_atOlder (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    (theDescriptionO o).extractor Z s = extractorAt o Z s := by
  unfold extractorAt
  rw [LayoutsByPublicReading.extractorOn_eq]
  show theExtractorAt o (asDescriptionFiles Z) s = _
  unfold theExtractorAt
  rfl

/-! ## 4 The laws on back and φ -/

theorem sec_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) :
    phiAt o Z (settingsOfRead pp) (backAt o Z (settingsOfRead pp) w) = some w := by
  unfold phiAt backAt
  rw [dif_pos (valid_of_read hr), dif_pos (valid_of_read hr)]
  exact VerifierAndGoals.Fit.section_backO (valid_of_read hr) w

theorem back_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) :
    backAt o Z (settingsOfRead pp) w = Flat.matrixOf (indexOfWeights (valid_of_read hr) w) :=
  dif_pos (valid_of_read hr)

theorem dec_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (r : (RAt o Z).protocol.EncodingRandomness) (sd : (RAt o Z).protocol.OutOfDomainSeed) :
    (RAt o Z).protocol.decodeIndex ((RAt o Z).protocol.encodeIndex (backAt o Z (settingsOfRead pp) w) r)
      ((RAt o Z).protocol.recOf (backAt o Z (settingsOfRead pp) w) r sd) =
      some (backAt o Z (settingsOfRead pp) w) := by
  rw [back_at o Z pp hr w]
  exact decodes_of_eq (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) (theCoding (asDescriptionFiles Z))
    (hE_the (asDescriptionFiles Z)) ((theDescriptionO o).F Z) ((theDescriptionO o).P Z) _ r sd

/-! ## 5 Binding -/

/-- **BINDING OVER THE DESCRIPTION's TOLD RECORD, WHATEVER FUNCTION STANDS IN THE SECOND HASH
FUNCTION's PLACE**: at every o and every Z whose files are read: the coins in the opener's hand, the
committer written out, at the named error 3 (t + 2 · 2^48 + 2)² / 2^256. -/
theorem bindsWith_atOlder (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (b : (RAt o Z).LeafBody) (sample : RandomizedAlgorithm (CoinsAt o Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt o Z → List Token → List Token →
      RandomizedAlgorithm (theDescriptionO o).Form) :
    BindsWith (plainSystemAt o Z (settingsOfRead pp) b sample prove)
      (extractorAt o Z (settingsOfRead pp)) (epsBind honestBudget) :=
  LPFD.Full.bindsD (dataAtFiles (flashProveDataAtSecondHash o) Z).A (dataAtFiles (flashProveDataAtSecondHash o) Z).E (dataAtFiles (flashProveDataAtSecondHash o) Z).G
    (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP (dataAtFiles (flashProveDataAtSecondHash o) Z).runK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).runP (dataAtFiles (flashProveDataAtSecondHash o) Z).dec (dataAtFiles (flashProveDataAtSecondHash o) Z).P
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hStar (dataAtFiles (flashProveDataAtSecondHash o) Z).it (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL
    (asDescriptionFiles Z).lay (parAt o Z) (dataAtFiles (flashProveDataAtSecondHash o) Z).sR (dataAtFiles (flashProveDataAtSecondHash o) Z).hDK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hDP (dataAtFiles (flashProveDataAtSecondHash o) Z).hK (dataAtFiles (flashProveDataAtSecondHash o) Z).N
    (dataAtFiles (flashProveDataAtSecondHash o) Z).d₀ (allZeroDigest, [])
    (fun c => length_par7O_le o recordGround (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay c)
    (parts_at o Z).hk (parts_at o Z).hE (parts_at o Z).wK (parts_at o Z).dK (parts_at o Z).wP
    (parts_at o Z).dP (parts_at o Z).hK40
    (plainSystemAt o Z (settingsOfRead pp) b sample prove) (backAt o Z (settingsOfRead pp))
    (phiAt o Z (settingsOfRead pp)) b (fun x => x.1.1) (fun x => x.1.2) (fun _ _ _ => rfl)
    (RAt o Z).compilerParameters.sMT (fun x => x.2) (sec_at o Z pp hr) (dec_at o Z pp hr)

/-- **THE NUMBER IN THE STATEMENT**: while the bounds on the committer's and the opener's queries
add up to at most 2^70, the probability is at most 2^-114. (Beyond: nothing.) -/
theorem bindsWith_atOlder_at_70 (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (b : (RAt o Z).LeafBody) (sample : RandomizedAlgorithm (CoinsAt o Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt o Z → List Token → List Token →
      RandomizedAlgorithm (theDescriptionO o).Form) :
    BindsWith (plainSystemAt o Z (settingsOfRead pp) b sample prove)
      (extractorAt o Z (settingsOfRead pp))
      fun t => if t ≤ 2 ^ 70 then (2 : ℝ≥0∞)⁻¹ ^ 114 else ⊤ :=
  (bindsWith_atOlder o Z pp hr b sample prove).mono fun t => by
    by_cases ht : t ≤ 2 ^ 70
    · rw [if_pos ht]
      exact epsBind_budget_at_70 t ht
    · rw [if_neg ht]
      exact le_top

/-- **NOBODY OPENS ONE COMMITMENT TO TWO DIFFERENT WEIGHTS, EACH AT COINS OF ITS OWN PICK**, but
with probability twice the named error. -/
theorem noTwoOpenings_atOlder (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (b : (RAt o Z).LeafBody) (sample : RandomizedAlgorithm (CoinsAt o Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt o Z → List Token → List Token →
      RandomizedAlgorithm (theDescriptionO o).Form) :
    NoTwoOpenings (plainSystemAt o Z (settingsOfRead pp) b sample prove)
      fun t => 2 * epsBind honestBudget t :=
  (bindsWith_atOlder o Z pp hr b sample prove).noTwoOpenings

/-! ## 6 It is not empty -/

/-- There are such coins, at every o and Z: any pads with tails, and salts of zeros. -/
theorem coinsAt_nonempty (Z : PublicFiles) : Nonempty (CoinsAt o Z) :=
  ⟨⟨(Classical.arbitrary _, fun _ => List.replicate (RAt o Z).compilerParameters.sMT false),
    fun _ _ => List.length_replicate⟩⟩

/-- There is a filling of the tree's spare leaves, at every o and Z: the empty list of bits. -/
theorem fillingAt_nonempty (Z : PublicFiles) : Nonempty (RAt o Z).LeafBody := ⟨([] : List Bool)⟩

/-- The written committer's count at o. -/
def countAt (Z : PublicFiles) : ℕ := 8 + (2 * 2 ^ (RAt o Z).queryLayout.depth + 2 * ((RAt o Z).queryLayout.K + 1)) + 1

/-- It is within the honest side's budget. -/
theorem countAt_le (Z : PublicFiles) : countAt o Z ≤ honestBudget :=
  LPFD.Full.countD (dataAtFiles (flashProveDataAtSecondHash o) Z).A (dataAtFiles (flashProveDataAtSecondHash o) Z).E
    (dataAtFiles (flashProveDataAtSecondHash o) Z).G (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP
    (dataAtFiles (flashProveDataAtSecondHash o) Z).runK (dataAtFiles (flashProveDataAtSecondHash o) Z).runP (dataAtFiles (flashProveDataAtSecondHash o) Z).dec
    (dataAtFiles (flashProveDataAtSecondHash o) Z).P (dataAtFiles (flashProveDataAtSecondHash o) Z).hStar (dataAtFiles (flashProveDataAtSecondHash o) Z).it
    (dataAtFiles (flashProveDataAtSecondHash o) Z).sR (dataAtFiles (flashProveDataAtSecondHash o) Z).hDK (dataAtFiles (flashProveDataAtSecondHash o) Z).hDP
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hK (dataAtFiles (flashProveDataAtSecondHash o) Z).N (dataAtFiles (flashProveDataAtSecondHash o) Z).d₀
    (allZeroDigest, []) (parts_at o Z).hK40

/- From here on Lean compares these by their names. -/
attribute [local irreducible] LayoutsByPublicReading.commitAtCoins countAt

theorem committerAt_count (Z : PublicFiles) (s : IntegerTransformer.Settings) (b : (RAt o Z).LeafBody)
    (w : ModelWeights s) (x : CoinsAt o Z) :
    (committerAt o Z s b w x).toRandomized.QueryBound (countAt o Z) :=
  commitAtCoins_within (TAt o Z) b
    (LPFD.Full.noCoinDBy (dataAtFiles (flashProveDataAtSecondHash o) Z).A (dataAtFiles (flashProveDataAtSecondHash o) Z).E
    (dataAtFiles (flashProveDataAtSecondHash o) Z).G
    (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP (dataAtFiles (flashProveDataAtSecondHash o) Z).runK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).runP (dataAtFiles (flashProveDataAtSecondHash o) Z).dec (dataAtFiles (flashProveDataAtSecondHash o) Z).P
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hStar (dataAtFiles (flashProveDataAtSecondHash o) Z).it (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL
    (asDescriptionFiles Z).lay (parAt o Z) (dataAtFiles (flashProveDataAtSecondHash o) Z).sR (dataAtFiles (flashProveDataAtSecondHash o) Z).hDK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hDP (dataAtFiles (flashProveDataAtSecondHash o) Z).hK (dataAtFiles (flashProveDataAtSecondHash o) Z).N
    (dataAtFiles (flashProveDataAtSecondHash o) Z).d₀ (allZeroDigest, []))
    8
    (LPFD.Full.readingDBy (dataAtFiles (flashProveDataAtSecondHash o) Z).A (dataAtFiles (flashProveDataAtSecondHash o) Z).E
    (dataAtFiles (flashProveDataAtSecondHash o) Z).G
    (dataAtFiles (flashProveDataAtSecondHash o) Z).DK (dataAtFiles (flashProveDataAtSecondHash o) Z).DP (dataAtFiles (flashProveDataAtSecondHash o) Z).runK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).runP (dataAtFiles (flashProveDataAtSecondHash o) Z).dec (dataAtFiles (flashProveDataAtSecondHash o) Z).P
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hStar (dataAtFiles (flashProveDataAtSecondHash o) Z).it (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL
    (asDescriptionFiles Z).lay (parAt o Z) (dataAtFiles (flashProveDataAtSecondHash o) Z).sR (dataAtFiles (flashProveDataAtSecondHash o) Z).hDK
    (dataAtFiles (flashProveDataAtSecondHash o) Z).hDP (dataAtFiles (flashProveDataAtSecondHash o) Z).hK (dataAtFiles (flashProveDataAtSecondHash o) Z).N
    (dataAtFiles (flashProveDataAtSecondHash o) Z).d₀ (allZeroDigest, []) 7
      fun c => length_par7O_le o recordGround (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay c)
    (backAt o Z s w) x.1.1 x.1.2 (countAt o Z) (by unfold countAt; rfl)

/-- **FROM A COMMITMENT AT ANY WEIGHTS AND ANY COINS, AND THE QUERIES OF THAT RUN, THE EXTRACTOR
GIVES THE WEIGHTS BACK**, but with probability the named error at that run's count. -/
theorem extracts_atOlder (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (b : (RAt o Z).LeafBody) (w : ModelWeights (settingsOfRead pp)) (x : CoinsAt o Z) :
    Prob (committerAt o Z (settingsOfRead pp) b w x).toRandomized.withQueryLog
        {c | extractorAt o Z (settingsOfRead pp) c.1 c.2 ≠ some w}
      ≤ epsBind honestBudget (countAt o Z) :=
  (bindsWith_atOlder o Z pp hr b (.done x) fun _ _ _ _ => .done
    ⟨[], ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty,
      ByteArray.empty⟩).atRandomness w x
    (countAt o Z) (committerAt_count o Z (settingsOfRead pp) b w x)

end FlashProve

#print axioms VerifiableInference.OnPublicFiles.commitAtCoins_within
#print axioms FlashProve.theLayAt_hl
#print axioms FlashProve.theLayAt_hd₁
#print axioms FlashProve.theLayAt_hd₂
#print axioms FlashProve.bindsWith_atOlder_at_70
#print axioms FlashProve.noTwoOpenings_atOlder
#print axioms FlashProve.coinsAt_nonempty
#print axioms FlashProve.fillingAt_nonempty
#print axioms FlashProve.countAt_le
#print axioms FlashProve.committerAt_count
#print axioms FlashProve.extracts_atOlder
#print axioms FlashProve.fit_theLayAt
#print axioms FlashProve.parts_at
#print axioms FlashProve.TAt_at
#print axioms FlashProve.TAt_fits
#print axioms FlashProve.TAt_reads
#print axioms FlashProve.extractor_atOlder
#print axioms FlashProve.sec_at
#print axioms FlashProve.back_at
#print axioms FlashProve.dec_at
#print axioms FlashProve.bindsWith_atOlder
