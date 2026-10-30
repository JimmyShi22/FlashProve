-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/TwoSizesAt.lean: A TWIN OF Johnson/Flat/TwoSizesAt.lean, WITH THE ENTRY FILE's THREE LETTERS FREE: ds (its rounds' data), xs (its openings of stored
tables), dec (its decision), in that order behind runP.

Why. The original's frame lays the entry file's protocol as the written link at written rounds' data, written openings and `verify-on-bytes`'s
DECISION (`fun rr => decFullX (recX rr)` | `decSmallX`). A verifier whose entry file's decision is another text is then no
member of the frame, and neither the tie from what runs nor the conditional soundness theorem can speak of it.
How it was made. Declared names of the original lose «WithFixedLink»; `ds xs dec` stand behind `runP` in every list of letters;
`linkSibFull` | `linkSibSmall` became `linkFullD ds xs dec` | `linkSmallD ds xs dec`; `dsFull` | `dsSmall` became ds, `frD.xs` | `srD.xs`
xs. All else is the original's text, docstrings too: WHERE A DOCSTRING SAYS «written» OR NAMES A FILE IT SPEAKS OF THE TEXT OF WHICH
THIS IS A TWIN. OTHER THAN THE ORIGINAL: `entrySoundWithFixedLinkAtFullSize` | `entrySoundWithFixedLinkAtSmallSize` (proved for the written letters alone, under the theorem on codes) are left out; `entrySound` IS A FOURTH FIELD OF `RemainingSoundnessConditionsAtFullSize` | `RemainingSoundnessConditionsAtSmallSize`: A NAMED HYPOTHESIS; so the theorem on codes (hA) is no premise of `compilerSoundnessConditionsAtFullSize` | `compilerSoundnessConditionsAtSmallSize`, `innerCompiledVerifierSoundAtFullSize` | `innerCompiledVerifierSoundAtSmallSize`, `innerCompiledVerifierSoundAtFullSize_for` | `innerCompiledVerifierSoundAtSmallSize_for`: it falls to whoever proves `entrySound`; the four tests on ds's numbers ride as premises.
Limits: those of the original's head. Nothing on soundness is gained: in the conditional theorem
`entrySound` becomes a named hypothesis, in the place of the theorem on codes, from which the
original (Johnson/Flat/TwoSizesAt.lean) proves it for the written letters alone; and four tests on
the numbers of ds become premises, which the original proves of the written data.

-/
import Johnson.Flat.Dec.WiresAtSizes
import Johnson.Flat.TwoSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## The full-size files -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt K : ℕ)
  (P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- The three files. -/
local notation "Ff" => threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt

/-- The fields of an input, and of what the hypotheses name beside it, that are letters at
this size. -/
structure InnerCompilerInputAndAnalysisFieldsAtFullSize where
  /-- the depth of a request tree of the key file's test -/
  depthReqT : ℕ
  /-- the wiring has blocks enough for the record's seed -/
  hSeed : (seedBS recLg recS).b ≤ K + 1
  /-- the stated bound on a round's error: at least 2^-128, at which the entry file's rounds and the
  record's seed are proved -/
  εs : ℝ≥0∞
  hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs
  t : Tag
  cfg : List (Dig 256)
  shape : Bits
  pl0 : PlainPart (shapeOf (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) t)
    (annOf (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) t)
  pl1 : PlainPart (shapeOf (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) t)
    (annOf (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) t)
  num : ℕ → Plains ((Ff).withProvers P).onlineBatch.loc.shape → Bool
  r₀ : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL)) 256
  enc : KeyRoot 256 ((Ff).withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X
  nextToken : A.Mat → List Token → Option Token
  ISK : Type
  commit : A.Mat → Rom.OComp (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((Ff).withProvers P) (List Bool)
                 (Ff).annT (Ff).annL))
    (KeyRoot 256 ((Ff).withProvers P) × ISK)
  prove : ISK → (b : List (X × Unit)) → Rom.OComp (typedOracleFamily 256 (K + 1)
      (typedOracleCarrier ((Ff).withProvers P) (List Bool)
      (Ff).annT (Ff).annL))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((Ff).withProvers P) (Ff).annT (Ff).annL) b)
  bound : ℕ
  π₀ : KeyRoot 256 ((Ff).withProvers P) × OfflineLinkOnlineProof 256 ((Ff).withProvers P) (Ff).annT (Ff).annL
  ext : ZKCP.Extractor 256 A.Mat X Unit (ZKCP.Digest 256) (KeyRoot 256 ((Ff).withProvers P) ×
      OfflineLinkOnlineProof 256 ((Ff).withProvers P) (Ff).annT (Ff).annL)
  εId : ℕ → ℝ≥0∞
  x₀ : X

variable {A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}

/-- The letters' type. It holds K, salt and P beside the files' letters. -/
local notation "Lf" => InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P

/-- The body of a leaf is a string of bits. -/
abbrev InnerCompilerInputAndAnalysisFieldsAtFullSize.Bd (_ : Lf) : Type := List Bool

/-- The wiring is `wireOfFullD` (Johnson/Flat/WiresAtSizes.lean). -/
abbrev InnerCompilerInputAndAnalysisFieldsAtFullSize.W (T : Lf) :
    QueryLayout 256 (typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL) :=
  wireOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K T.depthReqT

/-- The wiring has blocks enough for the record's seed. -/
theorem InnerCompilerInputAndAnalysisFieldsAtFullSize.hK (T : Lf) : (seedBS recLg recS).b ≤ T.W.K :=
  T.hSeed

/-- With the record's code and seed written. -/
def InnerCompilerInputAndAnalysisFieldsAtFullSize.letters (T : Lf) :
    InnerCompilerInputFieldsOverThreeProtocols (Ff) P where
  Bd := T.Bd
  W := T.W
  Sd := outOfDomainSampleQueryLayoutOfCode ((Ff).withProvers P) T.Bd _ _ (v := frS.P.v) (lg := 29) (s := 1)
    T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS T.W.K T.hK) id
    seedEqFull
  cA := codeA (v := frS.P.v) (s := 1)
  r₀ := T.r₀
  p := T.p
  m := T.m
  enc := T.enc
  build := T.build
  nextToken := T.nextToken
  ISK := T.ISK
  commit := T.commit
  prove := T.prove
  bound := T.bound
  π₀ := T.π₀

/-- Every round's error is stated at εs, counted with the round's proof of work: stated, not proved,
of the key file's and the proof file's rounds. -/
def InnerCompilerInputAndAnalysisFieldsAtFullSize.names (T : Lf) :
    SoundnessAnalysisFieldsOverThreeProtocols (Ff) P :=
  ⟨T.ext, T.εId, T.x₀, T.εs⟩

/-- The input at this size. -/
def innerCompilerInputAtFullSize (T : Lf) : InnerCompilerInput :=
  innerInputOfThreeProtocols (Ff) P T.letters

/-- What the hypotheses name beside it. -/
def soundnessAnalysisDataAtFullSize (T : Lf) : SoundnessAnalysisData (innerCompilerInputAtFullSize T) :=
  soundnessAnalysisDataOfThreeProtocols (Ff) P T.letters T.names

/-- The named hypotheses that are left at this size, beside the meaning and the theorem on codes. -/
structure RemainingSoundnessConditionsAtFullSize (T : Lf) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T)
  entrySound : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T)
  commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataAtFullSize T)

set_option maxRecDepth 20000 in
/-- **Eleven of the fifteen named hypotheses of `CompilerSoundnessConditions` hold at this make**, under the premises on
numbers: the fifteen, from these and the four of `RemainingSoundnessConditionsAtFullSize`. Two
premises more ride inside T: hSeed and hε. -/
theorem compilerSoundnessConditionsAtFullSize (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Lf}
    (h : RemainingSoundnessConditionsAtFullSize T) : CompilerSoundnessConditions (soundnessAnalysisDataAtFullSize T) where
  noneColl := (Ff).obj_noneColl P
  keySound := h.keySound
  entrySound := h.entrySound
  proofSound := h.proofSound
  keyLocal := (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).1
  entryLocal := (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).2.1
  proofLocal := (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).2.2
  keyCoherent := (threeProtocolsAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).1
  entryCoherent := threeProtocolsAtFullSize_entryCoherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt
  proofCoherent := (threeProtocolsAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).2
  seedLaw := outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y =>
    le_trans (entryFull_seedLawK A (relationsAndEncodingOfClaims A E) T.W.K T.hK y) T.hε
  wires := wiresOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K T.depthReqT hk
    bL wLk own dL wK dK wP dP
  answersCode := codeA_inj
  answersLength := codeA_one
  commitment := h.commitment

/-- **The compiler's theorem at this make, for any claim on the index**: `innerCompiledVerifier_soundFor`
(Johnson/Top/InnerCompiledVerifier.lean). Under: nine tests on numbers (hk, bL, wLk, own, dL, wK, dK,
wP, dP); keySound, entrySound, proofSound and commitment (h); that the relaxed relation gives the claim (hs);
and, inside T, hSeed and hε. All are hypotheses of the theorem: Lean's list of axioms does not show
them. -/
theorem innerCompiledVerifierSoundAtFullSize_for (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Lf}
    (h : RemainingSoundnessConditionsAtFullSize T) (claim : A.Mat → List Token → List Token → Prop)
    (hs : CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtFullSize T) claim) :
    SoundForWith (innerSystem (innerCompilerInputAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataAtFullSize T)) claim
      (compiledSoundnessError (soundnessAnalysisDataAtFullSize T)) :=
  innerCompiledVerifier_soundFor _ claim (compilerSoundnessConditionsAtFullSize hk bL wLk own dL wK dK wP dP h) hs

/-- **The same at the claim "the output tokens are the model's"** (the model is the letter
T.nextToken): `innerCompiledVerifier_sound`. Under the same hypotheses: hk, bL, wLk, own, dL, wK, dK, wP, dP; the four of h;
hSeed and hε inside T; with the meaning (hs : `CompilerSoundnessConditionStatements.sound`) in `soundFor`'s place. -/
theorem innerCompiledVerifierSoundAtFullSize (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Lf}
    (h : RemainingSoundnessConditionsAtFullSize T) (hs : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataAtFullSize T)) :
    SoundForWith (innerSystem (innerCompilerInputAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataAtFullSize T))
      (innerSystem (innerCompilerInputAtFullSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataAtFullSize T)) :=
  innerCompiledVerifier_sound _ ⟨compilerSoundnessConditionsAtFullSize hk bL wLk own dL wK dK wP dP h, hs⟩

end

/-! ## The small files -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (DK DP : WholeD)
  (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecSmall × RecSmall → PQ.View → Bool) (rK rP : RecSmall) (depthReq : ℕ)
  (early : X → X) (salt K : ℕ)
  (P : (threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- The three files. -/
local notation "Fs" => threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt

/-- The fields of an input, and of what the hypotheses name beside it, that are letters at
this size. -/
structure InnerCompilerInputAndAnalysisFieldsAtSmallSize where
  /-- the depth of a request tree of the key file's test -/
  depthReqT : ℕ
  /-- the wiring has blocks enough for the record's seed -/
  hSeed : (seedBS 19 1).b ≤ K + 1
  /-- the stated bound on a round's error: at least 2^-128, at which the entry file's rounds and the
  record's seed are proved -/
  εs : ℝ≥0∞
  hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs
  t : Tag
  cfg : List (Dig 256)
  shape : Bits
  pl0 : PlainPart (shapeOf (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) t)
    (annOf (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) t)
  pl1 : PlainPart (shapeOf (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) t)
    (annOf (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) t)
  num : ℕ → Plains ((Fs).withProvers P).onlineBatch.loc.shape → Bool
  r₀ : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL)) 256
  enc : KeyRoot 256 ((Fs).withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X
  nextToken : A.Mat → List Token → Option Token
  ISK : Type
  commit : A.Mat → Rom.OComp (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((Fs).withProvers P) (List Bool)
                 (Fs).annT (Fs).annL))
    (KeyRoot 256 ((Fs).withProvers P) × ISK)
  prove : ISK → (b : List (X × Unit)) → Rom.OComp (typedOracleFamily 256 (K + 1)
      (typedOracleCarrier ((Fs).withProvers P) (List Bool)
      (Fs).annT (Fs).annL))
      (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((Fs).withProvers P) (Fs).annT (Fs).annL) b)
  bound : ℕ
  π₀ : KeyRoot 256 ((Fs).withProvers P) × OfflineLinkOnlineProof 256 ((Fs).withProvers P) (Fs).annT (Fs).annL
  ext : ZKCP.Extractor 256 A.Mat X Unit (ZKCP.Digest 256) (KeyRoot 256 ((Fs).withProvers P) ×
      OfflineLinkOnlineProof 256 ((Fs).withProvers P) (Fs).annT (Fs).annL)
  εId : ℕ → ℝ≥0∞
  x₀ : X

variable {A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}

/-- The letters' type. It holds K, salt and P beside the files' letters. -/
local notation "Ls" => InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P

/-- The body of a leaf is a string of bits. -/
abbrev InnerCompilerInputAndAnalysisFieldsAtSmallSize.Bd (_ : Ls) : Type := List Bool

/-- The wiring is `wireOfSmallD` (Johnson/Flat/WiresAtSizes.lean). -/
abbrev InnerCompilerInputAndAnalysisFieldsAtSmallSize.W (T : Ls) :
    QueryLayout 256 (typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL) :=
  wireOfSmallD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K T.depthReqT

/-- The wiring has blocks enough for the record's seed. -/
theorem InnerCompilerInputAndAnalysisFieldsAtSmallSize.hK (T : Ls) : (seedBS 19 1).b ≤ T.W.K :=
  T.hSeed

/-- With the record's code and seed written. -/
def InnerCompilerInputAndAnalysisFieldsAtSmallSize.letters (T : Ls) :
    InnerCompilerInputFieldsOverThreeProtocols (Fs) P where
  Bd := T.Bd
  W := T.W
  Sd := outOfDomainSampleQueryLayoutOfCode ((Fs).withProvers P) T.Bd _ _ (v := srS.P.v) (lg := 19) (s := 1)
    T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK srT 19 1 T.W.K T.hK) id seedEqSmall
  cA := codeA (v := srS.P.v) (s := 1)
  r₀ := T.r₀
  p := T.p
  m := T.m
  enc := T.enc
  build := T.build
  nextToken := T.nextToken
  ISK := T.ISK
  commit := T.commit
  prove := T.prove
  bound := T.bound
  π₀ := T.π₀

/-- Every round's error is stated at εs, counted with the round's proof of work: stated, not proved,
of the key file's and the proof file's rounds. -/
def InnerCompilerInputAndAnalysisFieldsAtSmallSize.names (T : Ls) :
    SoundnessAnalysisFieldsOverThreeProtocols (Fs) P :=
  ⟨T.ext, T.εId, T.x₀, T.εs⟩

/-- The input at this size. -/
def innerCompilerInputAtSmallSize (T : Ls) : InnerCompilerInput :=
  innerInputOfThreeProtocols (Fs) P T.letters

/-- What the hypotheses name beside it. -/
def soundnessAnalysisDataAtSmallSize (T : Ls) : SoundnessAnalysisData (innerCompilerInputAtSmallSize T) :=
  soundnessAnalysisDataOfThreeProtocols (Fs) P T.letters T.names

/-- The named hypotheses that are left at this size, beside the meaning and the theorem on codes. -/
structure RemainingSoundnessConditionsAtSmallSize (T : Ls) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtSmallSize T)
  entrySound : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtSmallSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtSmallSize T)
  commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataAtSmallSize T)

set_option maxRecDepth 20000 in
/-- **Eleven of the fifteen named hypotheses of `CompilerSoundnessConditions` hold at this make**, under the premises on
numbers: the fifteen, from these and the four of `RemainingSoundnessConditionsAtSmallSize`. Two
premises more ride inside T: hSeed and hε. -/
theorem compilerSoundnessConditionsAtSmallSize (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Ls}
    (h : RemainingSoundnessConditionsAtSmallSize T) : CompilerSoundnessConditions (soundnessAnalysisDataAtSmallSize T) where
  noneColl := (Fs).obj_noneColl P
  keySound := h.keySound
  entrySound := h.entrySound
  proofSound := h.proofSound
  keyLocal := (threeProtocolsAtSmallSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).1
  entryLocal := (threeProtocolsAtSmallSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).2.1
  proofLocal := (threeProtocolsAtSmallSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).2.2
  keyCoherent := (threeProtocolsAtSmallSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).1
  entryCoherent := threeProtocolsAtSmallSize_entryCoherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt
  proofCoherent := (threeProtocolsAtSmallSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt).2
  seedLaw := outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y =>
    le_trans (entrySmall_seedLawK A (relationsAndEncodingOfClaims A E) T.W.K T.hK y) T.hε
  wires := wiresOfSmallD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K T.depthReqT hk
    bL wLk own dL wK dK wP dP
  answersCode := codeA_inj
  answersLength := codeA_one
  commitment := h.commitment

/-- **The compiler's theorem at this make, for any claim on the index**: `innerCompiledVerifier_soundFor`
(Johnson/Top/InnerCompiledVerifier.lean). Under: nine tests on numbers (hk, bL, wLk, own, dL, wK, dK,
wP, dP); keySound, entrySound, proofSound and commitment (h); that the relaxed relation gives the claim (hs);
and, inside T, hSeed and hε. All are hypotheses of the theorem: Lean's list of axioms does not show
them. -/
theorem innerCompiledVerifierSoundAtSmallSize_for (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Ls}
    (h : RemainingSoundnessConditionsAtSmallSize T) (claim : A.Mat → List Token → List Token → Prop)
    (hs : CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtSmallSize T) claim) :
    SoundForWith (innerSystem (innerCompilerInputAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataAtSmallSize T)) claim
      (compiledSoundnessError (soundnessAnalysisDataAtSmallSize T)) :=
  innerCompiledVerifier_soundFor _ claim (compilerSoundnessConditionsAtSmallSize hk bL wLk own dL wK dK wP dP h) hs

/-- **The same at the claim "the output tokens are the model's"** (the model is the letter
T.nextToken): `innerCompiledVerifier_sound`. Under the same hypotheses: hk, bL, wLk, own, dL, wK, dK, wP, dP; the four of h;
hSeed and hε inside T; with the meaning (hs : `CompilerSoundnessConditionStatements.sound`) in `soundFor`'s place. -/
theorem innerCompiledVerifierSoundAtSmallSize (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    {T : Ls}
    (h : RemainingSoundnessConditionsAtSmallSize T) (hs : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataAtSmallSize T)) :
    SoundForWith (innerSystem (innerCompilerInputAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataAtSmallSize T))
      (innerSystem (innerCompilerInputAtSmallSize T)).IsModelOutput (compiledSoundnessError (soundnessAnalysisDataAtSmallSize T)) :=
  innerCompiledVerifier_sound _ ⟨compilerSoundnessConditionsAtSmallSize hk bL wLk own dL wK dK wP dP h, hs⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.compilerSoundnessConditionsAtFullSize
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundAtFullSize_for
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundAtFullSize
#print axioms VerifiableInference.OnPublicFiles.compilerSoundnessConditionsAtSmallSize
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundAtSmallSize_for
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundAtSmallSize
