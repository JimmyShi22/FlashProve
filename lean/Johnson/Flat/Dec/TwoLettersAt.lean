-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/TwoLettersAt.lean: A TWIN, MADE BY PROGRAM, OF A FILE THAT IS NOT IN THIS LIBRARY, WITH THE ENTRY FILE's THREE LETTERS FREE: ds (its rounds' data), xs (its openings of stored
tables), dec (its decision), in that order behind runP.

Why. The library's frame lays the entry file's protocol as the written link at written rounds' data, written openings and THE DECISION OF
`verify-on-bytes` (`fun rr => decFullX (recX rr)` | `decSmallX`). A verifier whose entry file's decision is another text is then no
member of the frame, and neither the tie from what runs nor the conditional soundness theorem can speak of it.
How it was made. Every declared name of the original has a D behind it; `ds xs dec` stand behind `runP` in every list of letters;
`linkSibFull` | `linkSibSmall` became `linkFullD ds xs dec` | `linkSmallD ds xs dec`; `dsFull` | `dsSmall` became ds, `frD.xs` | `srD.xs`
xs. All else is the original's text, docstrings too: WHERE A DOCSTRING SAYS «written» OR NAMES A FILE IT SPEAKS OF THE TEXT OF WHICH
THIS IS A TWIN. 
Limits: those of the original's head (not in this library). Nothing on soundness is gained: in the
conditional theorem `entrySound` becomes a named hypothesis, in the place of the theorem on codes,
from which Johnson/Flat/TwoSizesAt.lean proves it for the written letters alone; and four tests on
the numbers of ds become premises, which the library proves of the written data.

-/
import Johnson.Flat.Dec.TwoSizesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

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

set_option quotPrecheck false in
/-- The interface of the typed oracles over the three files. -/
local notation "Cf" => typedOracleCarrier ((Ff).withProvers P) (List Bool) (Ff).annT (Ff).annL

/-- The letters that stand in the verifier's text. -/
structure VerifierSideOfFullD where
  depthReqT : ℕ
  hSeed : (seedBS recLg recS).b ≤ K + 1
  t : Tag
  cfg : List (Dig 256)
  shape : Bits
  pl0 : PlainPart (shapeOf (Cf) t) (annOf (Cf) t)
  pl1 : PlainPart (shapeOf (Cf) t) (annOf (Cf) t)
  num : ℕ → Plains ((Ff).withProvers P).onlineBatch.loc.shape → Bool
  r₀ : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 (K + 1) (Cf)) 256
  enc : KeyRoot 256 ((Ff).withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X

/-- The letters that the claim, the hypotheses and the bound name, and the verifier's text does
not. -/
structure NamedSideOfFullD where
  nextToken : A.Mat → List Token → Option Token
  ext : ZKCP.Extractor 256 A.Mat X Unit (ZKCP.Digest 256) (KeyRoot 256 ((Ff).withProvers P) ×
      OfflineLinkOnlineProof 256 ((Ff).withProvers P) (Ff).annT (Ff).annL)
  εId : ℕ → ℝ≥0∞
  x₀ : X
  εs : ℝ≥0∞
  hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs

variable {A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}

/-- **The letters at a verifier's side and a named side.** The honest side is filled with the
plainest terms that have the types: no state, a fixed key, proofs with no proof string, no coins.
d₀: the fixed key's digest. -/
def lettersAtFullD (V : VerifierSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (N : NamedSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt P) (d₀ : Dig 256) :
    InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P where
  depthReqT := V.depthReqT
  hSeed := V.hSeed
  εs := N.εs
  hε := N.hε
  t := V.t
  cfg := V.cfg
  shape := V.shape
  pl0 := V.pl0
  pl1 := V.pl1
  num := V.num
  r₀ := V.r₀
  p := V.p
  m := V.m
  enc := V.enc
  build := V.build
  nextToken := N.nextToken
  ISK := Unit
  commit := fun _ => .pure (⟨d₀, rK⟩, ())
  prove := fun _ b => .pure ⟨b.map fun _ => ⟨0, none, (d₀, rK, none), none⟩, List.length_map ..⟩
  bound := 0
  π₀ := (⟨d₀, rK⟩, ⟨0, none, (d₀, rK, none), none⟩)
  ext := N.ext
  εId := N.εId
  x₀ := N.x₀

/-- The verifier's side of any letters. -/
def InnerCompilerInputAndAnalysisFieldsAtFullSize.verifierSide
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    VerifierSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt K P :=
  ⟨T.depthReqT, T.hSeed, T.t, T.cfg, T.shape, T.pl0, T.pl1, T.num, T.r₀, T.p, T.m, T.enc, T.build⟩

/-- The named side of any letters. -/
def InnerCompilerInputAndAnalysisFieldsAtFullSize.namedSide
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    NamedSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt P :=
  ⟨T.nextToken, T.ext, T.εId, T.x₀, T.εs, T.hε⟩

/-- The two sides are read back. -/
theorem lettersAtFull_verifierSideD
    (V : VerifierSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (N : NamedSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt P) (d₀ : Dig 256) :
    (lettersAtFullD V N d₀).verifierSide = V := rfl

theorem lettersAtFull_namedSideD
    (V : VerifierSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (N : NamedSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt P) (d₀ : Dig 256) :
    (lettersAtFullD V N d₀).namedSide = N := rfl

/-- **The verifier is a function of the verifier's side alone**: at any letters T it is the verifier
at T's verifier's side, any named side and the filled honest side. -/
theorem verify_lettersAtFullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (N : NamedSideOfFullD A E DK DP runK runP ds xs dec rK rP depthReq early salt P) (d₀ : Dig 256) :
    (innerSystem (innerCompilerInputAtFullSize (lettersAtFullD T.verifierSide N d₀))).verify =
      (innerSystem (innerCompilerInputAtFullSize T)).verify := rfl

/-- **The hypotheses that are left are functions of the verifier's side and the named side alone**;
so are the bound, the extractor, the hypothesis on the meaning and the conclusion (below). -/
theorem left_lettersAtFullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256) :
    RemainingSoundnessConditionsAtFullSize (lettersAtFullD T.verifierSide T.namedSide d₀) ↔ RemainingSoundnessConditionsAtFullSize T :=
  ⟨fun h => ⟨h.keySound, h.entrySound, h.proofSound, h.commitment⟩,
    fun h => ⟨h.keySound, h.entrySound, h.proofSound, h.commitment⟩⟩

theorem error_lettersAtFullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256) :
    compiledSoundnessError (soundnessAnalysisDataAtFullSize (lettersAtFullD T.verifierSide T.namedSide d₀)) =
      compiledSoundnessError (soundnessAnalysisDataAtFullSize T) := rfl

theorem extractor_lettersAtFullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256) :
    compiledIndexExtractor (soundnessAnalysisDataAtFullSize (lettersAtFullD T.verifierSide T.namedSide d₀)) =
      compiledIndexExtractor (soundnessAnalysisDataAtFullSize T) := rfl

/-- The hypothesis on the meaning, at any claim and at "the output tokens are the model's". -/
theorem soundFor_lettersAtFullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256)
    (claim : A.Mat → List Token → List Token → Prop) :
    CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtFullSize (lettersAtFullD T.verifierSide T.namedSide d₀)) claim ↔
      CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtFullSize T) claim := Iff.rfl

theorem sound_lettersAtFullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256) :
    CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataAtFullSize (lettersAtFullD T.verifierSide T.namedSide d₀)) ↔
      CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataAtFullSize T) := Iff.rfl

/-- **The theorems' conclusion is the same statement**: soundness of the system at T, with T's
extractor, for a claim, at a bound, is soundness of the system at T's two sides with the honest side
filled. -/
theorem soundForWith_lettersAtFullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256)
    (claim : A.Mat → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞) :
    SoundForWith (innerSystem (innerCompilerInputAtFullSize (lettersAtFullD T.verifierSide T.namedSide d₀)))
        (compiledIndexExtractor (soundnessAnalysisDataAtFullSize (lettersAtFullD T.verifierSide T.namedSide d₀))) claim ε ↔
      SoundForWith (innerSystem (innerCompilerInputAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataAtFullSize T)) claim ε :=
  Iff.rfl

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

set_option quotPrecheck false in
/-- The interface of the typed oracles over the three files. -/
local notation "Cs" => typedOracleCarrier ((Fs).withProvers P) (List Bool) (Fs).annT (Fs).annL

/-- The letters that stand in the verifier's text. -/
structure VerifierSideOfSmallD where
  depthReqT : ℕ
  hSeed : (seedBS 19 1).b ≤ K + 1
  t : Tag
  cfg : List (Dig 256)
  shape : Bits
  pl0 : PlainPart (shapeOf (Cs) t) (annOf (Cs) t)
  pl1 : PlainPart (shapeOf (Cs) t) (annOf (Cs) t)
  num : ℕ → Plains ((Fs).withProvers P).onlineBatch.loc.shape → Bool
  r₀ : (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).Rec
  p : Params
  m : OracleCoding (typedOracleFamily 256 (K + 1) (Cs)) 256
  enc : KeyRoot 256 ((Fs).withProvers P) → Option ZKCP.Str
  build : List Token × List Token → List Token → Option X

/-- The letters that the claim, the hypotheses and the bound name, and the verifier's text does
not. -/
structure NamedSideOfSmallD where
  nextToken : A.Mat → List Token → Option Token
  ext : ZKCP.Extractor 256 A.Mat X Unit (ZKCP.Digest 256) (KeyRoot 256 ((Fs).withProvers P) ×
      OfflineLinkOnlineProof 256 ((Fs).withProvers P) (Fs).annT (Fs).annL)
  εId : ℕ → ℝ≥0∞
  x₀ : X
  εs : ℝ≥0∞
  hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs

variable {A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}

/-- **The letters at a verifier's side and a named side.** The honest side is filled with the
plainest terms that have the types: no state, a fixed key, proofs with no proof string, no coins.
d₀: the fixed key's digest. -/
def lettersAtSmallD (V : VerifierSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (N : NamedSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt P) (d₀ : Dig 256) :
    InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P where
  depthReqT := V.depthReqT
  hSeed := V.hSeed
  εs := N.εs
  hε := N.hε
  t := V.t
  cfg := V.cfg
  shape := V.shape
  pl0 := V.pl0
  pl1 := V.pl1
  num := V.num
  r₀ := V.r₀
  p := V.p
  m := V.m
  enc := V.enc
  build := V.build
  nextToken := N.nextToken
  ISK := Unit
  commit := fun _ => .pure (⟨d₀, rK⟩, ())
  prove := fun _ b => .pure ⟨b.map fun _ => ⟨0, none, (d₀, rK, none), none⟩, List.length_map ..⟩
  bound := 0
  π₀ := (⟨d₀, rK⟩, ⟨0, none, (d₀, rK, none), none⟩)
  ext := N.ext
  εId := N.εId
  x₀ := N.x₀

/-- The verifier's side of any letters. -/
def InnerCompilerInputAndAnalysisFieldsAtSmallSize.verifierSide
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    VerifierSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt K P :=
  ⟨T.depthReqT, T.hSeed, T.t, T.cfg, T.shape, T.pl0, T.pl1, T.num, T.r₀, T.p, T.m, T.enc, T.build⟩

/-- The named side of any letters. -/
def InnerCompilerInputAndAnalysisFieldsAtSmallSize.namedSide
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    NamedSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt P :=
  ⟨T.nextToken, T.ext, T.εId, T.x₀, T.εs, T.hε⟩

/-- The two sides are read back. -/
theorem lettersAtSmall_verifierSideD
    (V : VerifierSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (N : NamedSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt P) (d₀ : Dig 256) :
    (lettersAtSmallD V N d₀).verifierSide = V := rfl

theorem lettersAtSmall_namedSideD
    (V : VerifierSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (N : NamedSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt P) (d₀ : Dig 256) :
    (lettersAtSmallD V N d₀).namedSide = N := rfl

/-- **The verifier is a function of the verifier's side alone**: at any letters T it is the verifier
at T's verifier's side, any named side and the filled honest side. -/
theorem verify_lettersAtSmallD
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (N : NamedSideOfSmallD A E DK DP runK runP ds xs dec rK rP depthReq early salt P) (d₀ : Dig 256) :
    (innerSystem (innerCompilerInputAtSmallSize (lettersAtSmallD T.verifierSide N d₀))).verify =
      (innerSystem (innerCompilerInputAtSmallSize T)).verify := rfl

/-- **The hypotheses that are left are functions of the verifier's side and the named side alone**;
so are the bound, the extractor, the hypothesis on the meaning and the conclusion (below). -/
theorem left_lettersAtSmallD
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256) :
    RemainingSoundnessConditionsAtSmallSize (lettersAtSmallD T.verifierSide T.namedSide d₀) ↔ RemainingSoundnessConditionsAtSmallSize T :=
  ⟨fun h => ⟨h.keySound, h.entrySound, h.proofSound, h.commitment⟩,
    fun h => ⟨h.keySound, h.entrySound, h.proofSound, h.commitment⟩⟩

theorem error_lettersAtSmallD
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256) :
    compiledSoundnessError (soundnessAnalysisDataAtSmallSize (lettersAtSmallD T.verifierSide T.namedSide d₀)) =
      compiledSoundnessError (soundnessAnalysisDataAtSmallSize T) := rfl

theorem extractor_lettersAtSmallD
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256) :
    compiledIndexExtractor (soundnessAnalysisDataAtSmallSize (lettersAtSmallD T.verifierSide T.namedSide d₀)) =
      compiledIndexExtractor (soundnessAnalysisDataAtSmallSize T) := rfl

/-- The hypothesis on the meaning, at any claim and at "the output tokens are the model's". -/
theorem soundFor_lettersAtSmallD
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256)
    (claim : A.Mat → List Token → List Token → Prop) :
    CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtSmallSize (lettersAtSmallD T.verifierSide T.namedSide d₀)) claim ↔
      CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataAtSmallSize T) claim := Iff.rfl

theorem sound_lettersAtSmallD
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256) :
    CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataAtSmallSize (lettersAtSmallD T.verifierSide T.namedSide d₀)) ↔
      CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataAtSmallSize T) := Iff.rfl

/-- **The theorems' conclusion is the same statement**: soundness of the system at T, with T's
extractor, for a claim, at a bound, is soundness of the system at T's two sides with the honest side
filled. -/
theorem soundForWith_lettersAtSmallD
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) (d₀ : Dig 256)
    (claim : A.Mat → List Token → List Token → Prop) (ε : ℕ → ℝ≥0∞) :
    SoundForWith (innerSystem (innerCompilerInputAtSmallSize (lettersAtSmallD T.verifierSide T.namedSide d₀)))
        (compiledIndexExtractor (soundnessAnalysisDataAtSmallSize (lettersAtSmallD T.verifierSide T.namedSide d₀))) claim ε ↔
      SoundForWith (innerSystem (innerCompilerInputAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataAtSmallSize T)) claim ε :=
  Iff.rfl

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.verify_lettersAtFullD
#print axioms VerifiableInference.OnPublicFiles.left_lettersAtFullD
#print axioms VerifiableInference.OnPublicFiles.verify_lettersAtSmallD
#print axioms VerifiableInference.OnPublicFiles.left_lettersAtSmallD
#print axioms VerifiableInference.OnPublicFiles.soundForWith_lettersAtFullD
#print axioms VerifiableInference.OnPublicFiles.soundForWith_lettersAtSmallD
