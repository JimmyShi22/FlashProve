-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/DescribeT.lean: a description whose letters T are a function of the two public
readings.
`DescriptionFields`: the letters at one set of public files, over the frame of Johnson/Flat/Dec/ (the entry
file's rounds, places and decision are letters). `CommitterProverFormAndParser`: the honest side, the form and the parser.
`descriptionOfFieldsWithReading`: the value, at a further public reading that is a letter; `descriptionOfFields`: at
`VerifierAndGoals.readMoreAt`. `input_descriptionOfFields`: its input is the frame's input at the family's member, by
`rfl`. `verify_descriptionOfFields`: the goals' verify at it, at a hash function. `cAt_hashOf`,
`sevenAt_hashOf`, `verify_descriptionOfFields_thru`: at the hash function made of a function O on byte strings
the two readings are `PV.Head.cThru` and `PV.Head.sevenThru` through O.

-/
import Johnson.Goal.Tie.VerifyEval
import Johnson.Goal.Tie.ReadThruHead
import Johnson.Flat.Dec.TwoSizesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open PV.Head (cThru sevenThru)

/-- The letters at one Z; the T a function of the two public readings. -/
structure DescriptionFields where
  X : Type
  A : (frS.toDecR frZ 402653181).Claims X
  E : Coding A
  DK : WholeD
  DP : WholeD
  runK : RecFull → PQ.View → PQ.View → PQ.View → Bool
  runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool
  /-- the entry file's written rounds, its openings' places, ITS DECISION: three letters of the
    frame (Johnson/Flat/Dec/) -/
  ds : List TypedOracleCompiler.Run.PQ.RD
  xs : List _root_.Run.PQ.XO
  dec : RecFull × RecFull → PQ.View → Bool
  rK : RecFull
  rP : RecFull
  depthReq : ℕ
  early : X → X
  salt : ℕ
  K : ℕ
  P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers
  inputFieldsAtReadings : Digest → List (Dig 256) →
    InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P
  ext : (s : IntegerTransformer.Settings) → Commitment → QueryLog → Option (ModelWeights s)

/-- The honest side, the form and the parser, over a family of frames. -/
structure CommitterProverFormAndParser (fr : PublicFiles → DescriptionFields) where
  Shown : Type
  shown : (s : IntegerTransformer.Settings) → ModelWeights s → Shown
  Rand : Type
  sample : RandomizedAlgorithm Rand
  commit : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand →
    DeterministicAlgorithm Commitment
  Form : Type
  parse : (Z : PublicFiles) → List Token → List Token → Form → DeterministicAlgorithm
    (TypedProof (threeProtocolsAtFullSize (fr Z).A (relationsAndEncodingOfClaims (fr Z).A (fr Z).E) (fr Z).DK (fr Z).DP (fr Z).runK
      (fr Z).runP (fr Z).ds (fr Z).xs (fr Z).dec (fr Z).rK (fr Z).rP (fr Z).depthReq (fr Z).early
          (fr Z).salt) (fr Z).P)
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm Form

variable (fr : PublicFiles → DescriptionFields) (H : CommitterProverFormAndParser fr)

/-- **THE VALUE, at a further public reading `more`.** -/
def descriptionOfFieldsWithReading (more : PublicFiles → Digest → DeterministicAlgorithm (List (Dig 256))) : Description where
  C := fun Z => DecR.configurationOfStoredTable (fr Z).A (relationsAndEncodingOfClaims (fr Z).A (fr Z).E)
  F := fun Z => threeProtocolsAtFullSize (fr Z).A (relationsAndEncodingOfClaims (fr Z).A (fr Z).E) (fr Z).DK (fr Z).DP (fr Z).runK
    (fr Z).runP (fr Z).ds (fr Z).xs (fr Z).dec (fr Z).rK (fr Z).rP (fr Z).depthReq (fr Z).early (fr
        Z).salt
  P := fun Z => (fr Z).P
  More := List (Dig 256)
  readMore := more
  T := fun Z c m => ((fr Z).inputFieldsAtReadings c m).letters
  extractor := fun Z s => (fr Z).ext s
  Shown := H.Shown
  shown := H.shown
  Rand := H.Rand
  sample := H.sample
  commit := H.commit
  Form := H.Form
  parse := H.parse
  prove := H.prove

/-- **THE VALUE**: at the further reading `readMoreAt`. -/
def descriptionOfFields : Description := descriptionOfFieldsWithReading fr H fun Z c => readMoreAt recordGround Z c

/-- **Its input is the frame's input at the family's member.** -/
theorem input_descriptionOfFields (Z : PublicFiles) (c : Digest) (m : List (Dig 256)) :
    (descriptionOfFields fr H).input Z c m = innerCompilerInputAtFullSize ((fr Z).inputFieldsAtReadings c m) := rfl

/-- What the further reading returns at a hash function: its values at the seven strings. -/
def sevenAt (Z : PublicFiles) (hash : VerifiableInference.Hash) : List (Dig 256) :=
  (readMoreAt recordGround Z (cAt Z hash)).evaluate hash

theorem mAt_descriptionOfFields (Z : PublicFiles) (hash : VerifiableInference.Hash) :
    mAt (descriptionOfFields fr H) Z hash = sevenAt Z hash := rfl

/-- **THE GOALS' verify AT descriptionOfFields, AT A HASH FUNCTION.** -/
theorem verify_descriptionOfFields (Z : PublicFiles) {Form : Type} (parse : Parser (descriptionOfFields fr H) Z Form)
    (scope : VerifierAndGoals.InScope Z = true) (hash : VerifiableInference.Hash) (commitment : Commitment)
    (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (descriptionOfFields fr H) Z parse commitment prompt output form).evaluate hash =
      (innerCompiledVerifier (innerCompilerInputAtFullSize ((fr Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))) commitment prompt
          output
        (proofAt parse prompt output form hash)).evaluate hash := by
  rw [verify_evaluate (descriptionOfFields fr H) Z parse scope hash commitment prompt output form,
    mAt_descriptionOfFields]
  rfl

/-- At the hash function made of O the first reading is `cThru` O Z, as a digest. -/
theorem cAt_hashOf (O : ByteArray → ByteArray) (Z : PublicFiles) :
    cAt Z (hashOf O) = bytesToDig (cThru O (asDescriptionFiles Z)) := readConfig_thru O Z

/-- And the further reading `sevenThru`, at the bytes of that digest. -/
theorem sevenAt_hashOf (O : ByteArray → ByteArray) (Z : PublicFiles) :
    sevenAt Z (hashOf O) =
      (sevenThru O recordGround (asDescriptionFiles Z) (digToBytes (bytesToDig (cThru O (asDescriptionFiles Z))))).map
        bytesToDig := by
  unfold sevenAt
  rw [cAt_hashOf]
  exact readMoreAt_thru O recordGround Z _

/-- **THE SAME AT hashOf O, THE READINGS SPELT THROUGH O.** hO: O answers the first public string
  with 32 bytes. -/
theorem verify_descriptionOfFields_thru (Z : PublicFiles) {Form : Type} (parse : Parser (descriptionOfFields fr H) Z Form)
    (scope : VerifierAndGoals.InScope Z = true) (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size
        = 32)
    (commitment : Commitment) (prompt output : List Token) (form : Form) :
    (VerifierAndGoals.verify (descriptionOfFields fr H) Z parse commitment prompt output form).evaluate (hashOf O) =
      (innerCompiledVerifier (innerCompilerInputAtFullSize ((fr Z).inputFieldsAtReadings (bytesToDig (cThru O (asDescriptionFiles Z)))
                                   ((sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))).map bytesToDig))) commitment
        prompt output
        (proofAt parse prompt output form (hashOf O))).evaluate (hashOf O) := by
  rw [verify_descriptionOfFields fr H Z parse scope (hashOf O) commitment prompt output form, sevenAt_hashOf,
    cAt_hashOf, digToBytes_bytesToDig _ hO]

end FlashProve
