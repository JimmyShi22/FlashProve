-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/DescriptionOnDecodedProof.lean: the description D*: `descriptionOfFields` at the letters `tAt`
(Johnson/Top/Fire/Code/TieAtValues.lean), with a parser of its own.
`DescriptionDataAtFiles`: the letters at one set of public files: the plan's values G, the claims, the coding, both
files' data and decisions, the entry's decision, the provers, the named side, the extractor, and
three tests on the data. `DescriptionDataAtFiles.inputFieldsAtReadings`: T as a function of the two readings; `tOf_at`: at digests of
bytes it is `tAt` at these bytes. `DecodedProof`: what a run hands the fast form. `DescriptionDataAtFiles.proofOf`,
`typedOf`, `typedOf_back`: the typed proof that is laid of a form. `parserOfDecodedProof`: the parser: one
query, for the configuration's digest c; `parserOfDecodedProof_within`: it asks once. `descriptionOnDecodedProof`: the value.
`verify_descriptionOnDecodedProof`: the goals' verify at it, with its own parser, at `hashOf O`, is `innerCompiledVerifier` at the
input of `tAt`.
`auxNo`: one number that is no token of the vocabulary.
Limits. T reaches the format's hashes by name. The commitment, the prompt and the output are
verify's own arguments; the parser reads none of them.

-/
import Johnson.Goal.Tie.DescribeT
import Johnson.Top.Fire.Code.TieAtValues
import Johnson.PV.RunArgsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open PV.Head (cThru sevenThru)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR tAt)
open PV.EntryFive (dsF xsF)

/-- The letters at one set of public files. -/
structure DescriptionDataAtFiles (Zk : OnBytes.K.Pub) where
  /-- the plan's values: a field, so that a family can take `LPFD.Full.GF Zk` where its test says
    yes
    and values with both depths 0 where it does not -/
  G : FilesParameters XF RecFull
  A : (frS.toDecR frZ 402653181).Claims XF
  E : Coding A
  DK : WholeD
  DP : WholeD
  runK : RecFull → PQ.View → PQ.View → PQ.View → Bool
  runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool
  /-- THE ENTRY FILE's DECISION: the third letter -/
  dec : RecFull × RecFull → PQ.View → Bool
  P : (FsAtR A E G DK DP runK runP dec).Provers
  hStar : HId
  /-- the statement's item "request" at an instance: a letter, so that no hash function is named
    here -/
  it : XF → ByteArray
  sR : ℕ
  hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true
  hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true
  hK : KF DK DP + 1 + 1 < 2 ^ 49
  N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
    (saltG G) P
  d₀ : Dig 256
  ext : (s : IntegerTransformer.Settings) → Commitment → QueryLog → Option (ModelWeights s)

variable {Zk : OnBytes.K.Pub}

/-- `T` at bytes c and seven strings. -/
def DescriptionDataAtFiles.inputFieldsAtReadingsAsBytes (S : DescriptionDataAtFiles Zk) (c : ByteArray) (hc : c.size = 32) (seven : List ByteArray) :
    InnerCompilerInputAndAnalysisFieldsAtFullSize S.A S.E S.DK S.DP S.runK S.runP dsF xsF S.dec S.G.rec₀ S.G.z₀.2 (sBG
                                    S.G).logLeaves S.G.early
      (saltG S.G) (KF S.DK S.DP) S.P :=
  tAt S.A S.E S.G c hc S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it S.sR
      (PV.RunArgsF.pdLOf seven)
    (PV.RunArgsF.pd3At seven 4) (PV.RunArgsF.pd3At seven 1) S.hDK S.hDP S.hK S.N S.d₀

/-- It is `tAt` at these letters: by unfolding. -/
theorem DescriptionDataAtFiles.tBytes_eq (S : DescriptionDataAtFiles Zk) (c : ByteArray) (hc : c.size = 32) (seven : List
                                    ByteArray) :
    S.inputFieldsAtReadingsAsBytes c hc seven =
      tAt S.A S.E S.G c hc S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it S.sR
          (PV.RunArgsF.pdLOf seven)
        (PV.RunArgsF.pd3At seven 4) (PV.RunArgsF.pd3At seven 1) S.hDK S.hDP S.hK S.N S.d₀ := rfl

/-- **The T as a function of the two public readings.** -/
def DescriptionDataAtFiles.inputFieldsAtReadings (S : DescriptionDataAtFiles Zk) (c : Digest) (m : List (Dig 256)) :
    InnerCompilerInputAndAnalysisFieldsAtFullSize S.A S.E S.DK S.DP S.runK S.runP dsF xsF S.dec S.G.rec₀ S.G.z₀.2 (sBG
                                    S.G).logLeaves S.G.early
      (saltG S.G) (KF S.DK S.DP) S.P :=
  S.inputFieldsAtReadingsAsBytes (digToBytes c) (size_digToBytes c) (m.map digToBytes)

/-- At the digests of bytes of the right length it is the T at these bytes. -/
theorem DescriptionDataAtFiles.tOf_at (S : DescriptionDataAtFiles Zk) (c : ByteArray) (hc : c.size = 32) (seven : List ByteArray)
    (h7 : ∀ b ∈ seven, b.size = 32) :
    S.inputFieldsAtReadings (bytesToDig c) (seven.map bytesToDig) = S.inputFieldsAtReadingsAsBytes c hc seven := by
  have e2 : (seven.map bytesToDig).map digToBytes = seven := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id seven]
    exact List.map_congr_left fun b hb => digToBytes_bytesToDig b (h7 b hb)
  have key : ∀ (c' : ByteArray) (h' : c'.size = 32), c' = c → S.inputFieldsAtReadingsAsBytes c' h' seven = S.inputFieldsAtReadingsAsBytes c hc
      seven := by
    intro c' h' e
    subst e
    rfl
  unfold DescriptionDataAtFiles.inputFieldsAtReadings
  rw [e2]
  exact key _ _ (digToBytes_bytesToDig c hc)

/-- As a frame of descriptionOfFields. -/
def DescriptionDataAtFiles.toDescriptionFields (S : DescriptionDataAtFiles Zk) : DescriptionFields where
  X := XF
  A := S.A
  E := S.E
  DK := S.DK
  DP := S.DP
  runK := S.runK
  runP := S.runP
  ds := dsF
  xs := xsF
  dec := S.dec
  rK := S.G.rec₀
  rP := S.G.z₀.2
  depthReq := (sBG S.G).logLeaves
  early := S.G.early
  salt := saltG S.G
  K := KF S.DK S.DP
  P := S.P
  inputFieldsAtReadings := S.inputFieldsAtReadings
  ext := S.ext

/-- What a run hands the term. -/
structure DecodedProof where
  aux : List Token
  cm : Dig 256
  rcd : RecFull
  copy : ℕ
  fT : FileIn
  e : EntryIn
  fB : FileIn

/-- One number that is no token of the vocabulary: the further tokens of the form that is laid
  where a decoder refuses. -/
def auxNo : List Token := [Inst.Model.ppref.V]

/-- The typed proof that is laid of a form, at the bytes c in the three cfg. -/
def DescriptionDataAtFiles.proofOf (S : DescriptionDataAtFiles Zk) (c : ByteArray) (f : DecodedProof) :=
  proofE S.DK S.DP S.runK S.runP S.G.rec₀ S.G.z₀.2 (sTG S.G) (sBG S.G) S.G.early dsF
    xsF S.dec f.aux f.cm f.rcd f.copy { f.fT with cfg := c } { f.e with cfg := c } { f.fB with cfg
        := c }

/-- The type of typed proofs at these letters: OF Zk's LETTERS ALONE. -/
abbrev DescriptionDataAtFiles.Typed (S : DescriptionDataAtFiles Zk) : Type :=
  TypedProof (threeProtocolsAtFullSize S.A (relationsAndEncodingOfClaims S.A S.E) S.DK S.DP S.runK S.runP dsF xsF S.dec S.G.rec₀
      S.G.z₀.2
    (sBG S.G).logLeaves S.G.early (saltG S.G)) S.P

/-- The way back, field by field, NAMING NO T: `InnerCompilerInput.back`'s own text
  (Johnson/Top/InnerCompiledVerifierBack.lean): it hangs on the types alone. -/
def DescriptionDataAtFiles.typedOf (S : DescriptionDataAtFiles Zk) (c : ByteArray) (f : DecodedProof) : S.Typed :=
  ((S.proofOf c f).1, KeyRoot.ofV (S.proofOf c f).2.1, OfflineLinkOnlineProof.ofV (S.proofOf c f).2.2)

/-- It is `back` at the input of every T of these letters. -/
theorem DescriptionDataAtFiles.typedOf_back (S : DescriptionDataAtFiles Zk)
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize S.A S.E S.DK S.DP S.runK S.runP dsF xsF S.dec S.G.rec₀ S.G.z₀.2 (sBG
                                    S.G).logLeaves
      S.G.early (saltG S.G) (KF S.DK S.DP) S.P) (c : ByteArray) (f : DecodedProof) :
    S.typedOf c f = (innerCompilerInputAtFullSize T).back (S.proofOf c f) := rfl

/-- innerCompiledVerifier along an equation of letters, the typed proof fixed. -/
theorem DescriptionDataAtFiles.verifyTwo_congr (S : DescriptionDataAtFiles Zk)
    {T T' : InnerCompilerInputAndAnalysisFieldsAtFullSize S.A S.E S.DK S.DP S.runK S.runP dsF xsF S.dec S.G.rec₀ S.G.z₀.2 (sBG
                                    S.G).logLeaves
      S.G.early (saltG S.G) (KF S.DK S.DP) S.P} (e : T = T') (hash : VerifiableInference.Hash)
    (commitment : Commitment) (prompt output : List Token) (q : S.Typed) :
    (innerCompiledVerifier (innerCompilerInputAtFullSize T) commitment prompt output q).evaluate hash =
      (innerCompiledVerifier (innerCompilerInputAtFullSize T') commitment prompt output q).evaluate hash := by
  subst e
  rfl

/-- The honest side's letters. -/
structure CommitterAndProverOfDecodedProof where
  Shown : Type
  shown : (s : IntegerTransformer.Settings) → ModelWeights s → Shown
  Rand : Type
  sample : RandomizedAlgorithm Rand
  commit : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand →
    DeterministicAlgorithm Commitment
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm DecodedProof

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (Hn : CommitterAndProverOfDecodedProof)

/-- **D's own parser**: one query: c; then the way back of the proof that is laid of the form. -/
def parserOfDecodedProof (Z : PublicFiles) (_ _ : List Token) (f : DecodedProof) : DeterministicAlgorithm
    (TypedProof (threeProtocolsAtFullSize (S Z).toDescriptionFields.A (relationsAndEncodingOfClaims (S Z).toDescriptionFields.A (S Z).toDescriptionFields.E) (S Z).toDescriptionFields.DK (S
                                                                                                  Z).toDescriptionFields.DP
      (S Z).toDescriptionFields.runK (S Z).toDescriptionFields.runP (S Z).toDescriptionFields.ds (S Z).toDescriptionFields.xs (S Z).toDescriptionFields.dec (S
                                                                                Z).toDescriptionFields.rK (S Z).toDescriptionFields.rP (S Z).toDescriptionFields.depthReq (S Z).toDescriptionFields.early
      (S Z).toDescriptionFields.salt) (S Z).toDescriptionFields.P) :=
  .query (configString Z) fun c => .done ((S Z).typedOf (digToBytes c) f)

/-- The side of descriptionOfFields. -/
def committerAndProverWithDecodedProofParser : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields where
  Shown := Hn.Shown
  shown := Hn.shown
  Rand := Hn.Rand
  sample := Hn.sample
  commit := Hn.commit
  Form := DecodedProof
  parse := parserOfDecodedProof S
  prove := Hn.prove

/-- **THE VALUE.** -/
def descriptionOnDecodedProof : Description := descriptionOfFields (fun Z => (S Z).toDescriptionFields) (committerAndProverWithDecodedProofParser S Hn)

/-- Its own parser asks once. -/
theorem parserOfDecodedProof_within (Z : PublicFiles) : Parser.Within ((descriptionOnDecodedProof S Hn).parse Z) 1 :=
  fun _ _ _ _ => trivial

/-- So it is within the goals' budget: the goals' own first conjunct, at D. -/
theorem parserOfDecodedProof_withinHonestBudget (Z : PublicFiles) : Parser.Within ((descriptionOnDecodedProof S Hn).parse Z) honestBudget :=
  fun _ _ _ _ => trivial

/-- What D's own parser returns at hashOf O. -/
theorem proofAt_parserOfDecodedProof (Z : PublicFiles) (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size =
                       32)
    (prompt output : List Token) (f : DecodedProof) :
    (parserOfDecodedProof S Z prompt output f).evaluate (hashOf O) = (S Z).typedOf (cThru O (asDescriptionFiles Z)) f :=
        by
  show (S Z).typedOf (digToBytes (cAt Z (hashOf O))) f = _
  rw [cAt_hashOf, digToBytes_bytesToDig _ hO]

/-- **THE GOALS' verify AT D, WITH D's OWN PARSER, AT hashOf O: IT IS innerCompiledVerifier AT THE SEAM's r.**
  -/
theorem verify_descriptionOnDecodedProof (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (O : ByteArray → ByteArray)
    (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (f : DecodedProof) :
    (VerifierAndGoals.verify (descriptionOnDecodedProof S Hn) Z ((descriptionOnDecodedProof S Hn).parse Z) commitment prompt output f).evaluate
        (hashOf O) =
      (innerCompiledVerifier
        (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadingsAsBytes (cThru O (asDescriptionFiles Z)) hO
                       (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)))))
        commitment prompt output
        ((innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadingsAsBytes (cThru O (asDescriptionFiles Z)) hO
                         (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))))).back
          ((S Z).proofOf (cThru O (asDescriptionFiles Z)) f))).evaluate (hashOf O) := by
  have h1 := verify_descriptionOfFields_thru (fun Z => (S Z).toDescriptionFields) (committerAndProverWithDecodedProofParser S Hn) Z ((descriptionOnDecodedProof S Hn).parse Z)
      scope O hO
    commitment prompt output f
  have h2 : proofAt ((descriptionOnDecodedProof S Hn).parse Z) prompt output f (hashOf O) =
      (S Z).typedOf (cThru O (asDescriptionFiles Z)) f := proofAt_parserOfDecodedProof S Z O hO prompt output f
  have h3 := (S Z).verifyTwo_congr ((S Z).tOf_at _ hO _ h7) (hashOf O) commitment prompt output
    ((S Z).typedOf (cThru O (asDescriptionFiles Z)) f)
  exact (h1.trans (congrArg (fun q : (S Z).Typed =>
    (innerCompiledVerifier (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (bytesToDig (cThru O (asDescriptionFiles Z)))
                               ((sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))).map bytesToDig))) commitment
          prompt output
      q).evaluate (hashOf O)) h2)).trans h3

end FlashProve
