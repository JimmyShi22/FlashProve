-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsAtDescriptionOfFields.lean: THE GOAL ON BINDING, G9, AT EVERY DESCRIPTION
`descriptionOfFields (fun Z => (S Z).toDescriptionFields) H` (Johnson/Goal/Tie/DescribeT.lean; S a family of `DescriptionDataAtFiles`,
Johnson/Goal/Tie/DescriptionOnDecodedProof.lean) WITH THE HONEST COMMITTER AND THE EXTRACTOR LAID IN AS TERMS
(Johnson/Goal/Conditions/DescribeTerms.lean), over the told record of
Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFields.lean. Definitions, statements and proofs. Conditionals: no S is built.

Why. Johnson/Goal/Conditions/DescribeTermsAt.lean shows the laws that opening-form binding owes
(`BindLaws`) at a slot that lays an older coding of queries. The term that runs lays another coding;
its told record is `layoutsByPublicReadingAtDescriptionOfFields`. Here the same laws are shown there.

Main names (namespace `FlashProve`).
  `honestTermsAtDescriptionOfFields`: `HonestTerms` at the description: T := `layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀`. The index of given
    weights (back), the way back (φ), the coins' enumerations and algorithm, the provers and the
    randomness are letters.
  `honestTermsAtDescriptionOfFields_noCoin` … `honestTermsAtDescriptionOfFields_number`: the laws one by one.
  **`bindLaws_honestTermsAtDescriptionOfFields`**: `BindLaws` at tP := 8. PAID: the told law's six and total (`layoutsByPublicReading_noCoin` …
    `layoutsByPublicReading_total`, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean); the first of the wire's laws (`wiresOfFullD`);
    the reading's count (`pub8_queries`); the test on numbers (the tree's depth is the code's a = 32
    and the wiring has KF DK DP + 1 blocks, both by definition; then arithmetic).
  **`G9_descriptionOfFields_withTerms`**: the stored G9. **`G9bits_descriptionOfFields_withTerms`**: the stored G9bits
    (Ladder/Bits.lean), under the same premises.
  **`nearestSoundAndBinding_descriptionOfFields`**: with `SoundUnderPolicyAt` of that very description: the row's
    form at a named error. **`nearestSoundAndBinding_descriptionOfFields_of_G8`**: the same from the stored G8 of
    the description as it is, whatever its honest side, where (S Z).ext is the told record's named
    extractor, then φ (hext).

THE PREMISES OF `G9_descriptionOfFields_withTerms`, ALL. At every Z in scope, at K := KF DK DP: hk, hEnt (the entry
file's four: `EntryFit`, Johnson/Flat/Dec/EntrySound.lean), wK dK wP dP, hK40 (K + 2 < 2^40): TESTS
ON NUMBERS, all among what the yes of the frame's one test says (`FrameFitFullD`,
Johnson/Flat/Dec/FailsClosed.lean, with hK40). At every Z in scope that the reader
reads: hsec (φ gives back the weights from their index); hdec (the
decoder gives back the index of every set of weights from its honest word and record). Of the coins'
algorithm: it asks at most q ≤ 2^40 queries. hsec AND hdec STAY PREMISES BECAUSE (S Z).A AND (S Z).E
ARE LETTERS. At an S whose A is `claimsReqAt` at `numsRef` and the files' own table, whose E is
`codingCells` (Johnson/Flat/CodingCells.lean), with back := `backO` and φ := `phiO`, they are
`obj_decodes_index_full` and `section_backO` (Johnson/PV/DescribeBinds.lean): so it is done at the
older slot in Johnson/Goal/Conditions/DescribeTermsAt.lean. NOT AMONG THEM: keySound, proofSound,
the theorem on codes, meaning, carries, any law on a committer or an extractor.

WHO READS EACH LETTER: as in Johnson/Goal/Conditions/DescribeTerms.lean. S: the verifier (all fields
but E's honest side, N and ext); the committer (A, E, the public files through the reading, the
coding). H: its parse, the verifier; the rest is overwritten by `withTerms`, as is (S Z).ext. c₀,
m₀: the pair at which the told record's input is taken: any would do.
NOTHING THAT THE VERIFIER READS STANDS UNDER "THERE IS".

Limits.
- A THEOREM ON `(descriptionOfFields …).withTerms …` IS A THEOREM ON THAT DESCRIPTION: the description that
  runs is of this form only if its `ext` and its honest side's `commit` are laid so. The goals'
  verifier is not touched (`verify_withTerms`).
- THE VERIFIER IS IDLE IN G9. THE COMMITTER IS TIED TO NO PROGRAM.
- All limits of the files named above stand.


Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFields
import Johnson.Flat.Dec.EntrySound
import Johnson.Goal.Conditions.DescribeTermsSound
import Johnson.Goal.Conditions.DescribeTermsBits
import Johnson.Top.KeyTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) (c₀ : Digest)
  (m₀ : List (Dig 256))

/-- The description. -/
abbrev dsOf (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) : Description :=
  descriptionOfFields (fun Z => (S Z).toDescriptionFields) H

variable
  (φ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → ((dsOf S H).input Z c₀ m₀).Index →
    Option (ModelWeights s))
  (back : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → ModelWeights s → ((dsOf S H).input Z c₀
          m₀).Index) (ri : (Z : PublicFiles) → _root_.Iop.Enum ((dsOf S H).input Z c₀ m₀).protocol.EncodingRandomness)
  (sl : PublicFiles → _root_.Iop.Enum (ℕ → Rom.Bits)) (b₀ : (Z : PublicFiles) → ((dsOf S H).input Z c₀ m₀).LeafBody)
  (proveT : (Z : PublicFiles) → ((dsOf S H).input Z c₀ m₀).Index × ((dsOf S H).input Z c₀ m₀).protocol.EncodingRandomness × (ℕ →
                                       Rom.Bits) → (l : List (((dsOf S H).input Z c₀ m₀).Instance × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((dsOf S H).input Z c₀ m₀).protocol
      ((dsOf S H).input Z c₀ m₀).offlineRoundSplits ((dsOf S H).input Z c₀ m₀).linkRoundSplits) l))
  (Rand : Type) (sample : RandomizedAlgorithm Rand)
  (coins : (Z : PublicFiles) → Rand → DeterministicAlgorithm (Fin (((dsOf S H).input Z c₀ m₀).coinBound + 1)))
  (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm H.Form)

/-- The honest side's terms at the description. -/
def honestTermsAtDescriptionOfFields : HonestTerms (dsOf S H) where
  c₀ := fun _ => c₀
  m₀ := fun _ => m₀
  T := layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀
  φ := φ
  back := back
  ri := ri
  sl := sl
  b₀ := b₀
  proveT := proveT
  Rand := Rand
  sample := sample
  coins := coins
  prove := prove

local notation "Qs" => honestTermsAtDescriptionOfFields S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove

theorem honestTermsAtDescriptionOfFields_noCoin (Z : PublicFiles) : ((Qs).T Z).Pub.NoCoin := layoutsByPublicReading_noCoin (S Z) c₀ m₀

theorem honestTermsAtDescriptionOfFields_asks (Z : PublicFiles) : ((Qs).T Z).Pub.AsksIn fun _ x => ((Qs).T Z).Pt x :=
  layoutsByPublicReading_asks (S Z) c₀ m₀

theorem honestTermsAtDescriptionOfFields_once (Z : PublicFiles) : NoRepeat ((Qs).T Z).Pub := layoutsByPublicReading_once (S Z) c₀ m₀

theorem honestTermsAtDescriptionOfFields_spare (Z : PublicFiles) : ∀ d x, ((Qs).T Z).Pt x → IsOther (((Qs).T Z).m d) x :=
  layoutsByPublicReading_spare (S Z) c₀ m₀

theorem honestTermsAtDescriptionOfFields_word (Z : PublicFiles) : ∀ d d', ((Qs).T Z).part d = ((Qs).T Z).part d' →
    (extractorOverOneHashFunction (((Qs).T Z).m d) (indexExtractorAtRootAndOutOfDomainSample ((dsOf S H).input Z c₀ m₀).queryLayout)).Ei =
      (extractorOverOneHashFunction (((Qs).T Z).m d') (indexExtractorAtRootAndOutOfDomainSample ((dsOf S H).input Z c₀ m₀).queryLayout)).Ei :=
  layoutsByPublicReading_word (S Z) c₀ m₀

theorem honestTermsAtDescriptionOfFields_code (Z : PublicFiles) : ZKCP.CodeIsOneToOne ((Qs).T Z).encT := layoutsByPublicReading_code (S Z) c₀ m₀

theorem honestTermsAtDescriptionOfFields_total (Z : PublicFiles) : ∀ key, ((Qs).T Z).encT key ≠ none := layoutsByPublicReading_total (S Z) c₀ m₀

theorem wire_descriptionOfFields (Z : PublicFiles) (hk : kThree .two (S Z).DK [] (S Z).DP ≤ KF (S Z).DK (S Z).DP)
    (hEnt : EntryFit (KF (S Z).DK (S Z).DP) dsF)
    (wK : (S Z).DK.workFit = true) (dK : (S Z).DK.depthFit = true)
    (wP : (S Z).DP.workFit = true) (dP : (S Z).DP.depthFit = true) :
    ((dsOf S H).input Z c₀ m₀).queryLayout.OKG :=
  (wiresOfFullD (S Z).A (relationsAndEncodingOfClaims (S Z).A (S Z).E) (S Z).DK (S Z).DP (S Z).runK (S Z).runP dsF xsF
    (S Z).dec _ _ _ _ _ (S Z).P (KF (S Z).DK (S Z).DP) ((S Z).inputFieldsAtReadings c₀ m₀).depthReqT hk
    hEnt.bL hEnt.wLk hEnt.own hEnt.dL wK dK wP dP).1

theorem honestTermsAtDescriptionOfFields_readingQueryBound (Z : PublicFiles) : ((Qs).T Z).Pub.QueryBound 8 :=
  pub8_queries recordGround (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay

theorem wireDepth_descriptionOfFields (Z : PublicFiles) : ((dsOf S H).input Z c₀ m₀).queryLayout.depth = frS.P.T.a := rfl

theorem wireBlocks_descriptionOfFields (Z : PublicFiles) : ((dsOf S H).input Z c₀ m₀).queryLayout.K = KF (S Z).DK (S Z).DP + 1 := rfl

theorem honestTermsAtDescriptionOfFields_number (Z : PublicFiles) (hK40 : KF (S Z).DK (S Z).DP + 1 + 1 < 2 ^ 40) (q : ℕ)
    (hq : q ≤ 2 ^ 40) : q + ((Qs).tCommit Z 8 + 1) ≤ honestBudget := by
  have ha : frS.P.T.a = 32 := by decide
  show q + (8 + (2 * 2 ^ ((dsOf S H).input Z c₀ m₀).queryLayout.depth +
    2 * (((dsOf S H).input Z c₀ m₀).queryLayout.K + 1)) + 1) ≤ 2 ^ 48
  rw [wireDepth_descriptionOfFields, wireBlocks_descriptionOfFields, ha]
  have h1 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have h2 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
  have h3 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
  rw [h1, h3]
  rw [h2] at hK40 hq
  omega

/-- **THE LAWS THAT OPENING-FORM BINDING STILL OWES, AT THE DESCRIPTION THAT LAYS THE RUN'S CODING.** -/
theorem bindLaws_honestTermsAtDescriptionOfFields (Z : PublicFiles) (s : IntegerTransformer.Settings)
    (hk : kThree .two (S Z).DK [] (S Z).DP ≤ KF (S Z).DK (S Z).DP)
    (hEnt : EntryFit (KF (S Z).DK (S Z).DP) dsF)
    (wK : (S Z).DK.workFit = true) (dK : (S Z).DK.depthFit = true)
    (wP : (S Z).DP.workFit = true) (dP : (S Z).DP.depthFit = true)
    (hK40 : KF (S Z).DK (S Z).DP + 1 + 1 < 2 ^ 40) (q : ℕ) (hq : q ≤ 2 ^ 40)
    (hc : ∀ ρ, (coins Z ρ).toRandomized.QueryBound q)
    (hsec : ∀ w, φ Z s (back Z s w) = some w)
    (hdec : ∀ w r sd, ((dsOf S H).input Z c₀ m₀).protocol.decodeIndex (((dsOf S H).input Z c₀ m₀).protocol.encodeIndex (back Z s
                                    w) r) (((dsOf S H).input Z c₀ m₀).protocol.recOf (back Z s w) r sd) = some (back Z s w)) :
    BindLaws (Qs) Z s 8 q where
  noCoin := honestTermsAtDescriptionOfFields_noCoin S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
  asks := honestTermsAtDescriptionOfFields_asks S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
  once := honestTermsAtDescriptionOfFields_once S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
  spare := honestTermsAtDescriptionOfFields_spare S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
  word := honestTermsAtDescriptionOfFields_word S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
  code := honestTermsAtDescriptionOfFields_code S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
  wire := wire_descriptionOfFields S H c₀ m₀ Z hk hEnt wK dK wP dP
  section_ := hsec
  decodes := hdec
  total := honestTermsAtDescriptionOfFields_total S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
  reading := honestTermsAtDescriptionOfFields_readingQueryBound S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
  coinsWithin := hc
  number := honestTermsAtDescriptionOfFields_number S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z hK40 q hq

/-- **THE STORED G9 AT THE DESCRIPTION WITH THE TERMS LAID IN.** -/
theorem G9_descriptionOfFields_withTerms
    (hk : ∀ Z, InScope Z = true → kThree .two (S Z).DK [] (S Z).DP ≤ KF (S Z).DK (S Z).DP)
    (hEnt : ∀ Z, InScope Z = true → EntryFit (KF (S Z).DK (S Z).DP) dsF)
    (wK : ∀ Z, InScope Z = true → (S Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (S Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (S Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (S Z).DP.depthFit = true)
    (hK40 : ∀ Z, InScope Z = true → KF (S Z).DK (S Z).DP + 1 + 1 < 2 ^ 40) (q : ℕ)
    (hq : q ≤ 2 ^ 40) (hc : ∀ Z ρ, (coins Z ρ).toRandomized.QueryBound q)
    (hsec : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w, φ Z (settingsOfRead pp) (back Z (settingsOfRead pp) w) = some w)
    (hdec : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w r sd, ((dsOf S H).input Z c₀ m₀).protocol.decodeIndex
        (((dsOf S H).input Z c₀ m₀).protocol.encodeIndex (back Z (settingsOfRead pp) w) r)
        (((dsOf S H).input Z c₀ m₀).protocol.recOf (back Z (settingsOfRead pp) w) r sd) =
          some (back Z (settingsOfRead pp) w)) :
    G9 fun _ => (dsOf S H).withTerms (Qs) :=
  G9_withTerms (fun _ => dsOf S H) (fun _ => Qs) 8 q
    (le_trans hq (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    fun Z pp h₁ h₂ => bindLaws_honestTermsAtDescriptionOfFields S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
      (settingsOfRead pp) (hk Z h₁) (hEnt Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁) (dP Z h₁) (hK40 Z h₁)
      q hq (hc Z)
      (hsec Z pp h₁ h₂) (hdec Z pp h₁ h₂)

/-- **`SoundAndBinding` OF THE GOALS' OWN VERIFIER, IN ITS NEAREST FORM, AT A NAMED ERROR, AT THAT
DESCRIPTION**: from soundness under the files' policy of that very description, and the premises of
`G9_descriptionOfFields_withTerms`. -/
theorem nearestSoundAndBinding_descriptionOfFields (epsS : ℕ → ℕ → ℝ≥0∞)
    (sound : SoundUnderPolicyAt ((dsOf S H).withTerms (Qs)) epsS)
    (hk : ∀ Z, InScope Z = true → kThree .two (S Z).DK [] (S Z).DP ≤ KF (S Z).DK (S Z).DP)
    (hEnt : ∀ Z, InScope Z = true → EntryFit (KF (S Z).DK (S Z).DP) dsF)
    (wK : ∀ Z, InScope Z = true → (S Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (S Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (S Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (S Z).DP.depthFit = true)
    (hK40 : ∀ Z, InScope Z = true → KF (S Z).DK (S Z).DP + 1 + 1 < 2 ^ 40) (q : ℕ)
    (hq : q ≤ 2 ^ 40) (hc : ∀ Z ρ, (coins Z ρ).toRandomized.QueryBound q)
    (hsec : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w, φ Z (settingsOfRead pp) (back Z (settingsOfRead pp) w) = some w)
    (hdec : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w r sd, ((dsOf S H).input Z c₀ m₀).protocol.decodeIndex
        (((dsOf S H).input Z c₀ m₀).protocol.encodeIndex (back Z (settingsOfRead pp) w) r)
        (((dsOf S H).input Z c₀ m₀).protocol.recOf (back Z (settingsOfRead pp) w) r sd) =
          some (back Z (settingsOfRead pp) w)) :
    NearestSoundAndBinding (fun _ => (dsOf S H).withTerms (Qs))
      (joinError epsS fun t => epsBind honestBudget (t + q)) :=
  nearestSoundAndBinding_withTerms (fun _ => dsOf S H) (fun _ => Qs) 8 q epsS sound
    fun Z pp h₁ h₂ => bindLaws_honestTermsAtDescriptionOfFields S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
      (settingsOfRead pp) (hk Z h₁) (hEnt Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁) (dP Z h₁) (hK40 Z h₁)
      q hq (hc Z)
      (hsec Z pp h₁ h₂) (hdec Z pp h₁ h₂)

/-- **THE STORED G9bits AT THE DESCRIPTION WITH THE TERMS LAID IN**: the premises of
`G9_descriptionOfFields_withTerms`. -/
theorem G9bits_descriptionOfFields_withTerms
    (hk : ∀ Z, InScope Z = true → kThree .two (S Z).DK [] (S Z).DP ≤ KF (S Z).DK (S Z).DP)
    (hEnt : ∀ Z, InScope Z = true → EntryFit (KF (S Z).DK (S Z).DP) dsF)
    (wK : ∀ Z, InScope Z = true → (S Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (S Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (S Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (S Z).DP.depthFit = true)
    (hK40 : ∀ Z, InScope Z = true → KF (S Z).DK (S Z).DP + 1 + 1 < 2 ^ 40) (q : ℕ)
    (hq : q ≤ 2 ^ 40) (hc : ∀ Z ρ, (coins Z ρ).toRandomized.QueryBound q)
    (hsec : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w, φ Z (settingsOfRead pp) (back Z (settingsOfRead pp) w) = some w)
    (hdec : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w r sd, ((dsOf S H).input Z c₀ m₀).protocol.decodeIndex
        (((dsOf S H).input Z c₀ m₀).protocol.encodeIndex (back Z (settingsOfRead pp) w) r)
        (((dsOf S H).input Z c₀ m₀).protocol.recOf (back Z (settingsOfRead pp) w) r sd) =
          some (back Z (settingsOfRead pp) w)) :
    G9bits fun _ => (dsOf S H).withTerms (Qs) :=
  G9bits_withTerms (fun _ => dsOf S H) (fun _ => Qs) 8 q hq
    fun Z pp h₁ h₂ => bindLaws_honestTermsAtDescriptionOfFields S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove Z
      (settingsOfRead pp) (hk Z h₁) (hEnt Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁) (dP Z h₁) (hK40 Z h₁)
      q hq (hc Z)
      (hsec Z pp h₁ h₂) (hdec Z pp h₁ h₂)

/-- **THE ROW's FORM FROM G8 OF THE DESCRIPTION AS IT IS**: hG8: the stored G8 of
`descriptionOfFields (fun Z => (S Z).toDescriptionFields) H`, whatever its honest side; hext: at every Z in scope that the
reader reads, (S Z).ext is the told record's named extractor, then φ, by bind. -/
theorem nearestSoundAndBinding_descriptionOfFields_of_G8 (hG8 : G8 fun _ => dsOf S H)
    (hext : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      (S Z).ext (settingsOfRead pp) = fun commitment queryLog =>
        ((layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z).extractor commitment queryLog).bind (φ Z (settingsOfRead pp)))
    (hk : ∀ Z, InScope Z = true → kThree .two (S Z).DK [] (S Z).DP ≤ KF (S Z).DK (S Z).DP)
    (hEnt : ∀ Z, InScope Z = true → EntryFit (KF (S Z).DK (S Z).DP) dsF)
    (wK : ∀ Z, InScope Z = true → (S Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (S Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (S Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (S Z).DP.depthFit = true)
    (hK40 : ∀ Z, InScope Z = true → KF (S Z).DK (S Z).DP + 1 + 1 < 2 ^ 40) (q : ℕ)
    (hq : q ≤ 2 ^ 40) (hc : ∀ Z ρ, (coins Z ρ).toRandomized.QueryBound q)
    (hsec : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w, φ Z (settingsOfRead pp) (back Z (settingsOfRead pp) w) = some w)
    (hdec : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w r sd, ((dsOf S H).input Z c₀ m₀).protocol.decodeIndex
        (((dsOf S H).input Z c₀ m₀).protocol.encodeIndex (back Z (settingsOfRead pp) w) r)
        (((dsOf S H).input Z c₀ m₀).protocol.recOf (back Z (settingsOfRead pp) w) r sd) =
          some (back Z (settingsOfRead pp) w)) :
    ∃ epsS : ℕ → ℕ → ℝ≥0∞,
      (∀ t n, t ≤ queryBudget → n ≤ parserBudget → epsS t n ≤ ceiling) ∧
      NearestSoundAndBinding (fun _ => (dsOf S H).withTerms (Qs))
        (joinError epsS fun t => epsBind honestBudget (t + q)) := by
  obtain ⟨epsS, ceil, sound⟩ := hG8
  exact ⟨epsS, ceil, nearestSoundAndBinding_of_sound (fun _ => dsOf S H) (fun _ => Qs) 8 q epsS
    sound hext fun Z pp h₁ h₂ => bindLaws_honestTermsAtDescriptionOfFields S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins
      prove Z (settingsOfRead pp) (hk Z h₁) (hEnt Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁) (dP Z h₁)
      (hK40 Z h₁) q hq (hc Z)
      (hsec Z pp h₁ h₂) (hdec Z pp h₁ h₂)⟩

end FlashProve

#print axioms FlashProve.bindLaws_honestTermsAtDescriptionOfFields
#print axioms FlashProve.G9_descriptionOfFields_withTerms
#print axioms FlashProve.nearestSoundAndBinding_descriptionOfFields
#print axioms FlashProve.G9bits_descriptionOfFields_withTerms
#print axioms FlashProve.nearestSoundAndBinding_descriptionOfFields_of_G8
