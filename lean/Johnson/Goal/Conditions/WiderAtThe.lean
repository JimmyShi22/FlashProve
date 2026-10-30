-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WiderAtThe.lean: ONE FAMILY OF DESCRIPTIONS BESIDE theWide
(Johnson/Goal/Conditions/WideAtThe.lean): theWider K W. AT ITS MEMBERS THE NUMBER OF THE COMMITTER's
COINS MAY HANG ON A PUBLIC ANSWER OF THE HASH FUNCTION: c, the hash at configString Z. A reader of
the statements on binding below should know it: at theWide that number is gen Z ρ I; here it is
gen Z ρ c I. The coins' algorithm hands the generator BOTH answers that it asks for: the
configuration's digest c and the key's digest I. Its verifier is verify()'s; theWide is its member;
and the theorems named below hold at every member, each by the call that gave its twin at theWide.

Why. coinsAnchor (Johnson/Top/CoinsAnchor.lean) asks c := the hash at configString Z, then I := the
hash at anchorString c S, and hands gen the second alone. verify()'s parser lays c in front of every
stored leaf's salt. A committer whose number of coins cannot hang on c cannot make such leaves.

Main names.
  coinsBoth   coinsAnchor's text with gen ρ c I in the place of gen ρ I: the same two queries.
  WiderCoins   the number of the committer's coins, and the generator into it, which reads both.
  theWiderTerms, theWider   theWideTerms' and theWide's texts at coinsBoth.
  WideCoins.wider   a WideCoins as a WiderCoins: its generator does not read c.
  queryBound_coinsBoth, evaluate_coinsBoth, coins_theWider   at most two queries; its value.
  theWide_eq   theWide K W is theWider K (W.wider K): by unfolding.
  verify_theWider, parse_theWider, readMore_theWider, wider_extractor_bound, same_extractor_wider
    the verifier, the parser and the further reading are descriptionOfDataOnBytes flashProveData's; the extractor is
    theBound K's, and so theDescription's.
  bindLaws_wider, G9_theWider, G9bits_theWider, verifierWithin_theWider,
    soundUnderPolicyAtZ_bits_theWider, soundAndBinding_level_wider_at, soundOpened_level_wider_at
    EACH IS ITS TWIN's STATEMENT AND PROOF (bindLaws_wide, G9_theWide, G9bits_theWide:
    WideAtThe.lean; verifierWithin_theWide: MoreAtDigits.lean; soundUnderPolicyAtZ_bits_theWide:
    Johnson/Goal/TopAtZBinding.lean; soundAndBinding_level_wide_at, soundOpened_level_wide_at:
    Johnson/Goal/BindingOfCoreLevel.lean) with theWider in theWide's place: same premises, same
    errors.

No new step: each of these is its twin's call, and the steps are general in the coins'
algorithm (HonestTerms.reBound, BindLaws.reBound: Conditions/ReBound.lean;
soundUnderPolicyAtZ_reBound: TopAtZBinding.lean; verifierWithin_wide_iff:
Conditions/ReBoundGoals.lean). Every member of theWide is a member (theWide_eq). That there are more
members is read off coinsAnchor's text, whose generator is not handed c: no theorem here says so.

Limits. Nothing on hiding. (1) A statement on hiding at a member of theWider would need, AT EVERY
FIXED c AND I, the law of gen Z ρ c I over ρ: WiderCoins asks nothing of it: the constant 0 is a
member, as at theWide (the limit that lean/GAPS.md's appendix tells of the placeholder): so it is a
premise to NAME then, not a fact of the type. (2) A W whose number names the salts leafSalt c (s j)
lays DERIVED salts: right for completeness at a stored set, which is what the programs do; for
hiding, fresh masks and masks derived from a seed are two cases, and this file treats neither: so no
statement on hiding at that W.
This file states no goal: it proves the forms G9 and G9bits at a stand-in family (G9_theWider,
G9bits_theWider). The family theWider is defined here; member (HomeAtWider.lean), at which
completeOn_last (HomeLast.lean) concludes, is taken in it. A THIRD STAND-IN DESCRIPTION with the
verifier of descriptionOfDataOnBytes flashProveData: not theDescription. The sampler is K's, as at theWide: it is not
turned. No theorem ties the committer to the release's program that commits. The twins' limits
travel whole: the premises KeySoundAt Z and ProofSoundAt Z stay premises. No completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.BindingOfCoreLevel
import Johnson.Goal.SameExtractorWide

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice

/-- **The coins' algorithm that keeps both answers**: the configuration's digest; the key's digest;
then gen at both. -/
def coinsBoth {Rand α : Type} (Z : PublicFiles) (S : ByteArray) (gen : Rand → Digest → Digest → α)
    (ρ : Rand) : DeterministicAlgorithm α :=
  .query (configString Z) fun c => .query (anchorString c S) fun I => .done (gen ρ c I)

/-- **It asks at most twice.** -/
theorem queryBound_coinsBoth {Rand α : Type} (Z : PublicFiles) (S : ByteArray)
    (gen : Rand → Digest → Digest → α) (ρ : Rand) :
    (coinsBoth Z S gen ρ).toRandomized.QueryBound 2 :=
  fun _ _ => trivial

/-- Its value at a hash function. -/
theorem evaluate_coinsBoth {Rand α : Type} (Z : PublicFiles) (S : ByteArray)
    (gen : Rand → Digest → Digest → α) (ρ : Rand) (hash : Hash) :
    (coinsBoth Z S gen ρ).evaluate hash =
      gen ρ (hash (configString Z)) (hash (anchorString (hash (configString Z)) S)) := rfl

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem descriptionOfDataOnBytes

/-- The number of the committer's coins, and the generator into it: it reads the configuration's
digest and the key's digest. -/
structure WiderCoins (K : TheCoins) where
  bound : PublicFiles → ℕ
  gen : (Z : PublicFiles) → K.Rand → Digest → Digest → Fin (bound Z + 1)

variable (K : TheCoins)

/-- A WideCoins as a WiderCoins: its generator does not read the configuration's digest. -/
def WideCoins.wider (W : WideCoins K) : WiderCoins K := ⟨W.bound, fun Z ρ _ I => W.gen Z ρ I⟩

variable (W : WiderCoins K)

/-- The honest side's terms. -/
def theWiderTerms : HonestTerms (flashProveDescription.reBound W.bound) :=
  (theTerms K).reBound W.bound fun Z => coinsBoth Z (K.shape Z) (W.gen Z)

/-- **The family beside theWide.** -/
def theWider : SecondHashFunctionType → Description := fun _ => (flashProveDescription.reBound W.bound).withTerms (theWiderTerms K W)

/-- **theWide is its member.** -/
theorem theWide_eq (W' : WideCoins K) : theWide K W' = theWider K (W'.wider K) := rfl

/-- **The number of the told committer's coins is the generator's at both answers.** -/
theorem coins_theWider (Z : PublicFiles) (ρ : K.Rand) (hash : Hash) :
    ((theWiderTerms K W).coins Z ρ).evaluate hash =
      W.gen Z ρ (hash (configString Z))
        (hash (anchorString (hash (configString Z)) (K.shape Z))) := rfl

/-- **Its verifier is `descriptionOfDataOnBytes flashProveData`'s.** -/
theorem verify_theWider (o : SecondHashFunctionType) (Z : PublicFiles) {Form : Type} (parse : Parser flashProveDescription Z Form) :
    verify (theWider K W o) Z parse = verify flashProveDescription Z parse :=
  (verify_withTerms (theWiderTerms K W) Z parse).trans (verify_reBound flashProveDescription W.bound Z parse)

/-- The parser is `descriptionOfDataOnBytes flashProveData`'s. -/
theorem parse_theWider (o : SecondHashFunctionType) (Z : PublicFiles) : (theWider K W o).parse Z = flashProveDescription.parse Z := rfl

/-- The reading of the further public files is `descriptionOfDataOnBytes flashProveData`'s. -/
theorem readMore_theWider (o : SecondHashFunctionType) (Z : PublicFiles) : (theWider K W o).readMore Z = flashProveDescription.readMore Z :=
  rfl

/-- The laws that binding owes: bindLaws_wide's text. -/
theorem bindLaws_wider (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) :
    BindLaws (theWiderTerms K W) Z (settingsOfRead pp) 8 2 :=
  (bindLaws_the K hE_the Z pp hr).reBound (theTerms K) W.bound _
    (fun ρ => queryBound_coinsBoth Z (K.shape Z) (W.gen Z) ρ) (bindLaws_the K hE_the Z pp
    hr).number

/-- G9_theWide's text. -/
theorem G9_theWider : G9 (theWider K W) :=
  G9_withTerms (fun _ => flashProveDescription.reBound W.bound) (fun _ => theWiderTerms K W) 8 2 (by
                       have h1 : honestBudget = 2 ^ 48 := rfl
                       rw [h1]
                       norm_num) fun Z pp _ h₂ => bindLaws_wider K W Z pp h₂

/-- G9bits_theWide's text. -/
theorem G9bits_theWider : G9bits (theWider K W) :=
  G9bits_withTerms (fun _ => flashProveDescription.reBound W.bound) (fun _ => theWiderTerms K W) 8 2 (by norm_num)
    fun Z pp _ h₂ => bindLaws_wider K W Z pp h₂

/-- verifierWithin_theWide's text. -/
theorem verifierWithin_theWider (o : SecondHashFunctionType) : VerifierWithin (theWider K W o) :=
  (verifierWithin_wide_iff (theTerms K) W.bound
    fun Z => coinsBoth Z (K.shape Z) (W.gen Z)).2 (verifierWithin_theBound K o)

end FlashProve

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference
open P5J

/- Lean compares these names and does not open them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins) (W : WiderCoins K)

/-- wide_extractor_bound's text. -/
theorem wider_extractor_bound (o : SecondHashFunctionType) :
    (theWider K W o).extractor = (theBound K o).extractor := by
  funext Z s commitment queryLog
  rfl

/-- **The extractor of `theWider K W` is that of `atSecondHashFunction theDescription`.** -/
theorem same_extractor_wider (o : SecondHashFunctionType) :
    (theWider K W o).extractor = (atSecondHashFunction theDescription).extractor :=
  (wider_extractor_bound K W o).trans (same_extractor_bound K o)

/-- soundUnderPolicyAtZ_bits_theWide's text. -/
theorem soundUnderPolicyAtZ_bits_theWider (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) :
    SoundUnderPolicyAtZ ((flashProveDescription.reBound W.bound).withTerms (theWiderTerms K W)) soundnessErrorInQueries Z pp :=
  soundUnderPolicyAtZ_reBound (theTerms K) W.bound _ soundnessErrorInQueries Z pp
    (soundUnderPolicyAtZ_bits_theBound K OnBytes.secondHashFunction Z pp scope hr kS pS)

/-- **`SoundAndBinding` at one Z, of `theWider K W`, at `levelError`**:
soundAndBinding_level_wide_at's text. -/
theorem soundAndBinding_level_wider_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z) (pS : ProofSoundAt Z) :
    SoundAndBinding (systemOfRecord (atSecondHashFunction (theWider K W)) Z (settingsOfRead pp)) levelError :=
  soundAndBinding_of_atZ_within _ soundnessErrorInQueries bindingErrorInQueries Z pp
    (soundUnderPolicyAtZ_bits_theWider K W Z pp scope hr kS pS) (G9bits_theWider K W) scope hr exact
    verifierQueryAllowance (parserWithin_of_verifierWithin (verifierWithin_theWider K W OnBytes.secondHashFunction) Z scope)

/-- **`SoundOpened`**, at twice that error: soundOpened_level_wide_at's text. -/
theorem soundOpened_level_wider_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z) (pS : ProofSoundAt Z) :
    SoundOpened (systemOfRecord (atSecondHashFunction (theWider K W)) Z (settingsOfRead pp)) fun t =>
      2 * levelError t :=
  soundOpened_of_soundAndBinding _ _ (soundAndBinding_level_wider_at K W Z pp scope hr exact kS pS)

end VerifierAndGoals.AtTheName

#print axioms FlashProve.queryBound_coinsBoth
#print axioms FlashProve.evaluate_coinsBoth
#print axioms FlashProve.theWide_eq
#print axioms FlashProve.coins_theWider
#print axioms FlashProve.verify_theWider
#print axioms FlashProve.parse_theWider
#print axioms FlashProve.readMore_theWider
#print axioms FlashProve.bindLaws_wider
#print axioms FlashProve.G9_theWider
#print axioms FlashProve.G9bits_theWider
#print axioms FlashProve.verifierWithin_theWider
#print axioms VerifierAndGoals.AtTheName.wider_extractor_bound
#print axioms VerifierAndGoals.AtTheName.same_extractor_wider
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_bits_theWider
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_wider_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_wider_at
