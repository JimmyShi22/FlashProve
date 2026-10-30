-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/BindsAtThe.lean: THE GOALS ON BINDING, G9 (Ladder.lean) AND G9bits
(Ladder/Bits.lean), AT THE ONE CLOSED DESCRIPTION: `descriptionOfDataOnBytes flashProveData`
(Johnson/Goal/Tie/DescriptionOfData.lean;
Johnson/Goal/Description/Lay.lean) WITH THE HONEST COMMITTER AND THE EXTRACTOR LAID IN AS TERMS
(Johnson/Goal/Conditions/DescribeTerms.lean). Definitions, statements and proofs.

Why. Johnson/Goal/Conditions/BindsAtDescriptionOfFields.lean shows the laws that opening-form binding takes as
hypotheses at every family of letters, under tests on numbers and two premises (hsec, hdec), taken
as hypotheses where the claims and the coding of an index are letters. At `flashProveData` they are terms:
the claims are
`claimsReqAt` at `numsRef` and the files' own table; the tests on numbers hold at every set of
public files (`fit_theLay`, Johnson/Goal/Conditions/NumbersAtThe.lean: the family fails closed).

Main names (namespace `FlashProve`).
  `TheCoins`: what of the honest side binding does not pin, as one record: the two enumerations of
    coins (ri, sl), a body b₀, both provers, the randomness with its sampler, the stored table's
    shape and the generator (the letters of `coinsAnchor`, Johnson/Top/CoinsAnchor.lean).
  `phiThe`, `backThe`: `phiO` (Johnson/PV/DescribeO.lean) and `backO`
    (Johnson/PV/DescribeBinds.lean) at valid settings; none, and the matrix of a fixed index, else.
  `theTerms K`: `HonestTerms` at the description: T := `layoutsByPublicReadingAtDescriptionOfFields`
    (Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFields.lean); φ := `phiThe`; back := `backThe`; coins := `coinsAnchor`;
    the rest K's.
  `theBound K` := fun _ => (descriptionOfDataOnBytes flashProveData).withTerms (theTerms K): the description of which the
    goals below speak. `verify_theBound`: its verifier is `descriptionOfDataOnBytes flashProveData`'s, by definition.
  **`G9_theBound`**, **`G9bits_theBound`**: the stored G9 and G9bits, AT EVERY K.

THE PREMISES, ALL: hE: at every set of public files `theCoding` is `codingCells`
(Johnson/Flat/CodingCells.lean): AN EQUATION BETWEEN TWO CLOSED TERMS: it falls by rfl:
`hE_the` (Johnson/Goal/Description/AtBound.lean). NOTHING ELSE: no test on numbers, no premise on
soundness,
no law on a committer or an extractor. K stands under "for all".

WHO READS EACH LETTER. K: the honest committer (the FIRST members of ri and sl; b₀; shape, in the
second string that it asks), the honest provers (proveT, prove), the sampler; THE STATEMENTS G9 AND
G9bits THEMSELVES (the opener names randomness of the type K.Rand; the committer is K's); no
verifier, no extractor, no bound on an error but through the count 2 of `coinsAnchor`. gen and the
value of the randomness: NOBODY (the first limit). NOTHING THAT THE VERIFIER READS STANDS UNDER
"THERE IS".

Limits.
- TOO WEAK FOR A ROW ON OPENING-FORM BINDING: at `descriptionOfDataOnBytes flashProveData` the
  letter `coinBound` is 0, so gen lands in Fin 1 and the told committer's number is always 0: AT EVERY K
  the randomness and the generator reach nothing in the commitment, and G9 and G9bits of `theBound
  K` speak of ONE setting of pads, tails and salts, fixed in K before the hash function is drawn. AN
  OPENER THAT PICKS ITS OWN COINS IS NOT IN THEM. "At every K" stands outside the probability. The
  cure: `theWide K W` (Johnson/Goal/Conditions/WideAtThe.lean), where the number of coins is a
  letter.
- THE VERIFIER IS IDLE IN G9 AND G9bits: they stay proved whatever the three decisions are. They
  weigh only beside soundness AT THE SAME EXTRACTOR and completeness WITH THIS COMMITTER, of this
  very description: neither is shown here.
- THE COMMITTER IS TIED TO NO PROGRAM. The generator, the shape and the enumerations are K's.
- NOTHING ON HIDING: by the first limit the committer draws nothing, at every K.
- `theBound K` IS `VerifierAndGoals.theDescription` ONLY IF THAT NAME IS LAID SO, at one K.
- Several parts of `flashProveData` are place-holders (Johnson/Goal/Description/Lay.lean says which):
opening-form binding reads of
  them the rounds' data, through the tests on numbers alone.
- The public files are fixed before the hash function is drawn.
- The committer asks `configString Z` twice: once in `coinsAnchor`, once in the told record's public
  reading; the count counts both.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.BindsAtDescriptionOfFields
import Johnson.Goal.Conditions.NumbersAtThe
import Johnson.Goal.Conditions.DescribeTermsCoins
import Johnson.Goal.Conditions.DescribeTermsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF GF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8 theCoding theKeyData
  theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate theProvers theNamed
  LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

/-- The pair at which the told record's input is taken: zeros; no further digests. -/
def allZeroDigest : Digest := fun _ => false

/-- The description of the protocol at which FlashProve stands, before the terms are laid in. -/
abbrev flashProveDescription : Description := descriptionOfDataOnBytes flashProveData

/-- **What of the honest side binding does not pin.** -/
structure TheCoins where
  ri : (Z : PublicFiles) → _root_.Iop.Enum (flashProveDescription.input Z allZeroDigest []).protocol.EncodingRandomness
  sl : PublicFiles → _root_.Iop.Enum (ℕ → Rom.Bits)
  b₀ : (Z : PublicFiles) → (flashProveDescription.input Z allZeroDigest []).LeafBody
  proveT : (Z : PublicFiles) → (flashProveDescription.input Z allZeroDigest []).Index × (flashProveDescription.input Z allZeroDigest []).protocol.EncodingRandomness × (ℕ → Rom.Bits) →
    (l : List ((flashProveDescription.input Z allZeroDigest []).Instance × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 (flashProveDescription.input Z allZeroDigest []).protocol
      (flashProveDescription.input Z allZeroDigest []).offlineRoundSplits (flashProveDescription.input Z allZeroDigest []).linkRoundSplits) l)
  Rand : Type
  sample : RandomizedAlgorithm Rand
  /-- the stored table's shape, as bytes -/
  shape : PublicFiles → ByteArray
  /-- from the randomness and the key's digest to the told committer's number -/
  gen : (Z : PublicFiles) → Rand → Digest → Fin ((flashProveDescription.input Z allZeroDigest []).coinBound + 1)
  prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm FormBytes

/-- From the extractor's matrix to weights. -/
def phiThe (Z : PublicFiles) (s : IntegerTransformer.Settings) (M : (flashProveDescription.input Z allZeroDigest []).Index) :
    Option (ModelWeights s) :=
  if hv : settingsAreValid s = true then VerifierAndGoals.Fit.phiO hv M else none

/-- The matrix of given weights. -/
def backThe (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s) :
    (flashProveDescription.input Z allZeroDigest []).Index :=
  if hv : settingsAreValid s = true then VerifierAndGoals.Fit.backO hv w
  else Flat.matrixOf (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero)

variable (K : TheCoins)

/-- **The honest side's terms at the description.** -/
def theTerms : HonestTerms flashProveDescription :=
  honestTermsAtDescriptionOfFields (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀) allZeroDigest []
    phiThe backThe K.ri K.sl K.b₀ K.proveT K.Rand K.sample
    (fun Z => coinsAnchor Z (K.shape Z) (K.gen Z)) K.prove

/-- **The description of which the goals below speak.** -/
def theBound : SecondHashFunctionType → Description := fun _ => flashProveDescription.withTerms (theTerms K)

/-- Its verifier is `descriptionOfDataOnBytes flashProveData`'s. -/
theorem verify_theBound (o : SecondHashFunctionType) (Z : PublicFiles) {Form : Type} (parse : Parser flashProveDescription Z Form) :
    verify (theBound K o) Z parse = verify flashProveDescription Z parse := rfl

theorem sec_the (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) :
    phiThe Z (settingsOfRead pp) (backThe Z (settingsOfRead pp) w) = some w := by
  unfold phiThe backThe
  rw [dif_pos (valid_of_read hr), dif_pos (valid_of_read hr)]
  exact VerifierAndGoals.Fit.section_backO (valid_of_read hr) w

theorem back_the (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) :
    backThe Z (settingsOfRead pp) w = Flat.matrixOf (indexOfWeights (valid_of_read hr) w) :=
  dif_pos (valid_of_read hr)

theorem dec_the
    (hE : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL)
      Subtype.val)
    (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) (r : (flashProveDescription.input Z allZeroDigest []).protocol.EncodingRandomness)
    (sd : (flashProveDescription.input Z allZeroDigest []).protocol.OutOfDomainSeed) :
    (flashProveDescription.input Z allZeroDigest []).protocol.decodeIndex ((flashProveDescription.input Z allZeroDigest []).protocol.encodeIndex (backThe Z (settingsOfRead pp) w) r)
      ((flashProveDescription.input Z allZeroDigest []).protocol.recOf (backThe Z (settingsOfRead pp) w) r sd) =
      some (backThe Z (settingsOfRead pp) w) := by
  rw [back_the Z pp hr w]
  exact decodes_of_eq (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) (theCoding (asDescriptionFiles Z))
    (hE (asDescriptionFiles Z)) (flashProveDescription.F Z) (flashProveDescription.P Z) _ r sd

/-- What the yes of the frame's one test says, at every Z. -/
theorem parts_the (Z : PublicFiles) :
    FrameFitFullD (KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) theQueries
      (dataAtFiles flashProveData Z).G.c.first.binding.logLeaves (dataAtFiles flashProveData Z).G.k.oneTime.binding.logLeaves
      (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP dsFull frD.xs :=
  frameFitFullD_parts (fit_theLay Z)

/-- **THE LAWS THAT OPENING-FORM BINDING (`BindsWith`) TAKES AS HYPOTHESES, AT THE DESCRIPTION, AT
EVERY K.** -/
theorem bindLaws_the
    (hE : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL)
      Subtype.val)
    (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) :
    BindLaws (theTerms K) Z (settingsOfRead pp) 8 2 :=
  bindLaws_honestTermsAtDescriptionOfFields (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀) allZeroDigest []
    phiThe backThe K.ri K.sl K.b₀ K.proveT K.Rand K.sample
    (fun Z => coinsAnchor Z (K.shape Z) (K.gen Z)) K.prove Z (settingsOfRead pp) (parts_the Z).hk
    (parts_the Z).hE (parts_the Z).wK (parts_the Z).dK (parts_the Z).wP (parts_the Z).dP
    (parts_the Z).hK40 2 (by norm_num)
    (fun ρ => queryBound_coinsAnchor Z (K.shape Z) (K.gen Z) ρ) (sec_the Z pp hr)
    (dec_the hE Z pp hr)

/-- **THE STORED G9 AT THE DESCRIPTION, AT EVERY K.** -/
theorem G9_theBound
    (hE : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL)
      Subtype.val) : G9 (theBound K) :=
  G9_withTerms (fun _ => flashProveDescription) (fun _ => theTerms K) 8 2 (by
                       have h1 : honestBudget = 2 ^ 48 := rfl
                       rw [h1]
                       norm_num) fun Z pp _ h₂ => bindLaws_the K hE Z pp h₂

/-- **THE STORED G9bits AT THE DESCRIPTION, AT EVERY K.** -/
theorem G9bits_theBound
    (hE : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL)
      Subtype.val) : G9bits (theBound K) :=
  G9bits_withTerms (fun _ => flashProveDescription) (fun _ => theTerms K) 8 2 (by norm_num)
    fun Z pp _ h₂ => bindLaws_the K hE Z pp h₂

end FlashProve

#print axioms FlashProve.verify_theBound
#print axioms FlashProve.bindLaws_the
#print axioms FlashProve.G9_theBound
#print axioms FlashProve.G9bits_theBound
