-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/TheSettings.lean: THE COMPILER'S SETTINGS AT flashProveAtFiles: ONE VALUE.

1.  What the honest side chooses beside its three provers, written out at the protocol, at every set
    of public files and every value of the public reading, for ANY three provers. Nothing here reads
    more of the provers than the types of their coins.
2.  SaltStarts: the ten fields of CompiledSettings that make the public starts of a compiled run's
    salts. zeroSaltStarts is one value of it: no run value, 256 zeros. The format's starts, where stored
    salts begin with the digest, are another value, not written here.
3.  settingsOf fills the other ten fields for any layout; theSettings is settingsOf at flashProveAtFiles:
    one copy, numbered 0, a leaf's salt has 256 public and 320 free bits.
4.  The three search limits are arguments: their values are settled by the numbers on completeness
    and the hash budget.
5.  theCoinBound: the committer's one number, by coinsRange, which does not read the public reading.
6.  This file claims nothing of a protocol: this file proves neither completeness nor zero
    knowledge of the protocol.
-/
import Johnson.Face.FinalStatement
import E2E.ZetaSalt
import E2E.LinkLaidAny
import Johnson.FrontRoad.CoinsEnough

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles OnBytes.WholeKey OnBytes.FrontRoad OnBytes.Prover
open VerifierAndGoals FlashProve
open IntegerTransformer (Settings)

variable {Index Instance : Type}

/-! ## 1 The salts' starts -/

/-- **The public starts of a compiled run's salts**, and the run values of which they are made. -/
structure SaltStarts {protocol : HolographicProtocol Index Instance} (provers : HonestProvers protocol) where
  RunValues : Type
  wellFormed : RunValues → Prop
  runValuesOffline : provers.offlineProver.Coin → RunValues
  runValuesLink : provers.linkProver.Coin → RunValues
  runValuesOnline : provers.onlineProver.Coin → RunValues
  readOffline : Plains protocol.offline.shape → RunValues
  readLink : Plains protocol.link.shape → RunValues
  readOnline : Plains protocol.onlineBatch.loc.shape → RunValues
  saltStartOffline : RunValues → ℕ → Bool → Bits → Bits
  saltStartLink : RunValues → ℕ → Bool → Bits → Bits
  saltStartOnline : RunValues → ℕ → Bool → Bits → Bits

variable {L : HolographicProtocol Index Instance} {offlineRoundMarks : RoundSplits L.offline.shape}
  {linkRoundMarks : RoundSplits L.link.shape} {provers : HonestProvers L}

/-- Every coin gives well-formed run values, and at such values, after a first salt of firstSaltBits
bits, every start has startBits bits. -/
structure SaltStarts.LengthsFit (starts : SaltStarts provers) (firstSaltBits startBits : ℕ) :
    Prop where
  valuesOffline : ∀ κ, starts.wellFormed (starts.runValuesOffline κ)
  valuesLink : ∀ κ, starts.wellFormed (starts.runValuesLink κ)
  valuesOnline : ∀ κ, starts.wellFormed (starts.runValuesOnline κ)
  startsOffline : ∀ v i b salt, starts.wellFormed v → salt.length = firstSaltBits →
    (starts.saltStartOffline v i b salt).length = startBits
  startsLink : ∀ v i b salt, starts.wellFormed v → salt.length = firstSaltBits →
    (starts.saltStartLink v i b salt).length = startBits
  startsOnline : ∀ v i b salt, starts.wellFormed v → salt.length = firstSaltBits →
    (starts.saltStartOnline v i b salt).length = startBits

/-- **Constant starts**: no run value; every start is one string. -/
def constantStarts (provers : HonestProvers L) (start : Bits) : SaltStarts provers where
  RunValues := Unit
  wellFormed := fun _ => True
  runValuesOffline := fun _ => ()
  runValuesLink := fun _ => ()
  runValuesOnline := fun _ => ()
  readOffline := fun _ => ()
  readLink := fun _ => ()
  readOnline := fun _ => ()
  saltStartOffline := fun _ _ _ _ => start
  saltStartLink := fun _ _ _ _ => start
  saltStartOnline := fun _ _ _ _ => start

/-- **Plain starts**: every start is 256 zeros. -/
abbrev zeroSaltStarts (provers : HonestProvers L) : SaltStarts provers :=
  constantStarts provers (List.replicate 256 false)

/-- Plain starts have 256 bits, after any first salt. -/
theorem plainStarts_lengthsFit (provers : HonestProvers L) (firstSaltBits : ℕ) :
    (zeroSaltStarts provers).LengthsFit firstSaltBits 256 where
  valuesOffline := fun _ => trivial
  valuesLink := fun _ => trivial
  valuesOnline := fun _ => trivial
  startsOffline := fun _ _ _ _ _ _ => List.length_replicate ..
  startsLink := fun _ _ _ _ _ _ => List.length_replicate ..
  startsOnline := fun _ _ _ _ _ _ => List.length_replicate ..

/-! ## 2 The settings at a layout -/

/-- The three search limits: in round i a search may try limit i + 1 nonces. -/
structure SearchLimits where
  offline : ℕ → ℕ
  link : ℕ → ℕ
  online : ℕ → ℕ

/-- What stands behind a slot's value in a request tree's leaf: free bits, then a public tail. In the
byte format the tail is the 64-bit index of the slot's leaf and the free bits are the 8 · saltBytes
bits of the stored salt (OnBytes/Prover/Print/Carrier.lean, field rsalt): a value not written here. -/
structure RequestLeafSaltLayout where
  freeBits : ℕ
  tail : ℕ → Bits
  /-- the public slot of each of the three kinds of run -/
  offlineSlot : ℕ
  linkSlot : ℕ
  onlineSlot : ℕ
  /-- the public start of a table's salts, at the digest that the public reading gives -/
  tableStart : Iop.Dig 256 → Bits

/-- No free bit, no tail, every slot 0, a table's salts starting with 256 zeros. The format's value is
another. -/
def plainSlotSalts : RequestLeafSaltLayout := ⟨0, fun _ => [], 0, 0, 0, fun _ => List.replicate 256 false⟩

/-- **The settings at any layout**, from the starts, the limits, the copies, the numbers on coins and
the public start of a table's salts. The filler has as many bits as a leaf's free part. -/
def settingsOf (layout : HashLayout L offlineRoundMarks linkRoundMarks)
    (provers : HonestProvers L) (starts : SaltStarts provers) (leafFiller : layout.LeafBody)
    (limits : SearchLimits) (furtherCopies : ℕ) (copyNumber : ℕ → ℕ) (slotSalts : RequestLeafSaltLayout)
    (coins : CoinNums layout.LeafBody) (tableStart : Bits) : CompiledSettings layout provers where
  leafFiller := leafFiller
  searchLimitOffline := limits.offline
  searchLimitLink := limits.link
  searchLimitOnline := limits.online
  furtherCopies := furtherCopies
  copyNumber := copyNumber
  RunValues := starts.RunValues
  wellFormed := starts.wellFormed
  runValuesOffline := starts.runValuesOffline
  runValuesLink := starts.runValuesLink
  runValuesOnline := starts.runValuesOnline
  readOffline := starts.readOffline
  readLink := starts.readLink
  readOnline := starts.readOnline
  saltStartOffline := starts.saltStartOffline
  saltStartLink := starts.saltStartLink
  saltStartOnline := starts.saltStartOnline
  slotTail := slotSalts.tail
  windowFiller := List.replicate coins.ℓ false
  coinNumbers := { coins with pre₀ := tableStart }

/-- The committer's range at settingsOf does not read the seed's queries, the answers' code or the
public start of a table's salts. -/
theorem coinsRange_settingsOf_seeds (layout : HashLayout L offlineRoundMarks linkRoundMarks)
    (seeds seeds' : OutOfDomainSampleQueryLayout 256 layout.queryLayout.K L layout.LeafBody offlineRoundMarks linkRoundMarks)
    (code code' : L.OutOfDomainAnswer → List (Iop.Dig 256))
    (provers : HonestProvers L) (starts : SaltStarts provers) (leafFiller : layout.LeafBody)
    (limits : SearchLimits) (furtherCopies : ℕ) (copyNumber : ℕ → ℕ) (slotSalts : RequestLeafSaltLayout)
    (coins : CoinNums layout.LeafBody) (pre pre' : Bits) :
    coinsRange (honestSide { layout with seedQueries := seeds, answerCode := code } provers
      (settingsOf { layout with seedQueries := seeds, answerCode := code } provers starts leafFiller
        limits furtherCopies copyNumber slotSalts coins pre)).side =
    coinsRange (honestSide { layout with seedQueries := seeds', answerCode := code' } provers
      (settingsOf { layout with seedQueries := seeds', answerCode := code' } provers starts leafFiller
        limits furtherCopies copyNumber slotSalts coins pre')).side := rfl

/-! ## 3 The value at flashProveAtFiles -/

/-- The protocol of flashProveAtFiles at public files. -/
abbrev FlashProtocol (files : PublicFiles) : HolographicProtocol (flashProveDescription.C files).I (flashProveDescription.C files).X :=
  (flashProveDescription.F files).withProvers (flashProveDescription.P files)

/-- A value of flashProveAtFiles's public reading. -/
abbrev FlashReading (files : PublicFiles) : Type := (layoutsOfBuiltDescription flashProveData allZeroDigest [] files).D

/-- The layout of flashProveAtFiles at a value of the public reading. -/
abbrev flashLayout (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (reading : FlashReading files) :
    HashLayout (FlashProtocol files) (flashProveDescription.F files).annT (flashProveDescription.F files).annL :=
  (flashProveWiring files settings fallbackInstance).layoutAtReading reading

/-- A leaf's body at flashProveAtFiles holds nothing: the empty list of bits. -/
def theLeafFiller (files : PublicFiles) : (flashProveDescription.input files allZeroDigest []).LeafBody := ([] : List Bool)

/-- The free bits of a leaf's salt: 320. -/
abbrev leafFreeBits : ℕ := 320

/-- The numbers on coins: the library's own, at a leaf's 320 free bits, with the three public slots. -/
def baseCoinNumbers (files : PublicFiles) (slotSalts : RequestLeafSaltLayout) : CoinNums (flashProveDescription.input files allZeroDigest []).LeafBody :=
  { AtPublicFiles.Premises.coinNums (flashProveDescription.input files allZeroDigest []) (theLeafFiller files) leafFreeBits
      slotSalts.freeBits with
    slotT := slotSalts.offlineSlot
    slotL := slotSalts.linkSlot
    slotB := slotSalts.onlineSlot }

/-- **THE SETTINGS AT flashProveAtFiles.** At every set of public files and every value of the reading, for
any provers: one copy, numbered 0. The starts, the limits and what stands behind a slot's value are
arguments. The start of a table's salts hangs on the digest that the reading gives. -/
def theSettings (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers)
    (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout) (reading : FlashReading files) :
    CompiledSettings (flashLayout files settings fallbackInstance reading) provers :=
  settingsOf (flashLayout files settings fallbackInstance reading) provers starts
    (theLeafFiller files) limits 0 (fun _ => 0) slotSalts (baseCoinNumbers files slotSalts)
    (slotSalts.tableStart ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).part reading))

/-- The reading at which the family is typed. -/
abbrev baseReading (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X) :
    FlashReading files :=
  (flashProveWiring files settings fallbackInstance).pair allZeroDigest []

/-- **The committer's one number ranges up to this.** -/
def theCoinBound (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers)
    (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout) : ℕ :=
  coinsRange (honestSide (flashLayout files settings fallbackInstance
      (baseReading files settings fallbackInstance)) provers
    (theSettings files settings fallbackInstance provers starts limits slotSalts
      (baseReading files settings fallbackInstance))).side - 1

/-- **The committer's range divides theCoinBound + 1 at every reading.** -/
theorem coinsRange_dvd_theCoinBound (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (starts : SaltStarts provers) (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout)
    (reading : FlashReading files) :
    coinsRange (honestSide (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers starts limits slotSalts reading)).side ∣
      theCoinBound files settings fallbackInstance provers starts limits slotSalts + 1 := by
  have e : coinsRange (honestSide (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers starts limits slotSalts reading)).side =
      coinsRange (honestSide (flashLayout files settings fallbackInstance
        (baseReading files settings fallbackInstance)) provers
      (theSettings files settings fallbackInstance provers starts limits slotSalts
        (baseReading files settings fallbackInstance))).side :=
    coinsRange_settingsOf_seeds _ _ _ _ _ provers starts _ limits 0 (fun _ => 0) slotSalts _ _ _
  rw [e]
  unfold theCoinBound
  rw [Nat.sub_add_cancel (coinsRange_pos _)]

/-- **THE HONEST PART OF flashProveAtFiles at these settings**: 688127 sessions on the one copy. -/
def theHonestPartOf (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers)
    (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout) : HonestProversAndSettingsAtFiles files settings where
  fallbackInstance := fallbackInstance
  provers := provers
  compiledSettings := theSettings files settings fallbackInstance provers starts limits slotSalts
  coinBound := theCoinBound files settings fallbackInstance provers starts limits slotSalts
  onlineRunsPerCopy := 688127

/-- **The first clause of RepliesFit**: the one copy bears the replies. -/
theorem replies_fit_copies (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (provers : HonestProvers (FlashProtocol files)) (starts : SaltStarts provers)
    (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout) (reading : FlashReading files) :
    finalReplyCount ≤
      (((theHonestPartOf files settings fallbackInstance provers starts limits
        slotSalts).compiledSettings reading).furtherCopies + 1) *
        (theHonestPartOf files settings fallbackInstance provers starts limits
          slotSalts).onlineRunsPerCopy :=
  Nat.le_of_eq (Nat.one_mul _).symm

/-! ## 4 The public numbers at files in use -/

/-- A leaf's salt has 576 bits. -/
theorem flash_sMT (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (reading : FlashReading files) :
    (flashLayout files settings fallbackInstance reading).compilerParameters.sMT = 576 :=
  AtPublicFiles.ZetaAt.sMT_built files scope live allZeroDigest []

/-- A run's first salt has 256 bits. -/
theorem flash_sFS (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (reading : FlashReading files) :
    (flashLayout files settings fallbackInstance reading).compilerParameters.sFS = 256 := rfl

/-- The table fits its tree. -/
theorem flash_table_fits (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (reading : FlashReading files) :
    (FlashProtocol files).wordLength ≤
      2 ^ (flashLayout files settings fallbackInstance reading).queryLayout.depth :=
  (AtPublicFiles.Shown.fits_built files allZeroDigest []).2.oka.base.fits

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.plainStarts_lengthsFit
#print axioms VerifiableInference.Compilation.settingsOf
#print axioms VerifiableInference.Compilation.coinsRange_settingsOf_seeds
#print axioms VerifiableInference.Compilation.theSettings
#print axioms VerifiableInference.Compilation.theCoinBound
#print axioms VerifiableInference.Compilation.coinsRange_dvd_theCoinBound
#print axioms VerifiableInference.Compilation.theHonestPartOf
#print axioms VerifiableInference.Compilation.replies_fit_copies
#print axioms VerifiableInference.Compilation.flash_sMT
#print axioms VerifiableInference.Compilation.flash_sFS
#print axioms VerifiableInference.Compilation.flash_table_fits
