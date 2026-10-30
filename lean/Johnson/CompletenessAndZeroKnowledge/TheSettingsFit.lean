-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/TheSettingsFit.lean: THE SETTINGS AT flashProveAtFiles MEET THE COMPILER'S CONDITIONS.

1.  At any layout: settingsOf meets SettingsFit where the starts have their lengths, the table's salts
    and the leaves' salts have the strict format's length, the slots fit and the table fits its tree.
2.  At flashProveAtFiles, at public files in use, at every value of the public reading, for any provers and
    limits and for every starts of 256 bits: SettingsFit and PathsFit.
3.  At plain starts: RunValuesAreSent, so these starts owe the protocol nothing.
4.  A test that can fail: a constant start of any other length than 256 breaks SettingsFit.
5.  This file claims nothing of a protocol: this file proves neither completeness nor zero
    knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.TheSettings
import VerifiableInference.Final.CompilerHonestSide
import Johnson.WholeKey.WorkOf

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
open AtPublicFiles.Bridge (winR)
open IntegerTransformer (Settings)

variable {Index Instance : Type} {L : HolographicProtocol Index Instance} {offlineRoundMarks : RoundSplits L.offline.shape}
  {linkRoundMarks : RoundSplits L.link.shape}

section AtAnyLayout
variable (layout : HashLayout L offlineRoundMarks linkRoundMarks) (provers : HonestProvers L)
  (starts : SaltStarts provers) (leafFiller : layout.LeafBody) (limits : SearchLimits)
  (furtherCopies : ℕ) (copyNumber : ℕ → ℕ) (slotSalts : RequestLeafSaltLayout)
  (coins : CoinNums layout.LeafBody) (tableStart : Bits)

/-- The three public slots fit the request trees. -/
structure RequestLeafSaltLayout.Fit (slotSalts : RequestLeafSaltLayout)
    (layout : HashLayout L offlineRoundMarks linkRoundMarks) : Prop where
  offline : slotSalts.offlineSlot < 2 ^ layout.queryLayout.depthReqT
  link : slotSalts.linkSlot < 2 ^ layout.queryLayout.depthReqL
  online : slotSalts.onlineSlot < 2 ^ layout.queryLayout.depthReq
  /-- a table's salts start with 256 bits -/
  table : ∀ digest, (slotSalts.tableStart digest).length = 256

/-- Slots of 0 fit every request tree. -/
theorem plainSlotSalts_fit : plainSlotSalts.Fit layout :=
  ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, Nat.two_pow_pos _, fun _ => List.length_replicate ..⟩

/-- The seven lengths at settingsOf. -/
theorem settingsOf_lengths {startBits : ℕ}
    (h : starts.LengthsFit layout.compilerParameters.sFS startBits)
    (hTable : tableStart.length + coins.ℓ = layout.compilerParameters.sMT)
    (hLeaf : startBits + coins.ℓ = layout.compilerParameters.sMT) (rounds : ℕ → Prop) :
    (settingsOf layout provers starts leafFiller limits furtherCopies copyNumber slotSalts coins
      tableStart).Lengths rounds where
  tableSalt := hTable
  valuesOffline := h.valuesOffline
  valuesLink := h.valuesLink
  valuesOnline := h.valuesOnline
  startsOffline := fun v i b salt hv _ hs => by
    show (starts.saltStartOffline v i b salt).length + coins.ℓ = _
    rw [h.startsOffline v i b salt hv hs]
    exact hLeaf
  startsLink := fun v i b salt hv _ hs => by
    show (starts.saltStartLink v i b salt).length + coins.ℓ = _
    rw [h.startsLink v i b salt hv hs]
    exact hLeaf
  startsOnline := fun v i b salt hv _ hs => by
    show (starts.saltStartOnline v i b salt).length + coins.ℓ = _
    rw [h.startsOnline v i b salt hv hs]
    exact hLeaf

/-- **SettingsFit at settingsOf.** -/
theorem settingsFit_settingsOf {startBits : ℕ}
    (h : starts.LengthsFit layout.compilerParameters.sFS startBits)
    (hTable : tableStart.length + coins.ℓ = layout.compilerParameters.sMT)
    (hLeaf : startBits + coins.ℓ = layout.compilerParameters.sMT)
    (hOffline : coins.slotT < 2 ^ layout.queryLayout.depthReqT)
    (hLink : coins.slotL < 2 ^ layout.queryLayout.depthReqL)
    (hOnline : coins.slotB < 2 ^ layout.queryLayout.depthReq)
    (hFits : L.wordLength ≤ 2 ^ layout.queryLayout.depth) :
    SettingsFit layout provers (settingsOf layout provers starts leafFiller limits furtherCopies
      copyNumber slotSalts coins tableStart) :=
  settingsFit_of (settingsOf_lengths layout provers starts leafFiller limits furtherCopies copyNumber
      slotSalts coins tableStart h hTable hLeaf _)
    ⟨List.length_replicate .., hOffline, hLink, hOnline, Or.inr hFits⟩

/-- At plain starts the run values are sent, at any provers. -/
theorem plainStarts_sent (inRange : Index → Prop) (leaf : layout.LeafBody) :
    RunValuesAreSent layout provers (settingsOf layout provers (zeroSaltStarts provers) leaf limits
      furtherCopies copyNumber slotSalts coins tableStart) inRange :=
  runValues_plain_holds _ _ _ _ _ _ _ _ _ rfl

/-- Beyond the window a leaf's salt is its start and the filler: so under SettingsFit a constant
start and the free bits make the strict format's length. -/
theorem constantStart_length (start : Bits)
    (hF : SettingsFit layout provers (settingsOf layout provers (constantStarts provers start)
      leafFiller limits furtherCopies copyNumber slotSalts coins tableStart)) :
    start.length + coins.ℓ = layout.compilerParameters.sMT := by
  have f := hF.lengths.coT ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩
  have e : (start ++ if winR (L := L) < winR (L := L) ∧ 0 < AtPublicFiles.Bridge.winK layout.queryLayout ∧
      0 < AtPublicFiles.Bridge.winJ layout.queryLayout then _ else List.replicate coins.ℓ false).length =
      layout.compilerParameters.sMT := f.leaf (winR (L := L)) false 0 0
  rw [if_neg (fun z => lt_irrefl _ z.1), List.length_append, List.length_replicate] at e
  exact e

end AtAnyLayout

/-! ## At flashProveAtFiles -/

section AtFlashProve
variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
  (provers : HonestProvers (FlashProtocol files)) (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout)

/-- **SETTINGSFIT AT flashProveAtFiles**, at public files in use, at every reading. -/
theorem theSettings_fit (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (starts : SaltStarts provers) (h : starts.LengthsFit 256 256) (reading : FlashReading files)
    (slots : slotSalts.Fit (flashLayout files settings fallbackInstance reading)) :
    SettingsFit (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers starts limits slotSalts reading) :=
  settingsFit_settingsOf (flashLayout files settings fallbackInstance reading) provers starts _
    limits 0 (fun _ => 0) slotSalts _ _ h
    ((congrArg (· + 320) (slots.table _)).trans (AtPublicFiles.ZetaAt.sMT_built files scope live allZeroDigest []).symm)
    (show 256 + 320 = (flashProveDescription.input files allZeroDigest []).compilerParameters.sMT from
      (AtPublicFiles.ZetaAt.sMT_built files scope live allZeroDigest []).symm)
    slots.offline slots.link slots.online (flash_table_fits files settings fallbackInstance reading)

/-- **PATHSFIT AT flashProveAtFiles**, at public files in use, at every reading. -/
theorem theSettings_paths (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (starts : SaltStarts provers) (h : starts.LengthsFit 256 256) (reading : FlashReading files)
    (slots : slotSalts.Fit (flashLayout files settings fallbackInstance reading)) :
    PathsFit (flashLayout files settings fallbackInstance reading).queryLayout
      (honestSide (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers starts limits slotSalts reading)).side :=
  pathsFit_of_coins (theSettings_fit files settings fallbackInstance provers limits slotSalts scope
    live starts h reading slots).coins

/-- **NOT EMPTY: plain starts meet it**, at public files in use, at every reading, with the run values
sent. -/
theorem plainSettings_meet (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (inRange : (flashProveDescription.C files).I → Prop) (reading : FlashReading files) :
    SettingsFit (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers (zeroSaltStarts provers) limits
          plainSlotSalts reading) ∧
      RunValuesAreSent (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers (zeroSaltStarts provers) limits
          plainSlotSalts reading) inRange :=
  ⟨theSettings_fit files settings fallbackInstance provers limits plainSlotSalts scope live _
      (plainStarts_lengthsFit provers 256) reading (plainSlotSalts_fit _),
    plainStarts_sent _ provers limits 0 (fun _ => 0) plainSlotSalts _ _ inRange _⟩

/-- **A TEST THAT CAN FAIL**: at files in use a constant start of another length than 256 bits breaks
SettingsFit at every reading. -/
theorem constantStart_of_other_length_fails (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (start : Bits) (hne : start.length ≠ 256)
    (reading : FlashReading files) :
    ¬ SettingsFit (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers (constantStarts provers start) limits
        slotSalts reading) := fun hF => by
  have e := constantStart_length (flashLayout files settings fallbackInstance reading) provers _ limits
    0 (fun _ => 0) slotSalts _ _ start hF
  have hs : (flashLayout files settings fallbackInstance reading).compilerParameters.sMT = 576 :=
    flash_sMT files settings fallbackInstance scope live reading
  rw [hs] at e
  have e' : start.length + 320 = 576 := e
  omega

end AtFlashProve

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.plainSlotSalts_fit
#print axioms VerifiableInference.Compilation.settingsOf_lengths
#print axioms VerifiableInference.Compilation.settingsFit_settingsOf
#print axioms VerifiableInference.Compilation.plainStarts_sent
#print axioms VerifiableInference.Compilation.constantStart_length
#print axioms VerifiableInference.Compilation.theSettings_fit
#print axioms VerifiableInference.Compilation.theSettings_paths
#print axioms VerifiableInference.Compilation.plainSettings_meet
#print axioms VerifiableInference.Compilation.constantStart_of_other_length_fails
