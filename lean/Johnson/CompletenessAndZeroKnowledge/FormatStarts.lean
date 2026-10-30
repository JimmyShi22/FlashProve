-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/FormatStarts.lean: THE FORMAT'S SALT STARTS: a second value of SaltStarts (Johnson/CompletenessAndZeroKnowledge/TheSettings.lean), beside zeroSaltStarts.

1.  In the byte format a stored salt begins with the run value of its chain: the first salt itself before the join, then two further values
    that a prover's coin fixes. So a run value here is two strings of 32 bytes; the rounds at which the chains change are public.
2.  A link has no coin of this kind: its two further values are one fixed pair.
3.  formatStarts_lengthsFit: 256 bits, after a first salt of 256 bits. Zero run values are not ruled out: they fall in the exception of
    Johnson/CompletenessAndZeroKnowledge/UndoUpToOfBut.lean.
4.  SendsItsRunValues: what is asked of the provers; runValuesAreSent_formatStarts: it gives RunValuesAreSent. That the value of the provers
    meets it is not shown here. The tail behind a slot's value: formatTail.
5.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.TheSettingsFit
import VerifiableInference.Final.CompilerTheorems
import Run.CodingBitsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Compilation
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles OnBytes.WholeKey OnBytes.FrontRoad OnBytes.Prover
open _root_.Run (bytesToBits length_bytesToBits)

variable {Index Instance : Type} {L : HolographicProtocol Index Instance}

/-- The two further run values of a file. -/
abbrev FormatRuns : Type := ByteArray × ByteArray

/-- The bits with which a stored salt begins in round i: the first salt before round joinRound, then the two values. -/
def formatStart (joinRound thirdRound : ℕ) (runs : FormatRuns) (round : ℕ) (firstSalt : Bits) : Bits :=
  if round < joinRound then firstSalt
  else if round < thirdRound then bytesToBits runs.1 else bytesToBits runs.2

/-- The public rounds at which the chains change. -/
structure FormatRounds where
  offlineJoin : ℕ
  offlineThird : ℕ
  linkRounds : ℕ
  onlineJoin : ℕ
  onlineThird : ℕ

/-- **The format's starts.** runsOffline, runsOnline: what a prover's coin fixes; readOffline, readOnline: where the plain parts hold it. -/
def formatStarts (provers : HonestProvers L) (rounds : FormatRounds)
    (runsOffline : provers.offlineProver.Coin → FormatRuns) (runsOnline : provers.onlineProver.Coin → FormatRuns)
    (linkRuns : FormatRuns) (readOffline : Plains L.offline.shape → FormatRuns)
    (readOnline : Plains L.onlineBatch.loc.shape → FormatRuns) : SaltStarts provers where
  RunValues := FormatRuns
  wellFormed := fun runs => runs.1.size = 32 ∧ runs.2.size = 32
  runValuesOffline := runsOffline
  runValuesLink := fun _ => linkRuns
  runValuesOnline := runsOnline
  readOffline := readOffline
  readLink := fun _ => linkRuns
  readOnline := readOnline
  saltStartOffline := fun runs round _ firstSalt =>
    formatStart rounds.offlineJoin rounds.offlineThird runs round firstSalt
  saltStartLink := fun runs round _ firstSalt =>
    formatStart rounds.linkRounds rounds.linkRounds runs round firstSalt
  saltStartOnline := fun runs round _ firstSalt =>
    formatStart rounds.onlineJoin rounds.onlineThird runs round firstSalt

theorem formatStart_length (joinRound thirdRound : ℕ) (runs : FormatRuns) (round : ℕ) (firstSalt : Bits)
    (h : runs.1.size = 32 ∧ runs.2.size = 32) (hs : firstSalt.length = 256) :
    (formatStart joinRound thirdRound runs round firstSalt).length = 256 := by
  unfold formatStart
  split
  · exact hs
  · split
    · rw [length_bytesToBits, h.1]
    · rw [length_bytesToBits, h.2]

variable {provers : HonestProvers L} {rounds : FormatRounds}
  {runsOffline : provers.offlineProver.Coin → FormatRuns} {runsOnline : provers.onlineProver.Coin → FormatRuns}
  {linkRuns : FormatRuns} {readOffline : Plains L.offline.shape → FormatRuns}
  {readOnline : Plains L.onlineBatch.loc.shape → FormatRuns}

/-- **256 bits, after a first salt of 256 bits**, where every coin fixes two strings of 32 bytes. -/
theorem formatStarts_lengthsFit (hO : ∀ κ, (runsOffline κ).1.size = 32 ∧ (runsOffline κ).2.size = 32)
    (hB : ∀ κ, (runsOnline κ).1.size = 32 ∧ (runsOnline κ).2.size = 32)
    (hL : linkRuns.1.size = 32 ∧ linkRuns.2.size = 32) :
    (formatStarts provers rounds runsOffline runsOnline linkRuns readOffline readOnline).LengthsFit 256 256 where
  valuesOffline := hO
  valuesLink := fun _ => hL
  valuesOnline := hB
  startsOffline := fun _ _ _ _ hv hs => formatStart_length _ _ _ _ _ hv hs
  startsLink := fun _ _ _ _ hv hs => formatStart_length _ _ _ _ _ hv hs
  startsOnline := fun _ _ _ _ hv hs => formatStart_length _ _ _ _ _ hv hs

/-- **What is asked of the provers**: off the stops the plain parts of the offline and the online run hold the values that their coins fix.
RunVals' two clauses at these readers. -/
structure SendsItsRunValues (provers : HonestProvers L) (starts : SaltStarts provers) (inRange : Index → Prop) : Prop where
  offline : ∀ i r e κ ρ, inRange i → ρ ∉ provers.offlineProver.withheld (i, r, e) (L.recOf i r e) →
    starts.readOffline ((provers.offlineProver.strat (i, r, e) (L.recOf i r e) κ).run ρ).1.plains =
      starts.runValuesOffline κ
  online : ∀ i r e n x κ ρ, inRange i → ρ ∉ provers.onlineProver.withheld (i, r, e, n) (x, L.recOf i r e) →
    starts.readOnline ((provers.onlineProver.strat (i, r, e, n) (x, L.recOf i r e) κ).run ρ).1.plains =
      starts.runValuesOnline κ

/-- **It gives RunValuesAreSent at settingsOf.** The link's clause holds by the fixed pair. -/
theorem runValuesAreSent_formatStarts {offlineRoundMarks : RoundSplits L.offline.shape} {linkRoundMarks : RoundSplits L.link.shape}
    (layout : HashLayout L offlineRoundMarks linkRoundMarks) (leafFiller : layout.LeafBody) (limits : SearchLimits)
    (furtherCopies : ℕ) (copyNumber : ℕ → ℕ) (slotSalts : RequestLeafSaltLayout) (coins : CoinNums layout.LeafBody)
    (tableStart : Rom.Bits) (inRange : Index → Prop)
    (hS : SendsItsRunValues provers (formatStarts provers rounds runsOffline runsOnline linkRuns readOffline readOnline)
      inRange) :
    RunValuesAreSent layout provers
      (settingsOf layout provers (formatStarts provers rounds runsOffline runsOnline linkRuns readOffline readOnline)
        leafFiller limits furtherCopies copyNumber slotSalts coins tableStart) inRange :=
  ⟨hS.offline, fun _ _ _ _ _ _ _ => rfl, hS.online⟩

/-- **Under refuseUnserved the stops only grow**, so the provers still send their run values. -/
theorem SendsItsRunValues.refuse {inRange : Index → Prop}
    (h : SendsItsRunValues provers (formatStarts provers rounds runsOffline runsOnline linkRuns readOffline readOnline)
      inRange) (Served : Index → Instance → Prop) :
    SendsItsRunValues (provers.refuseUnserved Served)
      (formatStarts (provers.refuseUnserved Served) rounds runsOffline runsOnline linkRuns readOffline readOnline)
      inRange where
  offline := h.offline
  online := fun i r e n x κ ρ hi hρ => h.online i r e n x κ ρ hi fun hw => hρ (by
    rcases hw with hb | hh
    · exact Or.inl hb
    · exact Or.inr (Or.inr hh))

/-- The tail behind a slot's value: the 64-bit index of its leaf, in a tree of depth proofDepth at the slot proofSlot, and in a tree of
depth 0 elsewhere. One function serves all three kinds of run, since a compiled run reads it at its slot. -/
def formatTail (proofDepth proofSlot : ℕ) (slot : ℕ) : Bits :=
  if slot = proofSlot then bytesToBits (_root_.Fmt.u64n (2 ^ proofDepth + slot))
  else bytesToBits (_root_.Fmt.u64n (2 ^ 0 + slot))

/-- The proof file's slot: 0 in a tree of one leaf, else 1, so that it is told apart from the key's and the link's slot 0. -/
def formatProofSlot (proofDepth : ℕ) : ℕ := if proofDepth = 0 then 0 else 1

theorem formatProofSlot_lt (proofDepth : ℕ) : formatProofSlot proofDepth < 2 ^ proofDepth := by
  unfold formatProofSlot
  split
  · exact Nat.two_pow_pos _
  · rename_i h
    exact Nat.one_lt_two_pow h

/-- **The tail is the format's** at the proof file's slot, in its tree, and at slot 0, in a tree of one leaf. -/
theorem formatTail_proof (proofDepth : ℕ) :
    formatTail proofDepth (formatProofSlot proofDepth) (formatProofSlot proofDepth) =
      bytesToBits (_root_.Fmt.u64n (2 ^ proofDepth + formatProofSlot proofDepth)) :=
  if_pos rfl

theorem formatTail_zero (proofDepth : ℕ) :
    formatTail proofDepth (formatProofSlot proofDepth) 0 = bytesToBits (_root_.Fmt.u64n (2 ^ 0 + 0)) := by
  unfold formatTail formatProofSlot
  by_cases h : proofDepth = 0
  · subst h
    rfl
  · rw [if_neg h, if_neg (by omega)]

/-- **What stands behind a slot's value, in the format**: saltBytes bytes of free bits, then the tail. Slot 0 at the key's and the link's tree. -/
def formatRequestLeafSaltLayout (saltBytes proofDepth : ℕ) : RequestLeafSaltLayout :=
  ⟨8 * saltBytes, formatTail proofDepth (formatProofSlot proofDepth), 0, 0, formatProofSlot proofDepth,
    fun digest => bytesToBits (_root_.Run.digToBytes digest)⟩

/-- They fit a layout whose request tree has that depth. -/
theorem formatSlotSalts_fit {offlineRoundMarks : RoundSplits L.offline.shape} {linkRoundMarks : RoundSplits L.link.shape}
    (layout : HashLayout L offlineRoundMarks linkRoundMarks) (saltBytes : ℕ) :
    (formatRequestLeafSaltLayout saltBytes layout.queryLayout.depthReq).Fit layout :=
  ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, formatProofSlot_lt _, fun digest => by
    show (bytesToBits (_root_.Run.digToBytes digest)).length = 256
    rw [_root_.Run.length_bytesToBits, _root_.Run.size_digToBytes]⟩

section AtFlashProve
open VerifierAndGoals FlashProve
open IntegerTransformer (Settings)
variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
  (provers : HonestProvers (FlashProtocol files)) (limits : SearchLimits)
  {rounds : FormatRounds} {runsOffline : provers.offlineProver.Coin → FormatRuns}
  {runsOnline : provers.onlineProver.Coin → FormatRuns} {linkRuns : FormatRuns}
  {readOffline : Plains (FlashProtocol files).offline.shape → FormatRuns}
  {readOnline : Plains (FlashProtocol files).onlineBatch.loc.shape → FormatRuns}

/-- The format's slots at flashProveAtFiles. -/
abbrev flashProveRequestLeafSaltLayout (saltBytes : ℕ) : RequestLeafSaltLayout :=
  formatRequestLeafSaltLayout saltBytes (flashProveDescription.input files allZeroDigest []).queryLayout.depthReq

/-- **THE FORMAT'S SETTINGS MEET SettingsFit AND RunValuesAreSent AT flashProveAtFiles**, at public files in use, at every reading, for provers that
send their run values and whose coins fix 32 bytes each. -/
theorem formatSettings_meet (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (hO : ∀ κ, (runsOffline κ).1.size = 32 ∧ (runsOffline κ).2.size = 32)
    (hB : ∀ κ, (runsOnline κ).1.size = 32 ∧ (runsOnline κ).2.size = 32)
    (hL : linkRuns.1.size = 32 ∧ linkRuns.2.size = 32) (saltBytes : ℕ) (inRange : (flashProveDescription.C files).I → Prop)
    (hS : SendsItsRunValues provers (formatStarts provers rounds runsOffline runsOnline linkRuns readOffline readOnline)
      inRange) (reading : FlashReading files) :
    SettingsFit (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers
          (formatStarts provers rounds runsOffline runsOnline linkRuns readOffline readOnline) limits
          (flashProveRequestLeafSaltLayout files saltBytes) reading) ∧
      RunValuesAreSent (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers
          (formatStarts provers rounds runsOffline runsOnline linkRuns readOffline readOnline) limits
          (flashProveRequestLeafSaltLayout files saltBytes) reading) inRange :=
  ⟨theSettings_fit files settings fallbackInstance provers limits (flashProveRequestLeafSaltLayout files saltBytes) scope live _
      (formatStarts_lengthsFit hO hB hL) reading
      (formatSlotSalts_fit (flashLayout files settings fallbackInstance reading) saltBytes),
    runValuesAreSent_formatStarts _ _ _ _ _ _ _ _ _ hS⟩

end AtFlashProve

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.formatSettings_meet
#print axioms VerifiableInference.Compilation.SendsItsRunValues.refuse
#print axioms VerifiableInference.Compilation.formatSlotSalts_fit
#print axioms VerifiableInference.Compilation.formatStarts
#print axioms VerifiableInference.Compilation.formatStarts_lengthsFit
#print axioms VerifiableInference.Compilation.runValuesAreSent_formatStarts
#print axioms VerifiableInference.Compilation.formatProofSlot_lt
#print axioms VerifiableInference.Compilation.formatTail_proof
#print axioms VerifiableInference.Compilation.formatTail_zero
