-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Face/ByteSettings.lean: the byte-facing fields of the compiler's honest settings at
flashProveAtFiles, at the names of Johnson/CompletenessAndZeroKnowledge/TheSettings.lean and Johnson/CompletenessAndZeroKnowledge/FormatStarts.lean, and SideBytes
(Johnson/Face/BytesOfSide.lean) of them at every value of the public reading.

 1. shapes_the: the key's binding tree is ⟨0, 40⟩, the proof file's ⟨6, 40⟩, a salt has 40 bytes.
 2. flashRounds, flashStartsOfBytes: formatStarts at the rounds at which the chains change, with the
    readers of the plain parts. The link's two run values are one fixed pair; the link's entry has no
    test on them.
 3. sideBytes_at_theSettings: SideBytes of theSettings at these starts, at flashProveRequestLeafSaltLayout files 40.
 4. undoOn_at_theSettings: undoOn_compile at these settings.
 5. sendsItsRunValues_of_print: from StratsPrint to SendsItsRunValues.

Not shown here: StratLaw of any prover at these run values.
-/
import Johnson.Face.UndoAtCompile
import Johnson.Face.SideBytesOf
import Johnson.CompletenessAndZeroKnowledge.FormatStarts
import Johnson.Goal.Conditions.NumberAtHome

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles OnBytes.WholeKey OnBytes.FrontRoad OnBytes.Prover
open VerifiableInference.OnPublicFiles.SlotsBehindCutD OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes.Prover.Print
open VerifierAndGoals FlashProve FlashProve
open _root_.Run
open LPFD.Full (sBG sTG saltG)
open PV.EntryFive (dsF)
open Johnson.Prover.Print Johnson.Face
open IntegerTransformer (Settings)

/-- The letters of the public files. -/
abbrev flashS (files : PublicFiles) : DescriptionDataAtFiles (asDescriptionFiles files) := dataAtFiles flashProveData files

/-- **The three shapes at files in use.** -/
theorem shapes_the (files : PublicFiles) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    sTG (flashS files).G = ⟨0, 40⟩ ∧ sBG (flashS files).G = ⟨6, 40⟩ ∧
      saltG (flashS files).G = 40 := by
  rw [show (flashS files).G = thePlan (asDescriptionFiles files) from g_built_live files live]
  obtain ⟨X₀, m, hX, _, hG, hc, hb⟩ := thePlan_key files live
  have hf := (H2K.Sizes.publicO_at_scope scope hX).frame
  rw [hG]
  exact ⟨OnBytes.Model.Verify.chainsOf_key_binding hc hf VerifiableInference.Desc.theCfg_size
      (hb .keyOneTime),
    OnBytes.Model.Verify.chainsOf_proof_binding hc hf VerifiableInference.Desc.theCfg_size
      (hb .proofFirst),
    OnBytes.Model.Verify.chainsOf_key_salt_at hc hf⟩

/-- What the plain parts of a whole file's rounds say of its two later chains' run values. -/
def readRunsT {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (pl : Plains (GT S).sh) :
    ByteArray × ByteArray :=
  ((Plains.fst (s := (GT S).c₂) (t := (GT S).c₃)
      (Plains.snd (s := (GT S).c₁) (t := (GT S).c₂ ++ (GT S).c₃) pl)).1.run,
    (Plains.snd (s := (GT S).c₂) (t := (GT S).c₃)
      (Plains.snd (s := (GT S).c₁) (t := (GT S).c₂ ++ (GT S).c₃) pl)).1)

/-- The same of the proof file. -/
def readRunsB {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (pl : Plains (GB S).sh) :
    ByteArray × ByteArray :=
  ((Plains.fst (s := (GB S).c₂) (t := (GB S).c₃)
      (Plains.snd (s := (GB S).c₁) (t := (GB S).c₂ ++ (GB S).c₃) pl)).1.run,
    (Plains.snd (s := (GB S).c₂) (t := (GB S).c₃)
      (Plains.snd (s := (GB S).c₁) (t := (GB S).c₂ ++ (GB S).c₃) pl)).1)

/-- **The readers read what the joining round and the third chain's round send.** -/
theorem readRunsT_of_law {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (σ : Strat (GT S).sh Unit)
    (r2 r3 : ByteArray)
    (l : StratLaw (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty
      σ r2 r3) (ρ : Rho (GT S).sh) : readRunsT S (σ.run ρ).1.plains = (r2, r3) := by
  have h₂ : (Plains.fst (s := (GT S).c₂) (t := (GT S).c₃)
      (Plains.snd (s := (GT S).c₁) (t := (GT S).c₂ ++ (GT S).c₃) (σ.run ρ).1.plains)).1 =
      ((GT S).msgJ (σ.run ρ).1).2 := by
    show (Plains.snd (s := (GT S).s₁) (Tr.plains (σ.run ρ).1.2.2)).1 = _
    rw [← Tr.plains_snd]
    rfl
  have h₃ : (Plains.snd (s := (GT S).c₂) (t := (GT S).c₃)
      (Plains.snd (s := (GT S).c₁) (t := (GT S).c₂ ++ (GT S).c₃) (σ.run ρ).1.plains)).1 =
      ((GT S).msg3 (σ.run ρ).1).2 := by
    show (Plains.snd (s := (GT S).s₂)
      (Plains.snd (s := (GT S).s₁) (Tr.plains (σ.run ρ).1.2.2)).2).1 = _
    rw [← Tr.plains_snd]
    show (Plains.snd (s := (GT S).s₂) (Tr.plains ((GT S).trJ (σ.run ρ).1).2.2)).1 = _
    rw [← Tr.plains_snd]
    rfl
  unfold readRunsT
  rw [h₂, h₃, l.run2 ρ, l.run3 ρ]

/-- The same of the proof file. -/
theorem readRunsB_of_law {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (σ : Strat (GB S).sh Unit)
    (r2 r3 : ByteArray)
    (l : StratLaw (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty
      σ r2 r3) (ρ : Rho (GB S).sh) : readRunsB S (σ.run ρ).1.plains = (r2, r3) := by
  have h₂ : (Plains.fst (s := (GB S).c₂) (t := (GB S).c₃)
      (Plains.snd (s := (GB S).c₁) (t := (GB S).c₂ ++ (GB S).c₃) (σ.run ρ).1.plains)).1 =
      ((GB S).msgJ (σ.run ρ).1).2 := by
    show (Plains.snd (s := (GB S).s₁) (Tr.plains (σ.run ρ).1.2.2)).1 = _
    rw [← Tr.plains_snd]
    rfl
  have h₃ : (Plains.snd (s := (GB S).c₂) (t := (GB S).c₃)
      (Plains.snd (s := (GB S).c₁) (t := (GB S).c₂ ++ (GB S).c₃) (σ.run ρ).1.plains)).1 =
      ((GB S).msg3 (σ.run ρ).1).2 := by
    show (Plains.snd (s := (GB S).s₂)
      (Plains.snd (s := (GB S).s₁) (Tr.plains (σ.run ρ).1.2.2)).2).1 = _
    rw [← Tr.plains_snd]
    show (Plains.snd (s := (GB S).s₂) (Tr.plains ((GB S).trJ (σ.run ρ).1).2.2)).1 = _
    rw [← Tr.plains_snd]
    rfl
  unfold readRunsB
  rw [h₂, h₃, l.run2 ρ, l.run3 ρ]

/-- The readers read of a string what the exception reads of it. -/
theorem readRunsT_string {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (π : OneProtocolProof 256 (QT S)) :
    readRunsT S π.plains =
      ((TypedOracleCompiler.Joined.pls₂ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀)
                (join₀ S.G.rec₀) ByteArray.empty silK S.runK) π).1.run,
       (TypedOracleCompiler.Joined.pls₃ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀)
                (join₀ S.G.rec₀) ByteArray.empty silK S.runK) π).1) := rfl

/-- A value of 32 bytes for the link's run, which has no later chain: the link's entry has no test on
it (Johnson/PV/EntryInOf.lean, laidOf). -/
def linkRun : ByteArray := ⟨Array.replicate 32 1⟩

theorem linkRun_size : linkRun.size = 32 := rfl

/-- **The public rounds at which the chains change.** -/
def flashRounds (files : PublicFiles) : FormatRounds :=
  ⟨(GT (flashS files)).nJ, (GT (flashS files)).n3, dsF.length + 1, (GB (flashS files)).nJ,
    (GB (flashS files)).n3⟩

/-- **The format's salt starts at flashProveAtFiles**, for any provers and run values. -/
abbrev flashStartsOfBytes (files : PublicFiles) (provers : HonestProvers (FlashProtocol files))
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray) : SaltStarts provers :=
  formatStarts provers (flashRounds files) runsT runsB (linkRun, linkRun)
    (readRunsT (flashS files)) (readRunsB (flashS files))

/-- **The three search limits**: 2 ^ (work + 6) - 1 each. -/
def byteLimits (files : PublicFiles) : SearchLimits :=
  ⟨capT (flashS files), capL, capB (flashS files)⟩

/-- **The format's start is the run value of the round.** -/
theorem formatStart_bytes (joinRound thirdRound : ℕ) (runs : FormatRuns) (round : ℕ) (s : Bits)
    (hs : s.length = 256) :
    formatStart joinRound thirdRound runs round s =
      bytesToBits (if round < joinRound then bitsToBytes s
        else if round < thirdRound then runs.1 else runs.2) := by
  unfold formatStart
  split
  · exact (bytesToBits_bitsToBytes s (whole_of_len (n := 32) hs)).symm
  · split <;> rfl

section Layout
variable {Index Instance : Type} {L : HolographicProtocol Index Instance} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The table's salts that honestSide draws, at a start of bytes and a whole number of free bytes. -/
theorem salts_pre (cB : ByteArray) (saltB m ℓ : ℕ) (hℓ : ℓ = 8 * saltB)
    (E : Enum (Fin m → Fin ℓ → Bool)) (b : Fin (E.n + 1)) (j : ℕ) (hj : j < m) :
    ∃ o : ByteArray, o.size = saltB ∧
      (saltsPre (bytesToBits cB) m ℓ E).e b j = leafSalt cB o := by
  have hl : (List.ofFn (E.e b ⟨j, hj⟩)).length = 8 * saltB := by
    rw [List.length_ofFn]
    exact hℓ
  refine ⟨bitsToBytes (List.ofFn (E.e b ⟨j, hj⟩)), size_bitsToBytes _ _ hl, ?_⟩
  show (if h : j < m then bytesToBits cB ++ List.ofFn (E.e b ⟨j, h⟩) else []) = _
  rw [dif_pos hj]
  show _ = bytesToBits cB ++ bytesToBits (bitsToBytes _)
  rw [bytesToBits_bitsToBytes _ (whole_of_len hl)]

end Layout

/- Lean compares these by their names (as in Johnson/Goal/Description/AtBound.lean). -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

set_option maxRecDepth 100000 in
/-- **SideBytes of these settings**, at every value of the public reading. -/
theorem sideBytes_at_theSettings (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray) (limits : SearchLimits)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (sizeT : ∀ κ, (runsT κ).1.size = 32 ∧ (runsT κ).2.size = 32)
    (sizeB : ∀ κ, (runsB κ).1.size = 32 ∧ (runsB κ).2.size = 32)
    (limT : ∀ j, limits.offline j < 2 ^ 64) (limL : ∀ j, limits.link j < 2 ^ 64)
    (limB : ∀ j, limits.online j < 2 ^ 64) (reading : FlashReading files) :
    SideBytes (flashS files) allZeroDigest []
      (honestSide (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers (flashStartsOfBytes files provers
          runsT runsB)
          limits (flashProveRequestLeafSaltLayout files 40) reading)).side
      (digToBytes reading.1) ⟨0, 40⟩ runsT runsB := by
  obtain ⟨eK, eP, eG⟩ := shapes_the files scope live
  have e8 : 8 * saltG (flashS files).G = 320 := by rw [eG]
  have h32 : (digToBytes reading.1).size = 32 :=
    size_bitsToBytes _ 32 (by rw [List.length_ofFn])
  refine sideBytes_of (flashS files) allZeroDigest []
    (honestSide (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers (flashStartsOfBytes files provers runsT
        runsB)
        limits (flashProveRequestLeafSaltLayout files 40) reading)).side (digToBytes reading.1) ⟨0, 40⟩ runsT runsB
    (fun _ => (linkRun, linkRun)) h32 rfl ?_ (8 * 40) (8 * 40) (8 * 40)
    (flashLayout files settings fallbackInstance reading).queryLayout.depthReqT
    (flashLayout files settings fallbackInstance reading).queryLayout.depthReqL
    (flashLayout files settings fallbackInstance reading).queryLayout.depthReq 0 0
    (formatProofSlot (flashProveDescription.input files allZeroDigest []).queryLayout.depthReq)
    (theLeafFiller files) (theLeafFiller files) (theLeafFiller files) ?_ ?_ ?_ ?_ ?_ ?_ limT limL
    limB (fun _ _ => Nat.two_pow_pos 64)
  · intro b j hj
    exact salts_pre (digToBytes reading.1) (saltG (flashS files).G) _ 320 e8.symm _ b j hj
  · intro a
    rw [e8]
    exact preCoins_coinsPre _ _ rfl _ a
  · intro a
    rw [e8]
    exact preCoins_coinsPre _ _ rfl _ a
  · intro a
    rw [e8]
    exact preCoins_coinsPre _ _ rfl _ a
  · intro κ
    refine ⟨fun i _ s hs => formatStart_bytes _ _ _ i s hs, ?_, ?_, ?_, ?_, rfl, (sizeT κ).1,
      (sizeT κ).2⟩
    · rw [e8]
      exact List.length_replicate ..
    · rw [eK]
    · rw [eK]
      exact formatTail_zero _
    · rw [eK]
      decide
  · intro κ
    refine ⟨fun i _ s hs => formatStart_bytes _ _ _ i s hs, ?_, rfl, formatTail_zero _, by decide,
      rfl, linkRun_size, linkRun_size⟩
    rw [e8]
    exact List.length_replicate ..
  · intro κ
    refine ⟨fun i _ s hs => formatStart_bytes _ _ _ i s hs, ?_, ?_, formatTail_proof _,
      formatProofSlot_lt _, rfl, (sizeB κ).1, (sizeB κ).2⟩
    · rw [e8]
      exact List.length_replicate ..
    · rw [eP]

/-- **The honest part of flashProveAtFiles at these settings**, at any provers and run values: the form at
which Johnson/CompletenessAndZeroKnowledge/ParserGeneric.lean reads the strategies. -/
abbrev flashHonestPart (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
    (provers : HonestProvers (FlashProtocol files))
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray) (limits : SearchLimits) :
    HonestProversAndSettingsAtFiles files settings :=
  theHonestPartOf files settings fallbackInstance provers (flashStartsOfBytes files provers runsT
    runsB)
    limits (flashProveRequestLeafSaltLayout files 40)

set_option maxRecDepth 100000 in
/-- **THE PARSER UNDOES THE WRITER ON WHAT compile's HONEST SIDE MAKES AT THESE SETTINGS**, outside
the exception. Of the premises of undoOn_compile, SideBytes goes; what stands is the prover's
StratsPrint, and on the letters: run values of 32 bytes, limits below 2 ^ 64. -/
theorem undoOn_at_theSettings (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray) (limits : SearchLimits)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (sizeT : ∀ κ, (runsT κ).1.size = 32 ∧ (runsT κ).2.size = 32)
    (sizeB : ∀ κ, (runsB κ).1.size = 32 ∧ (runsB κ).2.size = 32)
    (limT : ∀ j, limits.offline j < 2 ^ 64) (limL : ∀ j, limits.link j < 2 ^ 64)
    (limB : ∀ j, limits.online j < 2 ^ 64)
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (ok : (flashProveDescription.input files allZeroDigest []).Index → Prop) (hok : ∀ i x, Tr i x → ok i)
    (hP : ∀ d, StratsPrint (flashS files) allZeroDigest []
      (sideAt files settings (flashHonestPart files settings fallbackInstance provers runsT runsB
        limits) d) runsT runsB ok Tr) :
    UndoOnBut flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      (sideAt files settings (flashHonestPart files settings fallbackInstance provers runsT runsB
        limits))
      (backThe files settings) Tr (flashProveDescription.parse files) (bytesWriter files)
      (ZeroRun (flashS files) allZeroDigest []) :=
  undoOn_compile files settings _ scope live Tr (fun _ => ⟨0, 40⟩) (fun _ => runsT)
    (fun _ => runsB)
    (fun d => sideBytes_at_theSettings files settings fallbackInstance provers runsT runsB limits
      scope live sizeT sizeB limT limL limB d)
    ok hok hP

set_option maxRecDepth 100000 in
/-- **The prover's law gives what SendsItsRunValues asks of the run values**, at the key file at every
index of ok, at the proof file where what is not withheld lies in Tr: so under refuseUnserved. -/
theorem sendsItsRunValues_of_print (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray) (limits : SearchLimits)
    (reading : FlashReading files)
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (ok : (flashProveDescription.input files allZeroDigest []).Index → Prop)
    (hP : StratsPrint (flashS files) allZeroDigest []
      (honestSide (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers (flashStartsOfBytes files provers
          runsT runsB)
          limits (flashProveRequestLeafSaltLayout files 40) reading)).side runsT runsB ok Tr)
    (hW : ∀ i r e n x ρ, ok i →
      ρ ∉ provers.onlineProver.withheld (i, r, e, n) (x, (FlashProtocol files).recOf i r e) →
      Tr i x) :
    SendsItsRunValues provers (flashStartsOfBytes files provers runsT runsB) ok where
  offline := fun i r e κ ρ hi _ =>
    readRunsT_of_law (flashS files) _ _ _ (hP.T i r e κ hi) ρ
  online := fun i r e n x κ ρ hi hρ =>
    readRunsB_of_law (flashS files) _ _ _ (hP.B i r e x n κ (hW i r e n x ρ hi hρ)) ρ

/-- **Off the withheld set of provers that refuse, the request is served.** -/
theorem notWithheld_served {Index Instance : Type} {L : HolographicProtocol Index Instance}
    (provers : HonestProvers L) (Served : Index → Instance → Prop)
    (w : _) (y : _) (ρ : _)
    (h : ρ ∉ (provers.refuseUnserved Served).onlineProver.withheld w y) : Served w.1 y.1 := by
  by_contra hs
  exact h (Or.inr (Or.inl hs))

set_option maxRecDepth 100000 in
/-- **At provers that refuse where the request is not served**, StratsPrint gives what SendsItsRunValues
asks of the run values: the law is asked at Tr alone. -/
theorem sendsItsRunValues_refuse (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (runsT : (provers.refuseUnserved Tr).offlineProver.Coin → ByteArray × ByteArray)
    (runsB : (provers.refuseUnserved Tr).onlineProver.Coin → ByteArray × ByteArray)
    (limits : SearchLimits) (reading : FlashReading files)
    (ok : (flashProveDescription.input files allZeroDigest []).Index → Prop)
    (hP : StratsPrint (flashS files) allZeroDigest []
      (honestSide (flashLayout files settings fallbackInstance reading) (provers.refuseUnserved Tr)
        (theSettings files settings fallbackInstance (provers.refuseUnserved Tr)
          (flashStartsOfBytes files (provers.refuseUnserved Tr) runsT runsB) limits
          (flashProveRequestLeafSaltLayout files 40) reading)).side runsT runsB ok Tr) :
    SendsItsRunValues (provers.refuseUnserved Tr)
      (flashStartsOfBytes files (provers.refuseUnserved Tr) runsT runsB) ok :=
  sendsItsRunValues_of_print files settings fallbackInstance _ runsT runsB limits reading Tr ok hP
    fun _ _ _ _ _ _ _ hρ => notWithheld_served provers Tr _ _ _ hρ

/-- **These limits are below 2 ^ 64**, at files in use. -/
theorem byteLimits_lt (files : PublicFiles) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    (∀ j, (byteLimits files).offline j < 2 ^ 64) ∧ (∀ j, (byteLimits files).link j < 2 ^ 64) ∧
      ∀ j, (byteLimits files).online j < 2 ^ 64 :=
  caps_home files scope live

set_option maxRecDepth 100000 in
/-- **undoOn_at_theSettings at these limits.** -/
theorem undoOn_at_byteLimits (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (sizeT : ∀ κ, (runsT κ).1.size = 32 ∧ (runsT κ).2.size = 32)
    (sizeB : ∀ κ, (runsB κ).1.size = 32 ∧ (runsB κ).2.size = 32)
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (ok : (flashProveDescription.input files allZeroDigest []).Index → Prop) (hok : ∀ i x, Tr i x → ok i)
    (hP : ∀ d, StratsPrint (flashS files) allZeroDigest []
      (sideAt files settings (flashHonestPart files settings fallbackInstance provers runsT runsB
        (byteLimits files)) d) runsT runsB ok Tr) :
    UndoOnBut flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
      (sideAt files settings (flashHonestPart files settings fallbackInstance provers runsT runsB
        (byteLimits files)))
      (backThe files settings) Tr (flashProveDescription.parse files) (bytesWriter files)
      (ZeroRun (flashS files) allZeroDigest []) :=
  undoOn_at_theSettings files settings fallbackInstance provers runsT runsB (byteLimits files) scope
    live sizeT sizeB (byteLimits_lt files scope live).1 (byteLimits_lt files scope live).2.1
    (byteLimits_lt files scope live).2.2 Tr ok hok hP

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.undoOn_at_byteLimits
#print axioms VerifiableInference.Compilation.sendsItsRunValues_refuse
#print axioms VerifiableInference.Compilation.undoOn_at_theSettings
#print axioms VerifiableInference.Compilation.sendsItsRunValues_of_print
#print axioms VerifiableInference.Compilation.byteLimits_lt
#print axioms VerifiableInference.Compilation.shapes_the
#print axioms VerifiableInference.Compilation.salts_pre
#print axioms VerifiableInference.Compilation.sideBytes_at_theSettings
