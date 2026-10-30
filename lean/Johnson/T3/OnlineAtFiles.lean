-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OnlineAtFiles.lean: from the rule on the rows (Owed) to the online clause of the zero-knowledge statement (ZeroKnowledgeOnServedRequests) at public files Z.

1.  The online clause, at a copy's number n: the online prover's output and the simulator's are equal at every challenge outside the
    private stops, and its private stops have a stated measure (ExactOutsideStops, PrivateStopsAtMost).
2.  Nothing here proves zero knowledge of the protocol. The theorems below take Owed, the rows' rule, and the private stops'
    measure as premises: no value of them is given here, and the prover is the family famG at arguments B, G, H.
-/
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws
import E2E.BridgeExact
import E2E.BridgeNonZero

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed
open Compile.Lifetime (SimOf)

/-! ## 1 The library's form of the clause is the statement's, for any protocol -/

section General
variable {I X : Type} {L : HolographicProtocol I X}

/-- **The library's «exact outside Hid» is the statement's clause**, at every map clear of messages. -/
theorem exactOutsideStops_of_oneExact (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
    (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
    (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed))
    {sim : SimB L} {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {inRange : I → Prop}
    {Served : I → X → Prop}
    (exact : OneExact Fm sim Tied) (tied : ValidTied Tied inRange (fun _ => True) Served)
    (clear : Rho L.onlineBatch.loc.shape → Rho L.onlineBatch.loc.shape) (n : ℕ) :
    ExactOutsideStops ((HonestProvers.ofThreeProvers (proversOf hT hL Fm)).onlineAtCopy n)
      (fun w y => inRange w.1 ∧ L.validB Served w y) clear (sim n) := by
  rintro ⟨i, r, e⟩ ⟨x, rc⟩ ⟨hi, hrc, hx⟩ ρ hρ
  obtain rfl : rc = L.recOf i r e := hrc
  exact exact n (i, r, e) (x, L.recOf i r e) (tied n i r e x hi trivial hx) (clear ρ) hρ

/-- **The statement's bound on the private stops from their measure at plain uniform messages**, where they do not read the map cleared. -/
theorem privateStopsAtMost_of_small (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
    (hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)))
    (Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed))
    {Tied : ℕ → I × L.EncodingRandomness × L.OutOfDomainSeed → X × L.Rec → Prop} {inRange : I → Prop}
    {Served : I → X → Prop} (work : WorkBits L.onlineBatch.loc.shape) {zHid : ℝ≥0∞}
    (blind : ∀ n w x ρ, work.cleared ρ ∈ (Fm.at n).Hid w x → ρ ∈ (Fm.at n).Hid w x)
    (hid : HidSmall Fm Tied zHid)
    (tied : ValidTied Tied inRange (fun _ => True) Served) (n : ℕ) :
    PrivateStopsAtMost ((HonestProvers.ofThreeProvers (proversOf hT hL Fm)).onlineAtCopy n)
      (fun w y => inRange w.1 ∧ L.validB Served w y) work zHid := by
  rintro ⟨i, r, e⟩ ⟨x, rc⟩ ⟨hi, hrc, hx⟩
  obtain rfl : rc = L.recOf i r e := hrc
  have hs : {ρ | work.cleared ρ ∈ (Fm.at n).Hid (i, r, e) (x, L.recOf i r e)} ⊆
      (Fm.at n).Hid (i, r, e) (x, L.recOf i r e) :=
    fun ρ h => blind n _ _ ρ h
  exact (pr_mono _ hs).trans (hid n _ _ (tied n i r e x hi trivial hx))

end General

/-! ## 2 At the public files -/

section AtFiles
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides Owed relAt honestBatchProverOfFile simOne)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne allZeroDigest)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) onlineAtFilesInstance1 : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) onlineAtFilesInstance2 {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- **The online simulator at Z**, for each copy's number: the library's simZ, read at the object's instances. It is made of the
description, the book, the rows' simulators, the committer's map from an instance to its key, and the public stops. -/
abbrev onlineSimulator (n : ℕ) : SimOf (protocolAtFiles Z).onlineBatch.loc := fun a ρ answers =>
  (simZ Z Zp Np cF run₂ run₃ B G H n (instanceAsPlainRecord a) ρ answers).map (Option.map (viewRe instanceAsPlainRecord _))

/-- **The online clause from Owed, at the served set alone.** Its premises on the request are those of Owed: the proof reads no
RyesZ. -/
theorem online_exact_of_owed_atServed (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (laid : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (owed : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord))
    (owns : G.owns = true)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    ExactOutsideStops
      ((HonestProvers.ofThreeProvers (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online.cleared (onlineSimulator Z Zp Np cF run₂ run₃ B G H n) := by
  have ex : ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))
      (simZ Z Zp Np cF run₂ run₃ B G H)
      (fun _ w x => ∃ x', ServedRequest committerCoinCountLessOne Z hr w.1 x' ∧
        x = instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) := by
    intro n w x hx ρ hρ
    obtain ⟨x', hx', rfl⟩ := hx
    exact ProofFile.Honest.one_exact_atItem_mute
      (tiedAt_along (AZ Z) PadZ (holdZ Z) Zp Np cF run₂ run₃ n (dataAtFiles flashProveData Z).DP)
      (AtPublicFiles.AtZero.itemsZero_of_data laid.data) owed owns
      (dataFits_atFiles Z Zp Np cF scope live laid) w (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)
      (by
        rw [ansAt_eq]
        exact valid_obj (Cf (AZ Z) PadZ (holdZ Z)) (filesAt Z) (dataAtFiles flashProveData Z).P
          (ServedRequest committerCoinCountLessOne Z hr) w (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2) ⟨rfl, hx'⟩)
      ρ (due_atFiles Z Zp Np cF scope live laid (nonZero_atFiles Z Zp Np cF scope laid) ρ) hρ
  have ex' : OneExact (famG Z Zp Np cF run₂ run₃ B G H)
      (onlineSimulator Z Zp Np cF run₂ run₃ B G H)
      (fun _ w a => ∃ x', ServedRequest committerCoinCountLessOne Z hr w.1 x' ∧
        instanceAsPlainRecord a = instanceAsPlainRecord (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)) :=
    ex.re instanceAsPlainRecord (protocolAtFiles Z).onlineBatch.loc.accept id
  exact exactOutsideStops_of_oneExact hT hL _ ex'
    (fun _ _ _ _ x _ _ hx => ⟨x, hx, rfl⟩) _ n

/-- **The online clause from Owed**, with the premise servedIsTrue that the proof through the library's TiedIn asks. -/
theorem online_exact_of_owed (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (laid : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (servedIsTrue : ∀ i x, ServedRequest committerCoinCountLessOne Z hr i x → RyesZ Z i x)
    (owed : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord))
    (owns : G.owns = true)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    ExactOutsideStops
      ((HonestProvers.ofThreeProvers (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online.cleared (onlineSimulator Z Zp Np cF run₂ run₃ B G H n) :=
  exactOutsideStops_of_oneExact hT hL _
    (show OneExact (famG Z Zp Np cF run₂ run₃ B G H)
        (onlineSimulator Z Zp Np cF run₂ run₃ B G H)
        (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H (ServedRequest committerCoinCountLessOne Z hr) rangeAtFiles
          (fun _ => True) n w (instanceAsPlainRecord a)) from
      (exactAt_of_owedAt Z Zp Np cF run₂ run₃ B G H scope live laid rangeAtFiles (fun _ => True)
        (ServedRequest committerCoinCountLessOne Z hr) (fun _ _ _ h => h) owed owns
        (nonZero_atFiles Z Zp Np cF scope laid)).re instanceAsPlainRecord (protocolAtFiles Z).onlineBatch.loc.accept id)
    (validIn Z Zp Np cF run₂ run₃ B G H servedIsTrue (AtPublicFiles.AtZero.itemsZero_of_data laid.data)
      rangeAtFiles fun _ => True)
    _ n

/-- **The statement's bound on the private stops, measured at the statement's own pairs.** hidZero_link: they do not read the work bits. -/
theorem online_stops_of_small_atValid {zHid : ℝ≥0∞} {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp)
    (hid : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a) zHid)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    PrivateStopsAtMost
      ((HonestProvers.ofThreeProvers (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online zHid :=
  privateStopsAtMost_of_small hT hL _ (workAtFiles Z).online
    (fun n w x ρ => (hidZero_link (lettersZ Z allZeroDigest []) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)
      n w x ρ).1)
    hid (fun _ _ _ _ _ hi _ hx => ⟨hi, rfl, hx⟩) n

/-- **The same, the private stops measured at TiedIn**, with the premise servedIsTrue that this proof asks. -/
theorem online_stops_of_small {zHid : ℝ≥0∞} {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (laid : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (servedIsTrue : ∀ i x, ServedRequest committerCoinCountLessOne Z hr i x → RyesZ Z i x)
    (hid : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H (ServedRequest committerCoinCountLessOne Z hr) rangeAtFiles
        (fun _ => True) n w (instanceAsPlainRecord a)) zHid)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    PrivateStopsAtMost
      ((HonestProvers.ofThreeProvers (proversOf hT hL (famG Z Zp Np cF run₂ run₃ B G H))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online zHid :=
  privateStopsAtMost_of_small hT hL _ (workAtFiles Z).online
    (fun n w x ρ => (hidZero_link (lettersZ Z allZeroDigest []) (descZ Zp Np cF) instanceAsPlainRecord silInst B G
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z)
      n w x ρ).1)
    hid
    (validIn Z Zp Np cF run₂ run₃ B G H servedIsTrue (AtPublicFiles.AtZero.itemsZero_of_data laid.data)
      rangeAtFiles fun _ => True)
    n

/-- **The statement at the protocol**, for the online prover famG at the arguments B, G, H and the link's explicit prover, whose error
is 0, from: the offline prover's two clauses and its table; the work bits; Owed and owns; the measure of the online private stops. That famG at
these arguments is the protocol's prover is not said here. -/
theorem zeroKnowledgeOnServedRequests_of_owed {zHid a : ℝ≥0∞}
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    (laid : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (owed : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord))
    (owns : G.owns = true)
    (hid : HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a) zHid)
    (faithful : (workAtFiles Z).Faithful) (two : TwoIndicesServeOneRequest Z hr)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (offlineSimulator : SimOf (protocolAtFiles Z).offline)
    (offlineTable : ∀ i r e, hT.ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r)
    (offline : ExactOutsideStops hT (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y)
      (workAtFiles Z).offline.cleared offlineSimulator)
    (offlineStops : PrivateStopsAtMost hT (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y)
      (workAtFiles Z).offline a) :
    ZeroKnowledgeOnServedRequests Z hr
      (HonestProvers.ofThreeProvers (proversOf hT (linkProverAtFiles committerCoinCountLessOne Z) (famG Z Zp Np cF run₂ run₃ B G H))) a 0
      zHid :=
  zeroKnowledgeOnServedRequests_of_runs_link scope
    ⟨offlineSimulator, OnBytes.LinkSim.AtHome.homeSim Z,
      onlineSimulator Z Zp Np cF run₂ run₃ B G H⟩ rfl rfl faithful two
    ⟨offlineTable, fun _ _ _ _ _ => rfl,
      fun i r e n => extIsEnc_famG Z Zp Np cF run₂ run₃ B G H n i r e⟩
    offline
    (fun n => online_exact_of_owed_atServed Z Zp Np cF run₂ run₃ B G H scope live hr laid owed owns
      hT (linkProverAtFiles committerCoinCountLessOne Z) n)
    offlineStops
    (fun n => online_stops_of_small_atValid Z Zp Np cF run₂ run₃ B G H hr hid hT
      (linkProverAtFiles committerCoinCountLessOne Z) n)

end AtFiles

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.exactOutsideStops_of_oneExact
#print axioms VerifiableInference.Compilation.privateStopsAtMost_of_small
#print axioms VerifiableInference.Compilation.onlineSimulator
#print axioms VerifiableInference.Compilation.online_exact_of_owed_atServed
#print axioms VerifiableInference.Compilation.online_exact_of_owed
#print axioms VerifiableInference.Compilation.online_stops_of_small_atValid
#print axioms VerifiableInference.Compilation.online_stops_of_small
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_of_owed
