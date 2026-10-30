-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/LinkLaidEightTold.lean

Summary. linkLaidEight (E2E/LinkLaidAllAtOnce.lean) is stated at homeR b Z, the parameters with an
all-zero digest of the public files and an empty second public reading. linkLaidEight_told proves
the same nine clauses (EightAt) at (homeT b Z).at d, the parameters at an arbitrary fixed value d of
the two public readings (E2E/LinkLaidTold.lean), for the same provers, simulators and numbers.
LinkLaidEight b Z is the case d := (allZeroDigest, []) (eightAt_zeros; eight_again).

Limits.
- All limits of E2E/LinkLaidTold.lean and of E2E/LinkLaidAllAtOnce.lean hold. The main one: d is
  fixed before the oracles are drawn, whereas VerifierAndGoals.verify takes it from the hash function.

Terms: E2E/HidingTerms.lean and E2E/LinkLaidTold.lean.

How it is proved. As in E2E/LinkLaidTold.lean: section 1 is stated for arbitrary parameters r and an
arbitrary told record T over them; the later sections only apply it.

Helper lemmas without a docstring. All other definitions and lemmas have docstrings.
  readsSome_at, readsLink_at: two more statements on the parameters read neither seedQueries nor answerCode, so they
    hold at T.at d where they hold at r.
-/
import E2E.LinkLaidTold
import E2E.LinkLaidAllAtOnce

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.LinkLaid.Told
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.Shown
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput LayoutsByPublicReading)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (flashProveData protocolDataWellFormed homeR homeT allZeroDigest)

/-! ## 1. For an arbitrary told record -/

section Letters
variable {r : InnerCompilerInput} (T : LayoutsByPublicReading r) (d : T.D)

theorem readsSome_at (h : ReadsSome r) : ReadsSome (T.at d) := ⟨h.T, h.B⟩

theorem readsLink_at (h : ReadsLink r) : ReadsLink (T.at d) := h

variable {a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits} {Sm : Sims r.protocol} {c : CoinNums r.LeafBody} {N : NumsW}
  {R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit} {i₀ : r.Index} {s1 : ℕ}

/-- eightAt_of (E2E/LinkLaidAllAtOnce.lean) at the parameters at d. -/
theorem eightAt_at (hE : EndAt (T.at d) a Sm c N R i₀ s1 (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0)
    (h1 : 1 ≤ s1) (ht : Tries r) (hL : LawFit r.queryLayout (T.Sd d) a.side.capT a.side.capL a.side.capB)
    (hW : WiresFit r.queryLayout (T.cA d)) (hs : NeverStops a.side.st) (hRS : ReadsSome r)
    (hRL : ReadsLink r) (hx : Nonempty r.Instance) (hp : PathsFit r.queryLayout a.side)
    (hSm : ∀ n y ρ ans, none ∉ (Sm.B n y ρ ans).support) (c1 : ∀ i, 2 ^ 40 ≤ a.side.capT i + 1)
    (c2 : ∀ i, 2 ^ 40 ≤ a.side.capL i + 1) (c3 : ∀ i, 2 ^ 40 ≤ a.side.capB i + 1) :
    EightAt (T.at d) a Sm c N R i₀ s1 :=
  eightAt_of (T.at d) hE h1 (tries_at T d ht) hL hW hs (readsSome_at T d hRS)
    (readsLink_at T d hRL) hx hp hSm c1 c2 c3

/-- Where T.Sd d and T.cA d are r's own, EightAt at the parameters at d is EightAt at r. -/
theorem eightAt_home (hS : T.Sd d = r.seedQueries) (hc : T.cA d = r.answerCode) :
    EightAt (T.at d) a Sm c N R i₀ s1 ↔ EightAt r a Sm c N R i₀ s1 := by
  have key : ∀ (S : OutOfDomainSampleQueryLayout 256 r.queryLayout.K r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (cA' : r.protocol.OutOfDomainAnswer → List (Dig 256)),
      S = r.seedQueries → cA' = r.answerCode →
      (EightAt { r with seedQueries := S, answerCode := cA' } a Sm c N R i₀ s1 ↔ EightAt r a Sm c N R i₀ s1) := by
    rintro _ _ rfl rfl
    exact Iff.rfl
  exact key _ _ hS hc

end Letters

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows _root_.Run.digToBytes

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-! ## 2. The nine clauses -/

set_option maxHeartbeats 1600000 in
/-- **For public files Z in scope with a live description and every d**: EightAt at the parameters
at d, for laid40. -/
theorem linkLaidEight_told (d : (homeT b Z).D) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (b₀ : (homeR b Z).LeafBody) (s1 ℓr : ℕ)
    (E : BitsE b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40))
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index)
    (hE : E.OK) (h1 : 1 ≤ s1) (h2 : s1 ≤ 688127) (hR : ∀ i x w, R.yes i x w → Ryes i x) :
    EightAt ((homeT b Z).at d) (laid40 b Z b₀ ℓr E) (fitSims (fixedSims (homeR b Z).protocol))
      (coinNums (homeR b Z) b₀ 320 ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) R i₀ s1 :=
  have h576 : 320 ≤ (homeR b Z).compilerParameters.sMT := by rw [sMT_home b Z scope live]; norm_num
  eightAt_at (homeT b Z) d
    (linkLaidWithBound_told b Z d b₀ 0 s1 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
      (fun _ => 2 ^ 40) E scope (2 ^ 40) (2 ^ 40) (2 ^ 40) Ryes R i₀ hE (by norm_num) h2
      (by norm_num) h576 (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) hR)
    h1 (tries_home b Z scope) (FlashProve.lawFit_home b Z d _ _ _)
    (FlashProve.wiresFit_home b Z d)
    (neverStops_laid b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E)
    (readsSome_home b Z scope live) (readsLink_home b Z) (instance_home b Z)
    (pathsFit_of_prem (premW_laid_told b Z d b₀ 0 s1 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
      (fun _ => 2 ^ 40) E scope (by norm_num) h2 h576 hE Ryes))
    (fun _ _ _ _ hm => by cases (PMF.mem_support_pure_iff _ _).1 hm)
    (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _)

/-! ## 3. LinkLaidEight b Z is the case of the all-zero digest and the empty second reading -/

/-- EightAt at the parameters at (allZeroDigest, []) is EightAt at homeR b Z. -/
theorem eightAt_zeros
    (a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (Sm : Sims (homeR b Z).protocol) (cn : CoinNums (homeR b Z).LeafBody) (N : NumsW)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index) (s1 : ℕ) :
    EightAt ((homeT b Z).at (allZeroDigest, [])) a Sm cn N R i₀ s1 ↔
      EightAt (homeR b Z) a Sm cn N R i₀ s1 :=
  eightAt_home (homeT b Z) (allZeroDigest, []) (seed_zeros b Z) (code_told b Z _)

/-- linkLaidEight (E2E/LinkLaidAllAtOnce.lean), from linkLaidEight_told at (allZeroDigest, []). -/
theorem eight_again (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    LinkLaidEight b Z :=
  fun b₀ s1 ℓr E Ryes R i₀ hE h1 h2 hR =>
    (eightAt_zeros b Z _ _ _ _ R i₀ s1).1
      (linkLaidEight_told b Z (allZeroDigest, []) scope live b₀ s1 ℓr E Ryes R i₀ hE h1 h2 hR)

end AtPublicFiles.LinkLaid.Told

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.Told.readsSome_at
#print axioms AtPublicFiles.LinkLaid.Told.readsLink_at
#print axioms AtPublicFiles.LinkLaid.Told.eightAt_at
#print axioms AtPublicFiles.LinkLaid.Told.eightAt_home
#print axioms AtPublicFiles.LinkLaid.Told.linkLaidEight_told
#print axioms AtPublicFiles.LinkLaid.Told.eightAt_zeros
#print axioms AtPublicFiles.LinkLaid.Told.eight_again
