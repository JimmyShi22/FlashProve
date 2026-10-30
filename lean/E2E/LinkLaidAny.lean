-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/LinkLaidAny.lean

Summary. The statements of E2E/LinkLaidTold.lean and E2E/LinkLaidEightTold.lean, once, for arbitrary
parameters a₀ of an honest side at homeR b Z into which the explicit link prover is substituted:
withLaidLink b Z a₀ cn v₀ E (Johnson/LinkSim/AtHome/CompileLaid.lean). Each statement with a d holds
at every fixed value d of the two public readings. Then two members, that is, parameters for which
PremW is shown: laidAt (E2E/LinkLaidPrivacy.lean), and a second member, laidAtN, with two
placeholder provers, over the placeholders' parameters with a window of constants and a filler of ℓ
zeros (silentAtN, E2E/FiveLeftSilentWindows.lean).

What is asked of a₀. hP is PremW for a₀ at homeR b Z's own data. The five statements whose
conclusion holds PremW or the conclusion of wholeKeyPrivacy ask hP: premW_any_home, premW_any_told,
endAt_any_told, atOnce_any_told, eight_any_told. The others do not. Four ask that a₀'s provers never
abort (NeverStops): neverStops_any, strings_any_told, atOnce_any_told, eight_any_told.

hP is shown in this file at two members alone, each with two placeholders (of PremW elsewhere:
lean/GAPS.md, 75). "For an arbitrary a₀" is a conditional, not more provers.

For arbitrary a₀, Sm₀, cn, N₀, v₀, E.
  premW_any_home, premW_any_told   PremW with the link prover substituted: at homeR b Z's own data
      (this is premW_withLaid, Johnson/LinkSim/AtHome/CompileFit.lean), and at every d.
  zeta_any, zeta_any_told   the bound boundZ (9 + CT + CL + CB) M t n on the error, for n ≤ s1.
  endAt_any_told   EndAt at (homeT b Z).at d.
  neverStops_any   the link prover never aborts; the other two provers are a₀'s.
  strings_any_told   with at least 2 ^ 40 tries in every search the proofs are produced, except
      with probability at most (a₀.M + 2) · 71 · 2 ^ -256.
  atOnce_any_told, eight_any_told   AtOnceAt and EightAt at (homeT b Z).at d.
  sideFit_any   SideFit (Johnson/WholeKey/Complete.lean) passes from a₀ to the substituted
      parameters, where a₀'s filler has cn.ℓ bits.
For arbitrary parameters, and at homeT b Z.
  honFit_cfg, honFit_told_of_home   HonFit (Johnson/Prover/All/OfHonest.lean), a premise of
      completeness, does not read the field cfg; so HonFit at homeR b Z's own data gives HonFit at
      the data at every d. HonFit is shown for no provers, here or in what this file imports.
Two numbers at homeR b Z, for all public files Z.
  sFS_home, depthReqL_home   compilerParameters.sFS = 256 and queryLayout.depthReqL = 0. bitsEN_eq: so the type BitsEN does not
      depend on b or Z.
The first member.
  laidAt_is   laidAt is withLaidLink over fixedAt. premW_fixed_home: hP for it.
  premW_laid_told_any   premW_laid_told (E2E/LinkLaidTold.lean), proved anew from premW_any_told.
The second member, with two placeholder provers: fixedAtN, BitsEN, laidAtN. It is another scheme
than laidAt's: other ranges of coins, another type for E. No statement about laidAt says anything of
it, nor the other way round. Its window, the constants 2 ^ 20, 2 ^ 39, 2 ^ 39, is not stated to be
the written window of E2E/FiveLeftSilentWindows.lean, which is the least.
  premW_fixedN_home   hP for it.
  premW_laidN_told, zeta_laidN_told, strings_laidN_told, atOnce_laidN_told, eight_laidN_told.
  sideFit_laidN   SideFit holds for it. For laidAt it fails, for 1 ≤ ℓ ≤ sMT (not_sideFit_laid).

Limits.
- All limits of E2E/LinkLaidTold.lean, E2E/LinkLaidToldAsks.lean, E2E/LinkLaidEightTold.lean and
  E2E/FiveLeftSilentWindows.lean hold. Among them: d is fixed before the oracles are drawn; PremW
  and zetaW do not read cfg, the one field that depends on d.
- Nothing on hiding is new here. At both members two of the three provers are placeholders.
- At both members the tables' leaf salts begin with sMT - ℓ zeros at every d. The library's own
  prover program over homeT b Z (pfOf, Johnson/Goal/Conditions/HomeAtWider.lean) starts them with
  the bytes of the digest that was read (saltsAt, Johnson/Goal/Conditions/WiderSalts.lean).
- Completeness is not proved of anything here. sideFit_laidN and honFit_told_of_home concern two of
  its premises. That any verifier accepts the placeholders' proofs is not proved.
- zeta_any, zeta_any_told, endAt_any_told, atOnce_any_told and eight_any_told ask that five error
  numbers of N₀ are 0; the last three fix ok and Gs at everything. So parameters whose key file's or
  sessions' simulators err, or whose provers abort on private data, are not served.
- That the ranges of all coins are the same for all public files in scope is not proved. Left, as
  far as read: the other two request trees' depths (at most 2 ^ 20 under Twelve: a bound, no
  equation); the sizes of protocol.EncodingRandomness and of the link prover's coins; no size of an enumeration is stated
  as a number, and no divisibility. queryLayout.depth = 32 in scope (Twelve.depth). sMT occurs in no range.
- By depthReqL_home, sideFit_any's premise cn.slotL < 2 ^ depthReqL says cn.slotL = 0.
- fixedAtN, BitsEN and laidAtN are new definitions that occur in conclusions.

Terms: E2E/HidingTerms.lean and E2E/LinkLaidTold.lean.
-/
import E2E.LinkLaidToldAsks
import E2E.LinkLaidEightTold
import E2E.FiveLeftSilentWindows

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.LinkLaid.Any
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.Shown AtPublicFiles.LinkLaid.Told
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput LayoutsByPublicReading)
open OnBytes.K.Arm.Pub (D8)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed homeR homeT)

/-! ## 1. HonFit does not read cfg -/

/-- **HonFit does not read S.cfg**, for arbitrary parameters. -/
theorem honFit_cfg {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (Hs : ThreeProvers L) (F : Falls Hs) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (l : List (Dig lam)) (Yes : I → X → Prop)
    (Zs : I → L.EncodingRandomness → Set L.OutOfDomainSeed) (ζ pT pL pO : ℝ≥0∞) :
    HonFit Hs F W { S with cfg := l } Yes Zs ζ pT pL pO ↔ HonFit Hs F W S Yes Zs ζ pT pL pO :=
  ⟨fun h => ⟨h.extT, h.extL, h.extB, h.whT, h.whL, h.whB, h.accT, h.accL, h.accB, h.prZ, h.prT,
      h.prL, h.prB, h.num⟩,
    fun h => ⟨h.extT, h.extL, h.extB, h.whT, h.whL, h.whB, h.accT, h.accL, h.accB, h.prZ, h.prT,
      h.prL, h.prB, h.num⟩⟩

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows _root_.Run.digToBytes

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **HonFit at homeR b Z's own data gives HonFit at the data at every d**, for all provers. -/
theorem honFit_told_of_home (d : D8) {Hs : ThreeProvers (homeR b Z).protocol} {F : Falls Hs}
    {Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop}
    {Zs : (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed} {ζ pT pL pO : ℝ≥0∞}
    (h : HonFit Hs F (homeR b Z).queryLayout (homeR b Z).seedQueries Yes Zs ζ pT pL pO) :
    HonFit Hs F (homeR b Z).queryLayout ((homeT b Z).Sd d) Yes Zs ζ pT pL pO := by
  rw [seed_is b Z d]
  exact (honFit_cfg Hs F (homeR b Z).queryLayout (homeR b Z).seedQueries [d.1] Yes Zs ζ pT pL pO).2 h

/-! ## 1b. Two numbers at homeR b Z -/

/-- **The first salt of a compiled run has 256 bits**, for all public files. -/
theorem sFS_home : (homeR b Z).compilerParameters.sFS = 256 :=
  atHome b Z (P := fun r => r.compilerParameters.sFS = 256) rfl

/-- **The link's request tree has depth 0**, for all public files. -/
theorem depthReqL_home : (homeR b Z).queryLayout.depthReqL = 0 :=
  atHome b Z (P := fun r => r.queryLayout.depthReqL = 0) rfl

/-! ## 2. For arbitrary parameters a₀ -/

section Any
variable (a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  (Sm₀ : Sims (homeR b Z).protocol) (cn : CoinNums (homeR b Z).LeafBody) (N₀ : NumsW) (v₀ : a₀.RV)
  (E : Enum (RunBits 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS cn.ℓ cn.ℓr (homeR b Z).queryLayout.depthReqL))

/-- PremW for a₀ at homeR b Z's own data gives PremW there with the explicit link prover
substituted: premW_withLaid. -/
theorem premW_any_home {ok : (homeR b Z).Index → Prop} {Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop}
    {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop}
    (hP : PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters a₀ Sm₀ ok Gs Ryes cn N₀)
    (hv : a₀.okV v₀) (hE : E.OK) :
    PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters (withLaidLink b Z a₀ cn v₀ E)
      (fitSims Sm₀) ok Gs Ryes cn (fitNums N₀) :=
  premW_withLaid b Z (homeR b Z).seedQueries (homeR b Z).answerCode a₀ Sm₀ ok Gs Ryes cn N₀ v₀ E hP hv hE

/-- **The same at every d.** -/
theorem premW_any_told (d : (homeT b Z).D) {ok : (homeR b Z).Index → Prop}
    {Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop} {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop}
    (hP : PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters a₀ Sm₀ ok Gs Ryes cn N₀)
    (hv : a₀.okV v₀) (hE : E.OK) :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).cA d) (homeR b Z).compilerParameters
      (withLaidLink b Z a₀ cn v₀ E) (fitSims Sm₀) ok Gs Ryes cn (fitNums N₀) :=
  premW_told_of_home b Z d (premW_any_home b Z a₀ Sm₀ cn N₀ v₀ E hP hv hE)

/-- **The bound on the error**, at homeR b Z's own data. It asks nothing of a₀'s provers. -/
theorem zeta_any (scope : InScope Z = true) (s1 M CT CL CB : ℕ) (e1 : N₀.s1 = s1) (e2 : a₀.M = M)
    (hT : ∀ i, a₀.capT i ≤ CT) (hL : ∀ i, a₀.capL i ≤ CL) (hB : ∀ i, a₀.capB i ≤ CB)
    (hz : N₀.zT = 0 ∧ N₀.zO = 0 ∧ N₀.hT = 0 ∧ N₀.hO = 0 ∧ N₀.δ = 0) (hℓ : 256 ≤ cn.ℓ) (t n : ℕ)
    (hn : n ≤ s1) :
    zetaW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).compilerParameters (withLaidLink b Z a₀ cn v₀ E) cn (fitNums N₀)
      t n ≤ boundZ (9 + CT + CL + CB) M t n := by
  subst e1 e2
  exact zeta_of_twelve (homeR b Z) (twelve_home b Z scope) (withLaidLink b Z a₀ cn v₀ E) cn
    (fitNums N₀) t n CT CL CB hT hL hB
    ⟨hz.1, rfl, hz.2.1, hz.2.2.1, rfl, hz.2.2.2.1, hz.2.2.2.2⟩ hn hℓ

/-- The same at every d. -/
theorem zeta_any_told (d : (homeT b Z).D) (scope : InScope Z = true) (s1 M CT CL CB : ℕ)
    (e1 : N₀.s1 = s1) (e2 : a₀.M = M) (hT : ∀ i, a₀.capT i ≤ CT) (hL : ∀ i, a₀.capL i ≤ CL)
    (hB : ∀ i, a₀.capB i ≤ CB)
    (hz : N₀.zT = 0 ∧ N₀.zO = 0 ∧ N₀.hT = 0 ∧ N₀.hO = 0 ∧ N₀.δ = 0) (hℓ : 256 ≤ cn.ℓ) (t n : ℕ)
    (hn : n ≤ s1) :
    zetaW (homeR b Z).queryLayout ((homeT b Z).Sd d) (homeR b Z).compilerParameters (withLaidLink b Z a₀ cn v₀ E) cn
      (fitNums N₀) t n ≤ boundZ (9 + CT + CL + CB) M t n :=
  le_of_eq_of_le (congrFun (congrFun (zeta_told b Z d _ _ _) t) n)
    (zeta_any b Z a₀ cn N₀ v₀ E scope s1 M CT CL CB e1 e2 hT hL hB hz hℓ t n hn)

set_option maxHeartbeats 1600000 in
/-- **The conclusion of wholeKeyPrivacy with the bound, at every d.** -/
theorem endAt_any_told (d : (homeT b Z).D) (scope : InScope Z = true)
    {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop}
    (hP : PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters a₀ Sm₀ (fun _ => True)
      (fun _ => True) Ryes cn N₀)
    (hv : a₀.okV v₀) (hE : E.OK) (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit)
    (i₀ : (homeR b Z).Index) (hR : ∀ i x w, R.yes i x w → Ryes i x) (s1 M CT CL CB : ℕ)
    (e1 : N₀.s1 = s1) (e2 : a₀.M = M) (hT : ∀ i, a₀.capT i ≤ CT) (hL : ∀ i, a₀.capL i ≤ CL)
    (hB : ∀ i, a₀.capB i ≤ CB)
    (hz : N₀.zT = 0 ∧ N₀.zO = 0 ∧ N₀.hT = 0 ∧ N₀.hO = 0 ∧ N₀.δ = 0) (hℓ : 256 ≤ cn.ℓ) :
    EndAt ((homeT b Z).at d) (withLaidLink b Z a₀ cn v₀ E) (fitSims Sm₀) cn (fitNums N₀) R i₀ s1
      (9 + CT + CL + CB) M :=
  endAt_at (homeT b Z) d hR (premW_any_told b Z a₀ Sm₀ cn N₀ v₀ E d hP hv hE)
    (twelve_home b Z scope) s1 M CT CL CB e1 e2 hT hL hB
    ⟨hz.1, rfl, hz.2.1, hz.2.2.1, rfl, hz.2.2.2.1, hz.2.2.2.2⟩ hℓ

/-- **The explicit link prover never aborts; the other two provers are a₀'s.** -/
theorem neverStops_any (h₀ : NeverStops a₀.side.st) :
    NeverStops (withLaidLink b Z a₀ cn v₀ E).side.st :=
  ⟨h₀.T,
    fun _ _ _ _ => @decide_eq_false _ ((withLaidLink b Z a₀ cn v₀ E).dc.Lk _ _ _)
      fun h => h.elim (fun a => a) fun a => a,
    h₀.B⟩

/-- **With at least 2 ^ 40 tries in every search the proofs are produced, at every d**, except with
probability at most (a₀.M + 2) · 71 · 2 ^ -256, where a₀'s provers never abort. -/
theorem strings_any_told (d : (homeT b Z).D) (scope : InScope Z = true)
    (h₀ : NeverStops a₀.side.st) (h1 : ∀ i, 2 ^ 40 ≤ a₀.capT i + 1)
    (h2 : ∀ i, 2 ^ 40 ≤ a₀.capL i + 1) (h3 : ∀ i, 2 ^ 40 ≤ a₀.capB i + 1) (i : (homeR b Z).Index)
    (x : (homeR b Z).Instance) :
    PrFrom (Table.empty _) (runOf ((homeT b Z).at d) (withLaidLink b Z a₀ cn v₀ E).side i x)
      {y | ¬ FullTo (a₀.M + 1) y} ≤ ((a₀.M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256) :=
  full_at (homeT b Z) d (withLaidLink b Z a₀ cn v₀ E).side (tries_home b Z scope)
    (FlashProve.lawFit_home b Z d _ _ _) (FlashProve.wiresFit_home b Z d)
    (neverStops_any b Z a₀ cn v₀ E h₀) h1 h2 h3 i x

set_option maxHeartbeats 1600000 in
/-- **AtOnceAt at every d**: one copy, every search limit at most 2 ^ 40 and at least 2 ^ 40 - 1. -/
theorem atOnce_any_told (d : (homeT b Z).D) (scope : InScope Z = true)
    {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop}
    (hP : PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters a₀ Sm₀ (fun _ => True)
      (fun _ => True) Ryes cn N₀)
    (hv : a₀.okV v₀) (hE : E.OK) (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit)
    (i₀ : (homeR b Z).Index) (hR : ∀ i x w, R.yes i x w → Ryes i x) (s1 : ℕ) (e1 : N₀.s1 = s1)
    (e2 : a₀.M = 0) (hT : ∀ i, a₀.capT i ≤ 2 ^ 40) (hL : ∀ i, a₀.capL i ≤ 2 ^ 40)
    (hB : ∀ i, a₀.capB i ≤ 2 ^ 40)
    (hz : N₀.zT = 0 ∧ N₀.zO = 0 ∧ N₀.hT = 0 ∧ N₀.hO = 0 ∧ N₀.δ = 0) (hℓ : 256 ≤ cn.ℓ)
    (h1 : 1 ≤ s1) (h₀ : NeverStops a₀.side.st) (c1 : ∀ i, 2 ^ 40 ≤ a₀.capT i + 1)
    (c2 : ∀ i, 2 ^ 40 ≤ a₀.capL i + 1) (c3 : ∀ i, 2 ^ 40 ≤ a₀.capB i + 1) :
    AtOnceAt ((homeT b Z).at d) (withLaidLink b Z a₀ cn v₀ E) (fitSims Sm₀) cn (fitNums N₀) R i₀
      s1 :=
  atOnceAt_at (homeT b Z) d
    (endAt_any_told b Z a₀ Sm₀ cn N₀ v₀ E d scope hP hv hE R i₀ hR s1 0 (2 ^ 40) (2 ^ 40) (2 ^ 40)
      e1 e2 hT hL hB hz hℓ)
    h1 (tries_home b Z scope) (FlashProve.lawFit_home b Z d _ _ _)
    (FlashProve.wiresFit_home b Z d) (neverStops_any b Z a₀ cn v₀ E h₀) c1 c2 c3

set_option maxHeartbeats 1600000 in
/-- **EightAt at every d**, for public files with a live description, where the session's simulator
always returns a view. -/
theorem eight_any_told (d : (homeT b Z).D) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop}
    (hP : PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters a₀ Sm₀ (fun _ => True)
      (fun _ => True) Ryes cn N₀)
    (hv : a₀.okV v₀) (hE : E.OK) (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit)
    (i₀ : (homeR b Z).Index) (hR : ∀ i x w, R.yes i x w → Ryes i x) (s1 : ℕ) (e1 : N₀.s1 = s1)
    (e2 : a₀.M = 0) (hT : ∀ i, a₀.capT i ≤ 2 ^ 40) (hL : ∀ i, a₀.capL i ≤ 2 ^ 40)
    (hB : ∀ i, a₀.capB i ≤ 2 ^ 40)
    (hz : N₀.zT = 0 ∧ N₀.zO = 0 ∧ N₀.hT = 0 ∧ N₀.hO = 0 ∧ N₀.δ = 0) (hℓ : 256 ≤ cn.ℓ)
    (h1 : 1 ≤ s1) (h₀ : NeverStops a₀.side.st)
    (hSm : ∀ n y ρ ans, none ∉ (Sm₀.B n y ρ ans).support) (c1 : ∀ i, 2 ^ 40 ≤ a₀.capT i + 1)
    (c2 : ∀ i, 2 ^ 40 ≤ a₀.capL i + 1) (c3 : ∀ i, 2 ^ 40 ≤ a₀.capB i + 1) :
    EightAt ((homeT b Z).at d) (withLaidLink b Z a₀ cn v₀ E) (fitSims Sm₀) cn (fitNums N₀) R i₀
      s1 :=
  eightAt_at (homeT b Z) d
    (endAt_any_told b Z a₀ Sm₀ cn N₀ v₀ E d scope hP hv hE R i₀ hR s1 0 (2 ^ 40) (2 ^ 40) (2 ^ 40)
      e1 e2 hT hL hB hz hℓ)
    h1 (tries_home b Z scope) (FlashProve.lawFit_home b Z d _ _ _)
    (FlashProve.wiresFit_home b Z d) (neverStops_any b Z a₀ cn v₀ E h₀)
    (readsSome_home b Z scope live) (readsLink_home b Z) (instance_home b Z)
    (pathsFit_of_prem (premW_any_told b Z a₀ Sm₀ cn N₀ v₀ E d hP hv hE)) hSm c1 c2 c3

/-- **SideFit passes from a₀ to the substituted parameters**, where a₀'s filler has cn.ℓ bits, these
fit into a leaf's salt, and the link's slot lies in its request tree. -/
theorem sideFit_any (h : SideFit (homeR b Z).queryLayout (homeR b Z).compilerParameters a₀.side)
    (hf : a₀.fill.length = cn.ℓ) (hℓ : cn.ℓ ≤ (homeR b Z).compilerParameters.sMT)
    (hslot : cn.slotL < 2 ^ (homeR b Z).queryLayout.depthReqL) :
    SideFit (homeR b Z).queryLayout (homeR b Z).compilerParameters (withLaidLink b Z a₀ cn v₀ E).side where
  sl := h.sl
  coT := h.coT
  coL := fun e _ => fit_dress_coinsPre
    (L' := typedOracleCarrier (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (fun _ _ _ => List.replicate ((homeR b Z).compilerParameters.sMT - cn.ℓ) false) a₀.rtail a₀.nR a₀.nK a₀.nJ
    (homeR b Z).compilerParameters.sFS cn.ℓ cn.ℓr (homeR b Z).queryLayout.depthReqL (homeR b Z).compilerParameters.sMT cn.padL cn.slotL a₀.fill
    a₀.fill E (fun _ _ _ => by rw [List.length_replicate]; exact Nat.sub_add_cancel hℓ) hf hslot e
  coB := h.coB

end Any

/-! ## 3. The first member: laidAt -/

section Laid
variable (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
  (E : BitsE b Z b₀ M ℓ ℓr capT capL capB)

/-- laidAt is withLaidLink over the placeholder provers' parameters fixedAt. -/
theorem laidAt_is : laidAt b Z b₀ M ℓ ℓr capT capL capB E =
    withLaidLink b Z (fixedAt b Z b₀ M ℓ ℓr capT capL capB) (coinNums (homeR b Z) b₀ ℓ ℓr) () E :=
  rfl

/-- hP for fixedAt. -/
theorem premW_fixed_home (scope : InScope Z = true) (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127)
    (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) :
    PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters
      (fixedAt b Z b₀ M ℓ ℓr capT capL capB) (fixedSims (homeR b Z).protocol) (fun _ => True)
      (fun _ => True) Ryes (coinNums (homeR b Z) b₀ ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) :=
  premW_of_five (homeR b Z) (noProverSide_home b Z scope M s1 hM hs 0 0 0 0 0 0 capT capL capB)
    (fiveLeft_fixed (homeR b Z) b₀ M s1 ℓ ℓr capT capL capB hℓ (fun _ => True) Ryes)

/-- premW_laid_told (E2E/LinkLaidTold.lean), from premW_any_told. -/
theorem premW_laid_told_any (d : (homeT b Z).D) (scope : InScope Z = true) (hM : M + 1 ≤ 710324)
    (hs : s1 ≤ 688127) (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) (hE : E.OK)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).cA d) (homeR b Z).compilerParameters
      (laidAt b Z b₀ M ℓ ℓr capT capL capB E) (fitSims (fixedSims (homeR b Z).protocol)) (fun _ => True)
      (fun _ => True) Ryes (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) :=
  premW_any_told b Z (fixedAt b Z b₀ M ℓ ℓr capT capL capB) (fixedSims (homeR b Z).protocol)
    (coinNums (homeR b Z) b₀ ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) () E d
    (premW_fixed_home b Z b₀ M s1 ℓ ℓr capT capL capB scope hM hs hℓ Ryes) trivial hE

/-- **SideFit fails for laidAt**, for 1 ≤ ℓ ≤ sMT: its filler is empty, and the first table's run is
the placeholder's. -/
theorem not_sideFit_laid (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) :
    ¬ SideFit (homeR b Z).queryLayout (homeR b Z).compilerParameters (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side := fun h =>
  not_coT_silentN (homeR b Z) b₀ M ℓ ℓr (roundsOf (homeR b Z)) (winK (homeR b Z))
    (winJ (homeR b Z)) [] capT capL capB hℓ (Nat.ne_of_lt h1) h.coT

end Laid

/-! ## 4. The second member, with two placeholder provers: a window of constants and a filler of ℓ
zeros -/

/-- The placeholder provers' parameters at homeR b Z, with the window 2 ^ 20, 2 ^ 39, 2 ^ 39 and a
filler of ℓ zeros. -/
abbrev fixedAtN (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ) :
    AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits :=
  silentAtN (homeR b Z) b₀ M ℓ ℓr (2 ^ 20) (2 ^ 39) (2 ^ 39) (List.replicate ℓ false) capT capL capB

/-- The type of the enumerations of the free bits of the link's compiled run, in that window. -/
abbrev BitsEN (ℓ ℓr : ℕ) : Type :=
  Enum (RunBits 256 (2 ^ 20) (2 ^ 39) (2 ^ 39) (homeR b Z).compilerParameters.sFS ℓ ℓr (homeR b Z).queryLayout.depthReqL)

/-- **The second member**, with two placeholder provers: the same with the explicit link prover
substituted for the link's placeholder. Another scheme than laidAt's. -/
def laidAtN (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ) (E : BitsEN b Z ℓ ℓr) :
    AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits :=
  withLaidLink b Z (fixedAtN b Z b₀ M ℓ ℓr capT capL capB) (coinNums (homeR b Z) b₀ ℓ ℓr) () E

section LaidN
variable (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ) (E : BitsEN b Z ℓ ℓr)

/-- There is an E that lists each value once. -/
theorem bitsEN_listed : ∃ E' : BitsEN b Z ℓ ℓr, E'.OK := runBits_listed _ _ _ _ _ _ _ _

/-- **The type BitsEN does not depend on b or Z.** -/
theorem bitsEN_eq :
    BitsEN b Z ℓ ℓr = Enum (RunBits 256 (2 ^ 20) (2 ^ 39) (2 ^ 39) 256 ℓ ℓr 0) := by
  show Enum (RunBits 256 (2 ^ 20) (2 ^ 39) (2 ^ 39) (homeR b Z).compilerParameters.sFS ℓ ℓr
    (homeR b Z).queryLayout.depthReqL) = _
  rw [sFS_home, depthReqL_home]

/-- hP for fixedAtN, for public files in scope. -/
theorem premW_fixedN_home (scope : InScope Z = true) (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127)
    (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) :
    PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters
      (fixedAtN b Z b₀ M ℓ ℓr capT capL capB) (fixedSims (homeR b Z).protocol) (fun _ => True)
      (fun _ => True) Ryes (coinNums (homeR b Z) b₀ ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) :=
  premW_of_five (homeR b Z) (noProverSide_home b Z scope M s1 hM hs 0 0 0 0 0 0 capT capL capB)
    (fiveLeft_fixedN (homeR b Z) b₀ M ℓ ℓr (2 ^ 20) (2 ^ 39) (2 ^ 39) (List.replicate ℓ false) capT
      capL capB s1 hℓ (windows_of_twelve (homeR b Z) (twelve_home b Z scope)) (fun _ => True) Ryes)

/-- The placeholder provers never abort. -/
theorem neverStops_fixedN : NeverStops (fixedAtN b Z b₀ M ℓ ℓr capT capL capB).side.st :=
  ⟨fun _ _ _ _ => @decide_eq_false _ ((fixedAtN b Z b₀ M ℓ ℓr capT capL capB).dc.T _ _ _)
      fun h => h.elim (fun a => a) fun a => a,
    fun _ _ _ _ => @decide_eq_false _ ((fixedAtN b Z b₀ M ℓ ℓr capT capL capB).dc.Lk _ _ _)
      fun h => h.elim (fun a => a) fun a => a,
    fun _ _ _ _ _ _ => @decide_eq_false _ ((fixedAtN b Z b₀ M ℓ ℓr capT capL capB).dc.B _ _ _)
      fun h => h.elim (fun a => a) fun a => a⟩

/-- **PremW holds for the second member, at every d.** There are no lower bounds: ℓ = 0, search
limits 0 and s1 = 0 are admitted. -/
theorem premW_laidN_told (d : (homeT b Z).D) (scope : InScope Z = true) (hM : M + 1 ≤ 710324)
    (hs : s1 ≤ 688127) (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) (hE : E.OK)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).cA d) (homeR b Z).compilerParameters
      (laidAtN b Z b₀ M ℓ ℓr capT capL capB E) (fitSims (fixedSims (homeR b Z).protocol)) (fun _ => True)
      (fun _ => True) Ryes (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) :=
  premW_any_told b Z (fixedAtN b Z b₀ M ℓ ℓr capT capL capB) (fixedSims (homeR b Z).protocol)
    (coinNums (homeR b Z) b₀ ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) () E d
    (premW_fixedN_home b Z b₀ M s1 ℓ ℓr capT capL capB scope hM hs hℓ Ryes) trivial hE

/-- The bound on the error for the second member, at every d. Its premises bound the search limits
from above only, and boundZ is given no number here. -/
theorem zeta_laidN_told (d : (homeT b Z).D) (scope : InScope Z = true) (CT CL CB : ℕ)
    (hℓ : 256 ≤ ℓ) (hT : ∀ i, capT i ≤ CT) (hL : ∀ i, capL i ≤ CL) (hB : ∀ i, capB i ≤ CB)
    (t n : ℕ) (hn : n ≤ s1) :
    zetaW (homeR b Z).queryLayout ((homeT b Z).Sd d) (homeR b Z).compilerParameters (laidAtN b Z b₀ M ℓ ℓr capT capL capB E)
      (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) t n ≤
      boundZ (9 + CT + CL + CB) M t n :=
  zeta_any_told b Z (fixedAtN b Z b₀ M ℓ ℓr capT capL capB) (coinNums (homeR b Z) b₀ ℓ ℓr)
    (indexPrivacyNumbers s1 0 0 0 0 0 0) () E d scope s1 M CT CL CB rfl rfl hT hL hB ⟨rfl, rfl, rfl, rfl, rfl⟩
    hℓ t n hn

/-- With at least 2 ^ 40 tries in every search the proofs are produced for the second member, at
every d, except with probability at most (M + 2) · 71 · 2 ^ -256. -/
theorem strings_laidN_told (d : (homeT b Z).D) (scope : InScope Z = true)
    (h1 : ∀ i, 2 ^ 40 ≤ capT i + 1) (h2 : ∀ i, 2 ^ 40 ≤ capL i + 1)
    (h3 : ∀ i, 2 ^ 40 ≤ capB i + 1) (i : (homeR b Z).Index) (x : (homeR b Z).Instance) :
    PrFrom (Table.empty _)
      (runOf ((homeT b Z).at d) (laidAtN b Z b₀ M ℓ ℓr capT capL capB E).side i x)
      {y | ¬ FullTo (M + 1) y} ≤ ((M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256) :=
  strings_any_told b Z (fixedAtN b Z b₀ M ℓ ℓr capT capL capB) (coinNums (homeR b Z) b₀ ℓ ℓr) () E
    d scope (neverStops_fixedN b Z b₀ M ℓ ℓr capT capL capB) h1 h2 h3 i x

/-- **SideFit holds for the second member**, for ℓ ≤ sMT. -/
theorem sideFit_laidN (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) :
    SideFit (homeR b Z).queryLayout (homeR b Z).compilerParameters (laidAtN b Z b₀ M ℓ ℓr capT capL capB E).side :=
  sideFit_any b Z (fixedAtN b Z b₀ M ℓ ℓr capT capL capB) (coinNums (homeR b Z) b₀ ℓ ℓr) () E
    (sideFit_silentN (homeR b Z) b₀ M ℓ ℓr (2 ^ 20) (2 ^ 39) (2 ^ 39) (List.replicate ℓ false) capT
      capL capB hℓ List.length_replicate (fits_home b Z).2.oka.base.fits)
    List.length_replicate hℓ (Nat.two_pow_pos _)

end LaidN

set_option maxHeartbeats 1600000 in
/-- **AtOnceAt for the second member, at every d**, for public files in scope with a live
description: one copy, ℓ := 320, every search limit 2 ^ 40. -/
theorem atOnce_laidN_told (d : (homeT b Z).D) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (b₀ : (homeR b Z).LeafBody) (s1 ℓr : ℕ) (E : BitsEN b Z 320 ℓr)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index)
    (hE : E.OK) (h1 : 1 ≤ s1) (h2 : s1 ≤ 688127) (hR : ∀ i x w, R.yes i x w → Ryes i x) :
    AtOnceAt ((homeT b Z).at d)
      (laidAtN b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E)
      (fitSims (fixedSims (homeR b Z).protocol)) (coinNums (homeR b Z) b₀ 320 ℓr)
      (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) R i₀ s1 :=
  atOnce_any_told b Z
    (fixedAtN b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40)
    (fixedSims (homeR b Z).protocol) (coinNums (homeR b Z) b₀ 320 ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) () E d scope
    (premW_fixedN_home b Z b₀ 0 s1 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
      scope (by norm_num) h2 (by rw [sMT_home b Z scope live]; norm_num) Ryes)
    trivial hE R i₀ hR s1 rfl rfl (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    ⟨rfl, rfl, rfl, rfl, rfl⟩ (show (256 : ℕ) ≤ 320 by norm_num) h1
    (neverStops_fixedN b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40)
    (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _)

set_option maxHeartbeats 1600000 in
/-- **EightAt for the second member, at every d**, for public files in scope with a live
description. -/
theorem eight_laidN_told (d : (homeT b Z).D) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (b₀ : (homeR b Z).LeafBody) (s1 ℓr : ℕ) (E : BitsEN b Z 320 ℓr)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index)
    (hE : E.OK) (h1 : 1 ≤ s1) (h2 : s1 ≤ 688127) (hR : ∀ i x w, R.yes i x w → Ryes i x) :
    EightAt ((homeT b Z).at d)
      (laidAtN b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E)
      (fitSims (fixedSims (homeR b Z).protocol)) (coinNums (homeR b Z) b₀ 320 ℓr)
      (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) R i₀ s1 :=
  eight_any_told b Z
    (fixedAtN b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40)
    (fixedSims (homeR b Z).protocol) (coinNums (homeR b Z) b₀ 320 ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) () E d scope
    live
    (premW_fixedN_home b Z b₀ 0 s1 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
      scope (by norm_num) h2 (by rw [sMT_home b Z scope live]; norm_num) Ryes)
    trivial hE R i₀ hR s1 rfl rfl (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    ⟨rfl, rfl, rfl, rfl, rfl⟩ (show (256 : ℕ) ≤ 320 by norm_num) h1
    (neverStops_fixedN b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40)
    (fun _ _ _ _ hm => by cases (PMF.mem_support_pure_iff _ _).1 hm)
    (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _)

end AtPublicFiles.LinkLaid.Any

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.Any.honFit_cfg
#print axioms AtPublicFiles.LinkLaid.Any.honFit_told_of_home
#print axioms AtPublicFiles.LinkLaid.Any.sFS_home
#print axioms AtPublicFiles.LinkLaid.Any.depthReqL_home
#print axioms AtPublicFiles.LinkLaid.Any.premW_any_home
#print axioms AtPublicFiles.LinkLaid.Any.premW_any_told
#print axioms AtPublicFiles.LinkLaid.Any.zeta_any
#print axioms AtPublicFiles.LinkLaid.Any.zeta_any_told
#print axioms AtPublicFiles.LinkLaid.Any.endAt_any_told
#print axioms AtPublicFiles.LinkLaid.Any.neverStops_any
#print axioms AtPublicFiles.LinkLaid.Any.strings_any_told
#print axioms AtPublicFiles.LinkLaid.Any.atOnce_any_told
#print axioms AtPublicFiles.LinkLaid.Any.eight_any_told
#print axioms AtPublicFiles.LinkLaid.Any.sideFit_any
#print axioms AtPublicFiles.LinkLaid.Any.laidAt_is
#print axioms AtPublicFiles.LinkLaid.Any.premW_fixed_home
#print axioms AtPublicFiles.LinkLaid.Any.premW_laid_told_any
#print axioms AtPublicFiles.LinkLaid.Any.not_sideFit_laid
#print axioms AtPublicFiles.LinkLaid.Any.fixedAtN
#print axioms AtPublicFiles.LinkLaid.Any.BitsEN
#print axioms AtPublicFiles.LinkLaid.Any.laidAtN
#print axioms AtPublicFiles.LinkLaid.Any.bitsEN_listed
#print axioms AtPublicFiles.LinkLaid.Any.bitsEN_eq
#print axioms AtPublicFiles.LinkLaid.Any.premW_fixedN_home
#print axioms AtPublicFiles.LinkLaid.Any.neverStops_fixedN
#print axioms AtPublicFiles.LinkLaid.Any.premW_laidN_told
#print axioms AtPublicFiles.LinkLaid.Any.zeta_laidN_told
#print axioms AtPublicFiles.LinkLaid.Any.strings_laidN_told
#print axioms AtPublicFiles.LinkLaid.Any.sideFit_laidN
#print axioms AtPublicFiles.LinkLaid.Any.atOnce_laidN_told
#print axioms AtPublicFiles.LinkLaid.Any.eight_laidN_told
