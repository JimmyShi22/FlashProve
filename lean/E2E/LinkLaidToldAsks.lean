-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/LinkLaidToldAsks.lean

Summary. Where the digest of the public files enters the scheme of E2E/LinkLaidTold.lean. This file
is about the text of the scheme: at which point of an oracle it asks. It says nothing on values,
distributions or hiding.

Why. PremW and zetaW do not read the field cfg of the OOD phase's compilation data S (premW_cfg,
zetaW_cfg), and at the told record homeT b Z the data at d are those of homeR b Z with cfg set to
[d.1] (seed_is). So PremW at homeR b Z's data gives PremW at the data at every d, for every
structure of provers, simulators and numbers (premW_told_of_home); premW_laid_told
(E2E/LinkLaidTold.lean) follows from premW_laid in this way (premW_laid_told_again). The digest
occurs in the text of the committer, the verifier and the simulator: a table's OOD seed is made from
the answers to two queries, and the first of them holds S.cfg.

What this file has.
  premW_cfg, zetaW_cfg   for arbitrary parameters: PremW and zetaW are unchanged when S.cfg is
                     replaced by any list.
  seedQ0_head        for arbitrary parameters: the head of the first query of a table's OOD seed, at
                     the root cm, is .f1 (cm :: S.cfg) none S.shape.
  seedQ0_head_inj    if the first queries for S and S' at one root have the same head, then
                     S.cfg = S'.cfg.
  seedsO_asks, seedIs_asks   the committer's two queries for a seed (seedsO,
                     Johnson/Prover/All/Defs.lean) and the verifier's test of a seed (outOfDomainSeedIs,
                     Johnson/TypedOracleCompiler/RecCompile/Seeds.lean) both begin by asking that query.
  premW_of_cfg       for an arbitrary told record T over parameters r: where T.Sd d is r.seedQueries with
                     another cfg and T.cA d is r.answerCode, PremW at r's two fields is PremW at T's at d.
  seed_is            (homeT b Z).Sd d is (homeR b Z).seedQueries with cfg set to [d.1].
  premW_told_of_home, premW_laid_told_again   see "Why".
  told_seed_query    at the told record homeT b Z and d: that head is .f1 [cm, d.1] none _.
  told_seed_query_ne two digests give two heads, at every root.

Limits.
- That the three programs reach these queries is by definition and not stated here. The committer:
  commitAt calls tabO and tabsO, which call seedsO at each table's root
  (Johnson/WholeKey/Defs.lean). The verifier: verifyW calls verifyAtKeyRoot, that calls verifyAtFullKey, and that calls
  outOfDomainSeedIs twice where all three proofs are present (Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean,
  CmsAns.lean). The simulator: tableA calls seedsO (Johnson/WholeKey/Wrap.lean).
- Which fields of S PremW does read (S.seed, S.t, S.pl0, S.pl1) is by inspection of
  Johnson/WholeKey/Premises.lean.
- Nothing is said on what the oracle answers. In particular it is not proved that at two digests the
  committer publishes two different keys under some oracle functions.
- Whether S.cfg is read at any other place of the scheme or of the simulator is not stated.

Terms: E2E/HidingTerms.lean and E2E/LinkLaidTold.lean.
-/
import E2E.LinkLaidTold

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.LinkLaid.Told
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises
open OnBytes.LinkSim.AtHome
open VerifiableInference.OnPublicFiles (InnerCompilerInput LayoutsByPublicReading)
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.K.Arm.Pub (D8)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (homeR homeT)

/-! ## 1. For arbitrary parameters -/

section Letters
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S S' : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- **PremW does not read S.cfg.** -/
theorem premW_cfg (l : List (Dig lam)) (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : _root_.Compile.Params)
    (a : AtRecs lam L Bd aT aL) (Sm : Sims L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop)
    (Ryes : I → X → Prop) (c : CoinNums Bd) (N : NumsW) :
    PremW W { S with cfg := l } cA p a Sm ok Gs Ryes c N ↔ PremW W S cA p a Sm ok Gs Ryes c N :=
  ⟨fun h => ⟨h.ext, h.runVals, h.reads, h.budget₀, h.budget₁, h.good, h.stops, h.seeds, h.freeT,
      h.freeL, h.freeB, h.wires, h.fmt, h.backT, h.backL, h.backB, h.plain, h.coherent, h.isLocal,
      h.coins⟩,
    fun h => ⟨h.ext, h.runVals, h.reads, h.budget₀, h.budget₁, h.good, h.stops, h.seeds, h.freeT,
      h.freeL, h.freeB, h.wires, h.fmt, h.backT, h.backL, h.backB, h.plain, h.coherent, h.isLocal,
      h.coins⟩⟩

/-- **zetaW does not read S.cfg.** -/
theorem zetaW_cfg (l : List (Dig lam)) (p : _root_.Compile.Params) (a : AtRecs lam L Bd aT aL)
    (c : CoinNums Bd) (u : NumsW) : zetaW W { S with cfg := l } p a c u = zetaW W S p a c u :=
  zetaW_tag W { S with cfg := l } S rfl p a c u

/-- The head of the first query of a table's OOD seed holds the root and then S.cfg. -/
theorem seedQ0_head (cm : Dig lam) :
    (seedQ0 W S cm).head = .f1 (cm :: S.cfg) none S.shape := rfl

/-- If the first queries for S and S' at one root have the same head, then S.cfg = S'.cfg. -/
theorem seedQ0_head_inj (cm : Dig lam) (h : (seedQ0 W S cm).head = (seedQ0 W S' cm).head) :
    S.cfg = S'.cfg := by
  rw [seedQ0_head, seedQ0_head] at h
  injection h with h1
  exact (List.cons.inj h1).2

/-- The committer's two queries for a seed begin with that query. -/
theorem seedsO_asks (cm : Dig lam) :
    ∃ k, seedsO W S cm = OComp.query (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
      (seedQ0 W S cm) k := ⟨_, rfl⟩

/-- The verifier's test of a seed begins with that query. -/
theorem seedIs_asks (cm : Dig lam) (s : L.OutOfDomainSeed) :
    ∃ k, outOfDomainSeedIs W S cm s = OComp.query (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
      (seedQ0 W S cm) k := ⟨_, rfl⟩

end Letters

/-- **Where T.Sd d is r.seedQueries with another cfg and T.cA d is r.answerCode, PremW at r's two fields is PremW at
T's two fields at d**, for an arbitrary told record T over arbitrary parameters r. -/
theorem premW_of_cfg {r : InnerCompilerInput} (T : LayoutsByPublicReading r) (d : T.D) (l : List (Dig 256))
    (hS : T.Sd d = { r.seedQueries with cfg := l }) (hc : T.cA d = r.answerCode)
    (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Sm : Sims r.protocol) (ok : r.Index → Prop) (Gs : r.protocol.OutOfDomainSeed → Prop)
    (Ryes : r.Index → r.Instance → Prop) (c : CoinNums r.LeafBody) (N : NumsW) :
    PremW r.queryLayout r.seedQueries r.answerCode r.compilerParameters a Sm ok Gs Ryes c N ↔
      PremW r.queryLayout (T.Sd d) (T.cA d) r.compilerParameters a Sm ok Gs Ryes c N := by
  rw [hS, hc]
  exact (premW_cfg r.queryLayout r.seedQueries l r.answerCode r.compilerParameters a Sm ok Gs Ryes c N).symm

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows _root_.Run.digToBytes

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-! ## 2. At the told record homeT b Z -/

/-- **The OOD phase's compilation data at d are those of homeR b Z with cfg set to [d.1].** -/
theorem seed_is (d : D8) : (homeT b Z).Sd d = { (homeR b Z).seedQueries with cfg := [d.1] } := by
  have h : (homeT b Z).Sd d = { (homeR b Z).seedQueries with cfg := ((homeT b Z).Sd d).cfg } := rfl
  rw [seed_reads_digest] at h
  exact h

/-- **PremW at homeR b Z's own data gives PremW at the data at every d**, for every structure of
provers, simulators and numbers. -/
theorem premW_told_of_home (d : D8)
    {a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits}
    {Sm : Sims (homeR b Z).protocol} {ok : (homeR b Z).Index → Prop} {Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop}
    {Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop} {c : CoinNums (homeR b Z).LeafBody} {N : NumsW}
    (h : PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters a Sm ok Gs Ryes c N) :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).cA d) (homeR b Z).compilerParameters a Sm ok Gs Ryes c N :=
  (premW_of_cfg (homeT b Z) d [d.1] (seed_is b Z d) (code_told b Z d) a Sm ok Gs Ryes c N).1 h

/-- premW_laid_told (E2E/LinkLaidTold.lean), from premW_laid (E2E/LinkLaidPrivacy.lean). -/
theorem premW_laid_told_again (d : D8) (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ)
    (capT capL capB : ℕ → ℕ) (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (scope : InScope Z = true)
    (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127) (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) (hE : E.OK)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) :
    PremW (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).cA d) (homeR b Z).compilerParameters
      (laidAt b Z b₀ M ℓ ℓr capT capL capB E) (fitSims (fixedSims (homeR b Z).protocol)) (fun _ => True)
      (fun _ => True) Ryes (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) :=
  premW_told_of_home b Z d (premW_laid b Z b₀ M s1 ℓ ℓr capT capL capB E scope hM hs hℓ hE Ryes)

/-- **At d the first query of a table's OOD seed holds the root and the digest d.1.** -/
theorem told_seed_query (d : D8) (cm : Dig 256) :
    (seedQ0 (homeR b Z).queryLayout ((homeT b Z).Sd d) cm).head =
      .f1 [cm, d.1] none ((homeT b Z).Sd d).shape := by
  rw [seedQ0_head, seed_reads_digest]

/-- **Two digests, two queries**, at every root. -/
theorem told_seed_query_ne (d d' : D8) (h : d.1 ≠ d'.1) (cm : Dig 256) :
    (seedQ0 (homeR b Z).queryLayout ((homeT b Z).Sd d) cm).head ≠
      (seedQ0 (homeR b Z).queryLayout ((homeT b Z).Sd d') cm).head := fun e =>
  h (List.cons.inj ((seed_reads_digest b Z d).symm.trans
    ((seedQ0_head_inj (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).Sd d') cm e).trans
      (seed_reads_digest b Z d')))).1

end AtPublicFiles.LinkLaid.Told

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.Told.premW_cfg
#print axioms AtPublicFiles.LinkLaid.Told.zetaW_cfg
#print axioms AtPublicFiles.LinkLaid.Told.seedQ0_head
#print axioms AtPublicFiles.LinkLaid.Told.seedQ0_head_inj
#print axioms AtPublicFiles.LinkLaid.Told.seedsO_asks
#print axioms AtPublicFiles.LinkLaid.Told.seedIs_asks
#print axioms AtPublicFiles.LinkLaid.Told.premW_of_cfg
#print axioms AtPublicFiles.LinkLaid.Told.seed_is
#print axioms AtPublicFiles.LinkLaid.Told.premW_told_of_home
#print axioms AtPublicFiles.LinkLaid.Told.premW_laid_told_again
#print axioms AtPublicFiles.LinkLaid.Told.told_seed_query
#print axioms AtPublicFiles.LinkLaid.Told.told_seed_query_ne
