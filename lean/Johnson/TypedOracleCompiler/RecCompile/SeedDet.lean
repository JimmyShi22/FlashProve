-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/SeedDet.lean: at fixed oracle functions, the seed in an accepted key is the
one that the two seed queries at the key's root give.

After Johnson/Top/TieSeedOne.lean [not in this library], for the two nested seed queries of Seeds.lean and the verifier
`verifyAtFullKey` (CmsAns.lean).
Main names: `seedOfRoot`, `seedIs_det`, `VCA_seed`, `VRA_seed`.
Limits: a fact on runs at fixed oracle functions; no probability.


-/
import Johnson.TypedOracleCompiler.RecCompile.FrontRootAns
import Rom.Cache

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- The answer to the first seed query at a root. -/
def seedAns0 (cm : Dig lam) : FsAns lam W.K := g (OracleName.fb S.t) (seedQ0 W S cm)

/-- The seed that the two seed queries at a root give. -/
def seedOfRoot (cm : Dig lam) : L.OutOfDomainSeed :=
  S.seed (show FsAns lam W.K from g (OracleName.fb S.t) (seedQ1 W S (link (seedAns0 W S g cm)))).1

/-- The run of `outOfDomainSeedIs` says yes exactly at that seed. -/
theorem seedIs_det (cm : Dig lam) (s : L.OutOfDomainSeed) :
    (outOfDomainSeedIs W S cm s).det g = true ↔ s = seedOfRoot W S g cm := by
  classical
  have e : (outOfDomainSeedIs W S cm s).det g = decide (seedOfRoot W S g cm = s) := by
    unfold outOfDomainSeedIs seedOfRoot seedAns0
    simp only [OComp.det_bind]
    exact decide_eq_decide.2 Iff.rfl
  rw [e, decide_eq_true_eq]
  exact eq_comm

/-- In an accepted key the seed is the one that the seed queries at the key's root give. -/
theorem VCA_seed (p : Params) (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L)
    (h : (verifyAtFullKey W S cA r₀ p v x π).det g = true) : v.rcd.1 = seedOfRoot W S g v.cm := by
  unfold verifyAtFullKey at h
  split at h
  · simp only [OComp.det_bind] at h
    have h' : (_ && (outOfDomainSeedIs W S v.cm v.rcd.1).det g && _ && _ && _ && _) = true := h
    simp only [Bool.and_eq_true] at h'
    exact (seedIs_det W S g v.cm v.rcd.1).1 h'.1.1.1.1.2
  · cases h

theorem VRA_seed (p : Params) (k : KeyRoot lam L) (x : X) (π : OfflineLinkOnlineProof lam L aT aL)
    (h : (verifyAtKeyRoot W S cA r₀ p k x π).det g = true) : k.rcd.1 = seedOfRoot W S g k.cm :=
  VCA_seed W S cA r₀ g p (k.full π) x π.low h

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.VRA_seed
