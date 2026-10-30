-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeNoneAside.lean: `asideOf Gs` (E2E/BridgeSeeds.lean) sets aside the out-of-domain (OOD)
seeds outside a set Gs. Where Gs is the set of all seeds, it sets no seed aside, and the guards
`guardT` and `guardFall`, which make a fall empty at the seeds set aside, change no fall (`Falls`,
Johnson/Prover/All/OfHonest.lean: sets of verifier randomness that are set aside on the acceptance
side). So `OnBytes.Prover.HonFit` (same file), stated with `guardT`, `guardFall` and `asideOf` at
all seeds, gives `HonFit` stated without the three. It is for files that import this one and have
the first form. L (an `HolographicProtocol I X`, Hiop/RecInterface.lean), the provers hT, hL and Fm, the falls, W,
S, Yes and the four bounds are free parameters.

  `honFit_noneAside`: from `HonFit` at the provers `proversOf hT hL Fm`, at the falls FT and FB
    guarded by `asideOf` of all seeds and the link's falls FL, with `asideOf` of all seeds as the
    seeds set aside: `HonFit` at the same provers, at FT, FL and FB themselves, with the empty set
    as the seeds set aside. W, S, Yes and the bounds ζ, pT, pL and pO are the same in both
  `asideOf_all`: `asideOf` at the set of all seeds is the empty set, at every index and every
    committer's randomness
  `guardT_none`: a family of falls of the key file's prover (`FallT`), guarded by the empty set
    (`guardT`; both E2E/KeyBridge.lean), is that family
  `guardFall_none`: the same for a family of falls of the session's prover (`FallB`) and
    `guardFall` (both E2E/BridgeAccept.lean)

By what. The three equations follow from the definitions of `asideOf`, `guardT` and `guardFall`, by
extensionality of functions and of sets; no lemma of this library is called. `honFit_noneAside`
rewrites its hypothesis by the three. `proversOf`: E2E/BridgePrivacy.lean. `fallsOf`:
E2E/BridgeAccept.lean.

Limits. Three equations and one rewriting by them. `HonFit` at the guarded falls is a hypothesis: it
is proved here of no provers. Nothing on completeness, soundness or hiding follows from this file
alone.
-/
import E2E.KeyBridge
import E2E.BridgeSeeds

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open AtPublicFiles.KeyBridge (guardT FallT)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}

/-- `asideOf` at the set of all seeds is empty, at every index and committer's randomness: no seed
is set aside. -/
theorem asideOf_all : asideOf (I := I) (L := L) (fun _ => True) = fun _ _ => ∅ :=
  funext fun _ => funext fun _ => Set.eq_empty_of_forall_notMem fun _ h => h trivial

/-- A family of falls of the key file's prover, guarded by the empty set, is that family. -/
theorem guardT_none (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)) (FT : FallT hT) :
    guardT hT (fun _ _ => ∅) FT = FT :=
  funext fun _ => funext fun _ => funext fun _ =>
    Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨fun h' => h', h⟩⟩

/-- A family of falls of the session's prover, guarded by the empty set, is that family. -/
theorem guardFall_none {Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)} (FB : FallB Fm) :
    guardFall (fun _ _ => ∅) FB = FB :=
  funext fun _ => funext fun _ => funext fun _ => funext fun _ =>
    Set.ext fun _ => ⟨fun h => h.2, fun h => ⟨fun h' => h', h⟩⟩

/-- **`HonFit` with `asideOf` of all seeds, as the guard of the falls and as the seeds set aside,
gives `HonFit` at the falls themselves, with no seed set aside.** -/
theorem honFit_noneAside {hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed)}
    {hL : Honest L.link (I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed))}
    {Fm : Family L.onlineBatch.loc (I × L.EncodingRandomness × L.OutOfDomainSeed)} {FT : FallT hT}
    {FL : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed) → L.Rec × L.Rec → hL.Coin →
      Set (Rho L.link.shape)} {FB : FallB Fm} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {Yes : I → X → Prop} {ζ pT pL pO : ℝ≥0∞}
    (h : HonFit (proversOf hT hL Fm)
      (fallsOf hT hL Fm (guardT hT (asideOf fun _ => True) FT) FL
        (guardFall (asideOf fun _ => True) FB)) W S Yes (asideOf fun _ => True) ζ pT pL pO) :
    HonFit (proversOf hT hL Fm) (fallsOf hT hL Fm FT FL FB) W S Yes (fun _ _ => ∅) ζ pT pL pO := by
  rw [asideOf_all, guardT_none, guardFall_none] at h
  exact h

end AtPublicFiles.Bridge

#print axioms AtPublicFiles.Bridge.asideOf_all
#print axioms AtPublicFiles.Bridge.guardT_none
#print axioms AtPublicFiles.Bridge.guardFall_none
#print axioms AtPublicFiles.Bridge.honFit_noneAside
