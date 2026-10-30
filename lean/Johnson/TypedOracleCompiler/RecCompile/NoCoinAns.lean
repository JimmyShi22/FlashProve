-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/NoCoinAns.lean: the three compiled verifiers at the answers alone, `verifyOfflineProof`,
`verifyOnlineProof` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean) and `verifyLinkProof` (Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean), and the
verifier with records `verifyAtFullKey` that runs them, draw no coin; so under fixed oracle functions g each has
one value, and that value is `.det g`.



Why. `OComp.det g` (Rom/Cache.lean) is defined for every algorithm: at an algorithm with coins it is
the result of the run in which every sample is 0. So a sentence "`(v ..).det g = true`" says "the
verifier says yes under g" only beside `NoCoin`.

What it states, of each of the three, strict and lax (the names with a prime), and of `verifyAtFullKey`: no path
samples coins (`noCoin_..`); under g the run is the point mass at `.det g` (`runEager_..`); of the
three also: at most `tVQB` queries on every path (`detBound_..`). No definition. No premise: the
statements hold at every wire record W, every record S of the seeds, every code cA of the answers
and all arguments.

Limits: nothing on what the value is. The object L and the wire record W are variables: "Test",
"Link" and "session" are the three protocols of any L; that they are a key file's, an entry file's
and a proof file's is the use that is meant, and is not said here. Nothing on a written file's
verifier (`FileW.verify`, OnBytes/TypedOracleCompiler/Joined/Verifier.lean; `detBound_verifyFile`,
OnBytes/TypedOracleCompiler/Joined/Top.lean, has its bound), nor on the verifier at a root (`verifyAtKeyRoot`,
Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean: `detBound_VRA`), nor on the three typed checks of an input
(`armK`, `armE`, `armP`, Johnson/Top/OnFilesArmsC.lean). g is a family of typed oracle functions;
what ties it to a hash function is not spoken of. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAnsPr
import OnBytes.TypedOracleCompiler.Compile.Batch.OursFirst

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

section Three
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

/-! ## The bound on queries -/

/-- The compiled Test asks at most `tVQB` queries on every path, and draws no coin. -/
theorem detBound_vTA (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    DetBound (verifyOfflineProof W cA p cm rec π) (tVQB (wTC W) W.depthReqT) :=
  detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The same of the lax Test. -/
theorem detBound_vTA' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    DetBound (vTA' W cA cm rec π) (tVQB (wTC W) W.depthReqT) :=
  detBound_verifyB _ _ _ _ _ _ _ _ _ _ _

/-- The same of the compiled Link. -/
theorem detBound_vLA (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec)
    (π : OneProtocolProof lam (batLC L aL)) :
    DetBound (verifyLinkProof W cA p cm cm' rec rec' π) (tVQB (wLC W) W.depthReqL) :=
  detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The same of the lax Link. -/
theorem detBound_vLA' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    DetBound (vLA' W cA cm cm' rec rec' π) (tVQB (wLC W) W.depthReqL) :=
  detBound_verifyB _ _ _ _ _ _ _ _ _ _ _

/-- The same of the compiled session. -/
theorem detBound_vBA (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    DetBound (verifyOnlineProof W cA r₀ p cm x rec π) (tVQB (wBC W) W.depthReq) :=
  detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The same of the lax session. -/
theorem detBound_vBA' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    DetBound (vBA' W cA r₀ cm x rec π) (tVQB (wBC W) W.depthReq) :=
  detBound_verifyB _ _ _ _ _ _ _ _ _ _ _

/-! ## No coin -/

/-- The compiled Test draws no coin. -/
theorem noCoin_vTA (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    (verifyOfflineProof W cA p cm rec π).NoCoin :=
  noCoin_of_detBound (detBound_vTA W cA p cm rec π)

/-- Nor does the lax Test. -/
theorem noCoin_vTA' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    (vTA' W cA cm rec π).NoCoin :=
  noCoin_of_detBound (detBound_vTA' W cA cm rec π)

/-- The compiled Link draws no coin. -/
theorem noCoin_vLA (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec)
    (π : OneProtocolProof lam (batLC L aL)) : (verifyLinkProof W cA p cm cm' rec rec' π).NoCoin :=
  noCoin_of_detBound (detBound_vLA W cA p cm cm' rec rec' π)

/-- Nor does the lax Link. -/
theorem noCoin_vLA' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    (vLA' W cA cm cm' rec rec' π).NoCoin :=
  noCoin_of_detBound (detBound_vLA' W cA cm cm' rec rec' π)

/-- The compiled session draws no coin. -/
theorem noCoin_vBA (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    (verifyOnlineProof W cA r₀ p cm x rec π).NoCoin :=
  noCoin_of_detBound (detBound_vBA W cA r₀ p cm x rec π)

/-- Nor does the lax session. -/
theorem noCoin_vBA' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    (vBA' W cA r₀ cm x rec π).NoCoin :=
  noCoin_of_detBound (detBound_vBA' W cA r₀ cm x rec π)

/-! ## One value under fixed oracle functions -/

/-- Under fixed oracle functions the compiled Test has one value: `.det g`. -/
theorem runEager_vTA (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT))
    (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (verifyOfflineProof W cA p cm rec π).runEager g = PMF.pure ((verifyOfflineProof W cA p cm rec π).det g) :=
  (noCoin_vTA W cA p cm rec π).runEager g

/-- The same of the compiled Link. -/
theorem runEager_vLA (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec)
    (π : OneProtocolProof lam (batLC L aL)) (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (verifyLinkProof W cA p cm cm' rec rec' π).runEager g =
      PMF.pure ((verifyLinkProof W cA p cm cm' rec rec' π).det g) :=
  (noCoin_vLA W cA p cm cm' rec rec' π).runEager g

/-- The same of the compiled session. -/
theorem runEager_vBA (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch)
    (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (verifyOnlineProof W cA r₀ p cm x rec π).runEager g = PMF.pure ((verifyOnlineProof W cA r₀ p cm x rec π).det g) :=
  (noCoin_vBA W cA r₀ p cm x rec π).runEager g

/-- The same of the lax Test. -/
theorem runEager_vTA' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT))
    (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (vTA' W cA cm rec π).runEager g = PMF.pure ((vTA' W cA cm rec π).det g) :=
  (noCoin_vTA' W cA cm rec π).runEager g

/-- The same of the lax Link. -/
theorem runEager_vLA' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL))
    (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (vLA' W cA cm cm' rec rec' π).runEager g = PMF.pure ((vLA' W cA cm cm' rec rec' π).det g) :=
  (noCoin_vLA' W cA cm cm' rec rec' π).runEager g

/-- The same of the lax session. -/
theorem runEager_vBA' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch)
    (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (vBA' W cA r₀ cm x rec π).runEager g = PMF.pure ((vBA' W cA r₀ cm x rec π).det g) :=
  (noCoin_vBA' W cA r₀ cm x rec π).runEager g

end Three

/-! ## The verifier with records -/

section Whole
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

/-- The verifier with records draws no coin. -/
theorem noCoin_VCA (p : Params) (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) :
    (verifyAtFullKey W S cA r₀ p v x π).NoCoin :=
  noCoin_of_detBound (detBound_VCA W S cA r₀ p v x π)

/-- Under fixed oracle functions it has one value: `.det g`. -/
theorem runEager_VCA (p : Params) (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L)
    (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) :
    (verifyAtFullKey W S cA r₀ p v x π).runEager g = PMF.pure ((verifyAtFullKey W S cA r₀ p v x π).det g) :=
  (noCoin_VCA W S cA r₀ p v x π).runEager g

end Whole

end TypedOracleCompiler.Compile.Batch.Cms
