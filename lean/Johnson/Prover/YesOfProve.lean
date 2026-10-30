-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/YesOfProve.lean: the compiled prover's strings are accepted by the three compiled
verifiers of an object with records: `yes_of_prove` (OnBytes/Prover/Main.lean) called at the letters
of the key's test (`verifyOfflineProof`), the link (`verifyLinkProof`) and the session (`verifyOnlineProof`)
(Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean, LinkAns.lean).

Why. These three are the compiled verifier of one slot (verifyOneProtocol) at other letters, by unfolding. So
one theorem on one prover serves the key file, the copy's file and the proof file.
  `proveTA`, `proveLA`, `proveBA`   the compiled prover at the three sets of letters
  `vTA_yes_of_prove`, `vLA_yes_of_prove`, `vBA_yes_of_prove`   each string gets its verifier's yes
      under the same oracle functions, under the premises of OnBytes/Prover/Main.lean; the laws of
      the wires come from `OKA`

Limits: those of OnBytes/Prover/Main.lean: no probability; the strategies are letters; that the
interactive verifier accepts is a premise; the outer trees (ExtAt) are a premise. Nothing new is
shown: three calls. No committer; the two seeds and the stored copy's number, which `verifyAtFullKey` tests
besides, are not spoken of.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAns
import OnBytes.Prover.Main

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom OnBytes.Prover TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)
  (p : Params) (xt : ℕ → TreeK lam (typedOracleCarrier L Bd aT aL)) (co : Coins lam (typedOracleCarrier L Bd aT aL))
  (cap : ℕ → ℕ)

/-- the compiled prover at the letters of the key's test -/
def proveTA (cm : Dig lam) (rec : L.Rec) (y : (oneExternalString L.wordLength L.Symbol).Str) (σ : Strat L.offline.shape Unit) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Res (OneProtocolProof lam (batTC L aT) × Tr L.offline.shape)) :=
  proveX Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) (cmsTA cA cm rec.2)
      rec y xt σ co cap

/-- at the letters of the link -/
def proveLA (cm cm' : Dig lam) (rec rec' : L.Rec) (y : (twoExternalStrings L.wordLength L.Symbol).Str)
    (σ : Strat L.link.shape Unit) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Res (OneProtocolProof lam (batLC L aL) × Tr L.link.shape)) :=
  proveX Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) (cmsLA cA cm cm' rec.2 rec'.2)
    (rec, rec') y xt σ co cap

/-- at the letters of the session -/
def proveBA (cm : Dig lam) (x : X) (rec : L.Rec) (y : (oneExternalString L.wordLength L.Symbol).Str)
    (σ : Strat L.onlineBatch.loc.shape Unit) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (Res (OneProtocolProof lam L.onlineBatch × Tr L.onlineBatch.loc.shape)) :=
  proveX Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) (cmsBA cA cm rec.2) (x, rec) y xt σ co cap

variable (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (hW : OKA W cA)
include hW

/-- **The key's test.** -/
theorem vTA_yes_of_prove (cm : Dig lam) (rec : L.Rec) (y : (oneExternalString L.wordLength L.Symbol).Str)
    (σ : Strat L.offline.shape Unit) (hJ : FewJ L.offline.shape aT (wTC W).sh)
    (h0 : Few0 L.offline.shape aT (wTC W).sh) (hloc : L.offline.IsLocal) (hC : aT.Coherent) (hF : aT.Fmt)
    (hfit : co.Fit p.sMT p.sFS W.depthReqT)
    (hx : ExtAt g p.sMT (wTC W).ext W.embE (cmsTA cA cm rec.2) y xt) (π : OneProtocolProof lam (batTC L aT))
    (τ : Tr L.offline.shape) (hp : (proveTA W cA xt co cap cm rec y σ).det g = .ok (π, τ)) :
    RoundsQueryLayout.pass L.offline.shape aT (wTC W).sh τ.rho = true ∧
      Puts L.offline.shape aT (wTC W).sh (σ.run τ.rho).1 τ ∧ π.plains = τ.plains ∧
      (L.offline.accept rec y τ = true → (verifyOfflineProof W cA p cm rec π).det g = true) :=
  yes_of_prove p.sMT p.sFS Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) W.embE
    W.depthReqT (cmsTA cA cm rec.2) rec y xt σ co cap g hW.T hJ h0 hloc hC hF
    (le_of_eq_of_le hW.base.extDepth.1 hW.base.depthT) hfit hx π τ hp

/-- **The link.** -/
theorem vLA_yes_of_prove (cm cm' : Dig lam) (rec rec' : L.Rec) (y : (twoExternalStrings L.wordLength L.Symbol).Str)
    (σ : Strat L.link.shape Unit) (hJ : FewJ L.link.shape aL (wLC W).sh)
    (h0 : Few0 L.link.shape aL (wLC W).sh) (hloc : L.link.IsLocal) (hC : aL.Coherent) (hF : aL.Fmt)
    (hfit : co.Fit p.sMT p.sFS W.depthReqL)
    (hx : ExtAt g p.sMT (wLC W).ext W.embE (cmsLA cA cm cm' rec.2 rec'.2) y xt)
    (π : OneProtocolProof lam (batLC L aL)) (τ : Tr L.link.shape)
    (hp : (proveLA W cA xt co cap cm cm' rec rec' y σ).det g = .ok (π, τ)) :
    RoundsQueryLayout.pass L.link.shape aL (wLC W).sh τ.rho = true ∧
      Puts L.link.shape aL (wLC W).sh (σ.run τ.rho).1 τ ∧ π.plains = τ.plains ∧
      (L.link.accept (rec, rec') y τ = true → (verifyLinkProof W cA p cm cm' rec rec' π).det g = true) :=
  yes_of_prove p.sMT p.sFS Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) W.embE
    W.depthReqL (cmsLA cA cm cm' rec.2 rec'.2) (rec, rec') y xt σ co cap g hW.Lk hJ h0 hloc hC hF
    (le_of_eq_of_le hW.base.extDepth.2.1 hW.base.depthL) hfit hx π τ hp

/-- **The session.** -/
theorem vBA_yes_of_prove (cm : Dig lam) (x : X) (rec : L.Rec) (y : (oneExternalString L.wordLength L.Symbol).Str)
    (σ : Strat L.onlineBatch.loc.shape Unit) (hJ : FewJ L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh)
    (h0 : Few0 L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh) (hloc : L.onlineBatch.loc.IsLocal)
    (hC : L.onlineBatch.ann.Coherent) (hF : L.onlineBatch.ann.Fmt) (hfit : co.Fit p.sMT p.sFS W.depthReq)
    (hx : ExtAt g p.sMT (wBC W).ext W.embE (cmsBA cA cm rec.2) y xt) (π : OneProtocolProof lam L.onlineBatch)
    (τ : Tr L.onlineBatch.loc.shape) (hp : (proveBA W cA r₀ xt co cap cm x rec y σ).det g = .ok (π, τ)) :
    RoundsQueryLayout.pass L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh τ.rho = true ∧
      Puts L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh (σ.run τ.rho).1 τ ∧ π.plains = τ.plains ∧
      (L.onlineBatch.loc.accept (x, rec) y τ = true → (verifyOnlineProof W cA r₀ p cm x rec π).det g = true) :=
  yes_of_prove p.sMT p.sFS Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) W.embE W.depthReq
    (cmsBA cA cm rec.2) (x, rec) y xt σ co cap g hW.B hJ h0 hloc hC hF
    (le_of_eq_of_le hW.base.extDepth.2.2 hW.base.depthB) hfit hx π τ hp

end TypedOracleCompiler.Compile.Batch.Cms
