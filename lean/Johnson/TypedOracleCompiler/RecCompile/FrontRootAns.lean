-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean: the key is (root, record) alone, over the compiled
verifier with the answers alone in each chain's first query (`verifyAtFullKey`, CmsAns.lean).

After FrontRoot.lean of this folder: its `KeyRoot`, `OfflineLinkOnlineProof`, `indexExtractorAtRootAndOutOfDomainSample`, `bindingR_one` are
used as they stand.
Main names:
  `verifyAtKeyRoot W S cA r₀ p k x π`: `verifyAtFullKey` fed from the key (root, record) and the proof.
  `VCA_binding_at`: index binding at the whole key. `cmsRA_binding_at`: at the key (root, record).
  `cmsRA_binding_work`: the same at the passed object, work counted.
  `epsA_sum`: the bound depends on the sum of the two budgets.
Each is for every committer and every prover, at the bound `soundnessBoundOverTypedOracles` (CmsAnsPr.lean).
Limits: soundness alone; typed oracles.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAnsPr

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

/-- The verifier at the key (root, record). -/
def verifyAtKeyRoot (p : Params) (k : KeyRoot lam L) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyAtFullKey W S cA r₀ p (k.full π) x π.low

theorem detBound_VRA (p : Params) (k : KeyRoot lam L) (x : X) (π : OfflineLinkOnlineProof lam L aT aL) :
    DetBound (verifyAtKeyRoot W S cA r₀ p k x π) (tVC W) := detBound_VCA W S cA r₀ p (k.full π) x π.low

theorem epsA_sum (c : ℝ≥0∞) (tC tP : ℕ) : soundnessBoundOverTypedOracles W c tC tP = soundnessBoundOverTypedOracles W c (tC + tP) 0 := by
  simp only [soundnessBoundOverTypedOracles, Nat.add_zero]

/-- Index binding at the whole key, of every scheme whose verifier is `verifyAtFullKey W S cA r₀ p`, for every
committer and prover, at `soundnessBoundOverTypedOracles W εs`. Under the premises of `cmsA_bcs` (CmsAns.lean): `SoundAtR` at
explicit lists of errors; `S.Law εs`; the three bounds on the rounds' errors; the three verifiers
read their oracles at the declared positions alone (`IsLocal`); the three lists of marks are
coherent; `OKA`. And under: an instance that is true for the first relation is true for the relaxed
one. The extractor `extractorC0 W` is `extractorG W FullKey.cm FullKey.rcd` (CmsAnsPr.lean) by unfolding.
-/
theorem VCA_binding_at {ISK : Type} (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (hSd : S.Law εs) (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hbB : Err.Below εB εs)
    (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hcT : aT.Coherent) (hcL : aL.Coherent) (hco : L.onlineBatch.ann.Coherent) (hW : OKA W cA)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL) ISK
      (RequestProof lam L))
    (hA : A.V = verifyAtFullKey W S cA r₀ p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (extractorC0 W) (soundnessBoundOverTypedOracles W εs) :=
  cmsA_binding_at W S cA r₀ (fun k _ => k) id FullKey.cm FullKey.rcd (fun _ _ => rfl) (fun _ _ => rfl)
    p Ryes Rno wit eR εT εL εB εs sub hS hSd hbT hbL hbB hlT hlL hlB hcT hcL hco hW A hA

/-- Index binding at the key (root, record), of every scheme whose verifier is `verifyAtKeyRoot W S cA r₀ p`,
for every committer and prover, at `soundnessBoundOverTypedOracles W εs`. Under the premises of `VCA_binding_at`. No premise
on the depth of a request tree: a shared round's error is counted once for each leaf. -/
theorem cmsRA_binding_at {ISK : Type} (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (hSd : S.Law εs) (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hbB : Err.Below εB εs)
    (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hcT : aT.Coherent) (hcL : aL.Coherent) (hco : L.onlineBatch.ann.Coherent) (hW : OKA W cA)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (KeyRoot lam L) ISK
      (OfflineLinkOnlineProof lam L aT aL))
    (hA : A.V = verifyAtKeyRoot W S cA r₀ p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (indexExtractorAtRootAndOutOfDomainSample W) (soundnessBoundOverTypedOracles W εs) :=
  cmsA_binding_at W S cA r₀ KeyRoot.full OfflineLinkOnlineProof.low KeyRoot.cm KeyRoot.rcd (fun _ _ => rfl)
    (fun _ _ => rfl) p Ryes Rno wit eR εT εL εB εs sub hS hSd hbT hbL hbB hlT hlL hlB hcT hcL hco
    hW A hA

/-- Index binding at the passed object, work counted, the key being (root, record), the answers
alone in each first query, of every scheme whose verifier is `verifyAtKeyRoot W S cA r₀ p`: the statement of
`cmsR_binding_work` with `verifyAtKeyRoot`, `OKA`, `soundnessBoundOverTypedOracles`. Under: `SoundAtR` of the object before the two
passes; the samplers' law `Fib`; `S.Law εs`; every round's error behind the passes, its work
counted, at most εs; the three verifiers read their oracles at the declared positions alone
(`IsLocal`); the marks are coherent; BOTH REQUEST TREES, THE KEY's TEST's AND THE LINK's, OF DEPTH 0
(`hdT`, `hdL`); `OKA`. And under: an instance that is true for the first relation is true for the
relaxed one. -/
theorem cmsRA_binding_work {I X Wn : Type} {lam : ℕ} {ISK Bd : Type} (Nn : Type) [Inhabited Nn]
    (L : HolographicProtocol I X)
    (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape)
    (gT : GBits (L.pull σT σL σB).offline.shape) (gL : GBits (L.pull σT σL σB).link.shape)
    (gB : GBits (L.pull σT σL σB).onlineBatch.loc.shape)
    (aT : RoundSplits ((L.pull σT σL σB).grind Nn gT gL gB).offline.shape)
    (aL : RoundSplits ((L.pull σT σL σB).grind Nn gT gL gB).link.shape)
    (W : QueryLayout lam (typedOracleCarrier ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL)
    (cA : ((L.pull σT σL σB).grind Nn gT gL gB).OutOfDomainAnswer → List (Dig lam))
    (r₀ : ((L.pull σT σL σB).grind Nn gT gL gB).Rec)
    (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (fT : σT.Fib) (fL : σL.Fib) (fB : σB.Fib) (hSd : S.Law εs)
    (hbT : Err.BelowG gT (Err.pull σT εT) εs) (hbL : Err.BelowG gL (Err.pull σL εL) εs)
    (hbB : Err.BelowG gB (Err.pull σB εB) εs)
    (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hcT : aT.Coherent) (hcL : aL.Coherent) (hco : L.onlineBatch.ann.Coherent)
    (hdT : W.depthReqT = 0) (hdL : W.depthReqL = 0) (hW : OKA W cA)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL)) I X
      Unit (KeyRoot lam ((L.pull σT σL σB).grind Nn gT gL gB)) ISK
      (OfflineLinkOnlineProof lam ((L.pull σT σL σB).grind Nn gT gL gB) aT aL))
    (hA : A.V = verifyAtKeyRoot W S cA r₀ p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (indexExtractorAtRootAndOutOfDomainSample W) (soundnessBoundOverTypedOracles W εs) :=
  cmsRA_binding_at W S cA r₀ p Ryes Rno _ eR _ _ _ εs sub
    (((hS.pull fT fL fB)).grind Nn gT gL gB) hSd
    (by rw [hdT, pow_zero, timesShared_one]; exact (Err.below_grind_iff gT _ εs).2 hbT)
    (by rw [hdL, pow_zero, timesShared_one]; exact (Err.below_grind_iff gL _ εs).2 hbL)
    ((Err.below_grind_iff gB _ εs).2 hbB) ((hlT.pull σT).grind gT) ((hlL.pull σL).grind gL)
    ((hlB.pull σB).grind gB) hcT hcL
    (BatchGrind.coherent_grind gB (BatchPull.coherent_pull σB hco)) hW A hA

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.VCA_binding_at
#print axioms TypedOracleCompiler.Compile.Batch.Cms.cmsRA_binding_at
#print axioms TypedOracleCompiler.Compile.Batch.Cms.cmsRA_binding_work
