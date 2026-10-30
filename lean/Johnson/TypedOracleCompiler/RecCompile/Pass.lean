-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/Pass.lean: index binding of the verifier `VC` (Cms.lean of this folder) at an
object with records that has gone through the library's two passes (verifier messages made from
other values: pull; proof-of-work bits: grind), with work counted in the rounds (`Err.BelowG`).

After lean/Johnson/RecCompile/Pass.lean. That file's first part (`Iop.HolographicProtocol.pull`, `Iop.HolographicProtocol.grind` and
their lemmas on soundness) speaks of the object alone and is used as it lies. Here are its two
theorems on the compiled verifier, `cms_binding_at` and `cms_binding_work`, in that file's words.

The annotations of Test and Link (`aT`, `aL`) are letters at the passed object's shapes.
`cms_binding_work` is for a wire whose request trees at Test and at Link have depth 0 (hypotheses
`hdT`, `hdL`: one slot); then the errors of their shared rounds count once. `cms_binding_at` is for
every depth. What depth 0 asks of a proof string (`verifyOneProtocol`,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean): its field slot is 0, and its path in the request tree is
empty. Where no round is shared, nothing else reads the depth.

Limits: soundness' road alone. No wire of the passed object's carrier is made here: `OKC W S` is a
hypothesis. Wire.lean of this folder makes one (`okc_passed`), with local rounds alone in Test and
Link and at most one tree for a component; the limits of Cms.lean tell what is not shown. The like
of `cms_binding_work` at the verifier with the answers alone in each first query, at the key (root,
record): `cmsRA_binding_work` (FrontRootAns.lean).

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsGlue
import Johnson.RecCompile.Pass

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {Bd : Type}

/-- Index binding for the languages from explicit lists. -/
theorem cms_binding_at {ISK : Type} {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (hSd : S.Law εs) (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hbB : Err.Below εB εs)
    (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hcT : aT.Coherent) (hcL : aL.Coherent) (hco : L.onlineBatch.ann.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL) ISK (RequestProof lam
                                  L))
    (hA : A.V = VC W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (extractorC0 W) (epsC W εs) :=
  bindingCAt W S p _ _ εs sub
    (cms_bcs I X Wn lam L Bd aT aL W S Rno wit eR εT εL εB εs hS hSd hbT hbL hbB hlT hlL hlB hcT hcL
      hco hW) hW A hA

/-- Index binding at the passed object, work counted: L sound with explicit lists; samplers with the
bounds on their fibres; proof-of-work bits g; every pulled error e_i at most εs · 2^(b_i) · |C_i|
(Err.BelowG). -/
theorem cms_binding_work {ISK : Type} (Nn : Type) [Inhabited Nn] (L : HolographicProtocol I X)
    (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape)
    (gT : GBits (L.pull σT σL σB).offline.shape) (gL : GBits (L.pull σT σL σB).link.shape)
    (gB : GBits (L.pull σT σL σB).onlineBatch.loc.shape)
    (aT : RoundSplits ((L.pull σT σL σB).grind Nn gT gL gB).offline.shape)
    (aL : RoundSplits ((L.pull σT σL σB).grind Nn gT gL gB).link.shape)
    (W : QueryLayout lam (typedOracleCarrier ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL)
    (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (fT : σT.Fib) (fL : σL.Fib) (fB : σB.Fib) (hSd : S.Law εs)
    (hbT : Err.BelowG gT (Err.pull σT εT) εs) (hbL : Err.BelowG gL (Err.pull σL εL) εs)
    (hbB : Err.BelowG gB (Err.pull σB εB) εs)
    (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hcT : aT.Coherent) (hcL : aL.Coherent) (hco : L.onlineBatch.ann.Coherent)
    (hdT : W.depthReqT = 0) (hdL : W.depthReqL = 0) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier ((L.pull σT σL σB).grind Nn gT gL gB) Bd aT aL)) I X
        Unit
      (FullKey lam ((L.pull σT σL σB).grind Nn gT gL gB) aT aL) ISK
      (RequestProof lam ((L.pull σT σL σB).grind Nn gT gL gB)))
    (hA : A.V = VC W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (extractorC0 W) (epsC W εs) :=
  cms_binding_at W S p Ryes Rno _ eR _ _ _ εs sub
    (((hS.pull fT fL fB)).grind Nn gT gL gB) hSd
    (by rw [hdT, pow_zero, timesShared_one]; exact (Err.below_grind_iff gT _ εs).2 hbT)
    (by rw [hdL, pow_zero, timesShared_one]; exact (Err.below_grind_iff gL _ εs).2 hbL)
    ((Err.below_grind_iff gB _ εs).2 hbB) ((hlT.pull σT).grind gT) ((hlL.pull σL).grind gL)
    ((hlB.pull σB).grind gB) hcT hcL
    (BatchGrind.coherent_grind gB (BatchPull.coherent_pull σB hco)) hW A hA

end TypedOracleCompiler.Compile.Batch.Cms
