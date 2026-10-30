-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/Pass.lean: THE TWO PASSES OF THE LIBRARY (verifier messages made
from other values: pull; proof-of-work bits: grind) FOR AN OBJECT WITH RECORDS (Iop.HolographicProtocol), ON
SOUNDNESS's ROAD ONLY, and index binding of the verifier VC (Cms.lean) at the passed object, WITH
WORK COUNTED IN THE ROUNDS (Err.BelowG).
The passes on protocols (InteractiveOracleProof.pull | grind, BatchInteractiveOracleProof.pull | grind) are generic in the type of
instances; so are their lemmas on soundness (InteractiveOracleProof.Sound.pull | grind, sndBKT_pull | sndBKT_grind).
Here they are put together field by field.
NOT HERE: hiding, completeness, reads of the passed object (PropsR's other clauses); a wire of the
passed object's carrier.
The record phase itself is not passed: seed, answer, hasCollisionAt, decodeIndex stay; no work on the seed.
The honest sides written into HolographicProtocol.grind have the library's own form (BatchProtocol.grind,
Iop/BatchGrind.lean:194-212: the interactive honest provers send the fixed nonce; the compiled
prover does the search): so acceptance (Acc) fails at the passed object, and GrFit's clause takes
its place, as in the library.
cms_binding_work takes any samplers with Fib; okc_passed (Wire.lean) stands at Samplers.ofDraws:
whoever joins the two needs (ofDraws d).Fib, from the library's Draws.Good (Shape.Draws.Good.fibS,
Iop/GrindPull.lean:90).

-/
import Johnson.RecCompile.CmsGlue
import Ior.KnowWidePass
import Iop.GrindPull

set_option autoImplicit false

noncomputable section

namespace Iop
open Prob BatchPull BatchGrind
open scoped ENNReal

variable {I X Wn : Type}

namespace HolographicProtocol

/-- The object with all verifier messages of the three protocols made from other values. -/
def pull (L : HolographicProtocol I X) (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape)
    (σB : Samplers L.onlineBatch.loc.shape) : HolographicProtocol I X where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  OutOfDomainSeed := L.OutOfDomainSeed
  OutOfDomainAnswer := L.OutOfDomainAnswer
  honestOutOfDomainAnswer := L.honestOutOfDomainAnswer
  hasCollisionAt := L.hasCollisionAt
  decodeIndex := L.decodeIndex
  offline := L.offline.pull σT
  link := L.link.pull σL
  maxBatchSize := L.maxBatchSize
  onlineBatch := L.onlineBatch.pull σB
  honestOfflineProver := L.honestOfflineProver.pull σT
  honestLinkProver := L.honestLinkProver.pull σL
  honestOnlineBatchProver := L.honestOnlineBatchProver.pull σB
  early := L.early
  late := L.late

/-- The object with proof-of-work bits in the rounds of the three protocols. -/
def grind (Nn : Type) [Inhabited Nn] (L : HolographicProtocol I X) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) : HolographicProtocol I X where
  wordLength := L.wordLength
  Symbol := L.Symbol
  EncodingRandomness := L.EncodingRandomness
  encodeIndex := L.encodeIndex
  OutOfDomainSeed := L.OutOfDomainSeed
  OutOfDomainAnswer := L.OutOfDomainAnswer
  honestOutOfDomainAnswer := L.honestOutOfDomainAnswer
  hasCollisionAt := L.hasCollisionAt
  decodeIndex := L.decodeIndex
  offline := L.offline.grind Nn gT
  link := L.link.grind Nn gL
  maxBatchSize := L.maxBatchSize
  onlineBatch := L.onlineBatch.grind Nn gB
  honestOfflineProver := L.honestOfflineProver.grind gT (GNon.nil Nn _)
  honestLinkProver := L.honestLinkProver.grind gL (GNon.nil Nn _)
  honestOnlineBatchProver := L.honestOnlineBatchProver.grind gB (GNon.nil Nn _)
  early := L.early
  late := L.late

variable {L : HolographicProtocol I X} {Rno : I → X → Wn → Prop}
  {wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn} {eR : ℕ}
  {εT : Err L.offline.shape} {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape}

theorem SoundAtR.pull (h : L.SoundAtR Rno wit eR εT εL εB) {σT : Samplers L.offline.shape}
    {σL : Samplers L.link.shape} {σB : Samplers L.onlineBatch.loc.shape} (hT : σT.Fib) (hL : σL.Fib)
    (hB : σB.Fib) :
    (L.pull σT σL σB).SoundAtR Rno (fun a y τ => wit a y (Tr.push σB τ)) eR
      (Err.pull σT εT) (Err.pull σL εL) (Err.pull σB εB) :=
  ⟨h.noneColl, h.rcd, h.sndT.pull hT, h.sndL.pull hL, fun rec =>
    sndBKT_pull X Wn _ (L.batAt rec) σB hB L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB (h.sndB rec)⟩

theorem SoundAtR.grind (Nn : Type) [Inhabited Nn] (h : L.SoundAtR Rno wit eR εT εL εB)
    (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) :
    (L.grind Nn gT gL gB).SoundAtR Rno (fun a y τ => wit a y (Tr.strip gB τ)) eR
      (Err.grind gT εT) (Err.grind gL εL) (Err.grind gB εB) :=
  ⟨h.noneColl, h.rcd, h.sndT.grind gT, h.sndL.grind gL, fun rec =>
    sndBKT_grind Nn X Wn _ (L.batAt rec) gB L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB (h.sndB rec)⟩

end HolographicProtocol
end Iop

namespace Compile.Batch.Cms
open Iop Rom Prob
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ}

/-- Index binding for the languages from explicit lists. -/
theorem cms_binding_at {ISK : Type} {L : HolographicProtocol I X} (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L)
    (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (hSd : S.Law εs) (hbT : Err.Below εT εs) (hbL : Err.Below εL εs) (hbB : Err.Below εB εs)
    (hl : L.late = none) (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hco : L.onlineBatch.ann.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (FullKey lam L) ISK (RequestProof lam L))
    (hA : A.V = VC W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (extractorC0 W) (epsC W εs) :=
  bindingCAt W S p _ _ εs sub
    (cms_bcs I X Wn lam L W S Rno wit eR εT εL εB εs hS hSd hbT hbL hbB hl hlT hlL hlB hco hW) hW A hA

/-- INDEX BINDING AT THE PASSED OBJECT, WORK COUNTED: L sound with explicit lists; samplers with the
bounds on their fibres;
proof-of-work bits g; every pulled error e_i at most εs · 2^(b_i) · |C_i| (Err.BelowG). -/
theorem cms_binding_work {ISK : Type} (Nn : Type) [Inhabited Nn] (L : HolographicProtocol I X)
    (σT : Samplers L.offline.shape) (σL : Samplers L.link.shape) (σB : Samplers L.onlineBatch.loc.shape)
    (gT : GBits (L.pull σT σL σB).offline.shape) (gL : GBits (L.pull σT σL σB).link.shape)
    (gB : GBits (L.pull σT σL σB).onlineBatch.loc.shape)
    (W : QueryLayout lam ((L.pull σT σL σB).grind Nn gT gL gB).carrierC)
    (S : OutOfDomainSampleQueryLayout lam W.K ((L.pull σT σL σB).grind Nn gT gL gB))
    (p : Params) (Ryes Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w) (hS : L.SoundAtR Rno wit eR εT εL εB)
    (fT : σT.Fib) (fL : σL.Fib) (fB : σB.Fib) (hSd : S.Law εs)
    (hbT : Err.BelowG gT (Err.pull σT εT) εs) (hbL : Err.BelowG gL (Err.pull σL εL) εs)
    (hbB : Err.BelowG gB (Err.pull σB εB) εs)
    (hl : L.late = none) (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal) (hlB : L.onlineBatch.loc.IsLocal)
    (hco : L.onlineBatch.ann.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (spec lam W.K ((L.pull σT σL σB).grind Nn gT gL gB).carrierC) I X Unit
      (FullKey lam ((L.pull σT σL σB).grind Nn gT gL gB)) ISK
      (RequestProof lam ((L.pull σT σL σB).grind Nn gT gL gB)))
    (hA : A.V = VC W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (extractorC0 W) (epsC W εs) :=
  cms_binding_at W S p Ryes Rno _ eR _ _ _ εs sub
    (((hS.pull fT fL fB)).grind Nn gT gL gB) hSd
    ((Err.below_grind_iff gT _ εs).2 hbT) ((Err.below_grind_iff gL _ εs).2 hbL)
    ((Err.below_grind_iff gB _ εs).2 hbB) hl ((hlT.pull σT).grind gT) ((hlL.pull σL).grind gL)
    ((hlB.pull σB).grind gB) (BatchGrind.coherent_grind gB (BatchPull.coherent_pull σB hco)) hW A hA

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.cms_binding_work
