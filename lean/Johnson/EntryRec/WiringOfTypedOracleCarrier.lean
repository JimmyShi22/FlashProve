-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/WiringOfTypedOracleCarrier.lean: three wire records of an object's own protocols as one wiring of
the carrier of the typed oracles, over the second form of the compiler's verifier side
(OnBytes/TypedOracleCompiler/), and the laws of the wires that Johnson/TypedOracleCompiler/RecCompile/Cms.lean asks (`OKC`).

After Johnson/RecCompile/Wire.lean's `wireOf` and `okc_wireOf`, in that file's words. What
differs: the wire records have lists of trees; Test and Link stand with their annotations (`batTC L
aT`, `batLC L aL`); each of the three calls has its own depth of the request tree; how a symbol is
written into the body of a leaf, and read back, are eight letters of the wiring (`Bodies`).

  `Bodies L Bd`: these eight letters. `Bodies.OK`: what is written is read back.
  `wireOf2`: the wiring. `okc_wireOf2`: `OKC`, for every object with records, every type of bodies
    and every two annotations.

Limits. Nothing on a verifier, and nothing on any particular object.

-/
import Johnson.TypedOracleCompiler.RecCompile.Cms

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ}

/-- How a symbol is written into the body of a leaf, and read back: a symbol of an encoded index, of
a prover's oracle of Test, of Link, of the session. -/
structure Bodies (L : HolographicProtocol I X) (Bd : Type) where
  embE : L.Symbol → Bd
  prjE : Bd → Option L.Symbol
  embT : (p : OPos L.offline.shape) → OSym L.offline.shape p → Bd
  prjT : (p : OPos L.offline.shape) → Bd → Option (OSym L.offline.shape p)
  embL : (p : OPos L.link.shape) → OSym L.link.shape p → Bd
  prjL : (p : OPos L.link.shape) → Bd → Option (OSym L.link.shape p)
  embB : (p : OPos L.onlineBatch.loc.shape) → OSym L.onlineBatch.loc.shape p → Bd
  prjB : (p : OPos L.onlineBatch.loc.shape) → Bd → Option (OSym L.onlineBatch.loc.shape p)

/-- What is written into a body is read back. -/
structure Bodies.OK {L : HolographicProtocol I X} {Bd : Type} (b : Bodies L Bd) : Prop where
  E : ∀ s, b.prjE (b.embE s) = some s
  T : ∀ p a, b.prjT p (b.embT p a) = some a
  L : ∀ p a, b.prjL p (b.embL p a) = some a
  B : ∀ p a, b.prjB p (b.embB p a) = some a

/-- **Three wire records of the object's own protocols, as a wiring of the carrier.** -/
def wireOf2 {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} (K : ℕ)
    (wT : ProtocolQueryLayout lam K (batTC L aT)) (wL : ProtocolQueryLayout lam K (batLC L aL)) (wB : ProtocolQueryLayout lam K L.onlineBatch)
    (depth depthReq depthReqT depthReqL : ℕ) (b : Bodies L Bd) :
    QueryLayout lam (typedOracleCarrier L Bd aT aL) where
  K := K
  T := ⟨wT.sh, wT.ext, wT.decO, wT.nOpen, wT.maxDepth⟩
  Lk := ⟨wL.sh, wL.ext, wL.decO, wL.nOpen, wL.maxDepth⟩
  B := ⟨wB.sh, wB.ext, wB.decO, wB.nOpen, wB.maxDepth⟩
  depth := depth
  depthReq := depthReq
  depthReqT := depthReqT
  depthReqL := depthReqL
  embE := b.embE
  prjE := b.prjE
  embT := b.embT
  prjT := b.prjT
  embL := b.embL
  prjL := b.prjL
  embB := b.embB
  prjB := b.prjB

/-- **The laws of the wires.** -/
theorem okc_wireOf2 {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
    {K : ℕ} {wT : ProtocolQueryLayout lam K (batTC L aT)} {wL : ProtocolQueryLayout lam K (batLC L aL)}
    {wB : ProtocolQueryLayout lam K L.onlineBatch} {depth depthReq depthReqT depthReqL : ℕ} {b : Bodies L Bd}
    (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) (hT : wT.OKG) (hL : wL.OKG) (hB : wB.OKG)
    (fits : L.wordLength ≤ 2 ^ depth) (slots : L.maxBatchSize = 2 ^ depthReq)
    (extDepth : wT.ext.depth = depth ∧ wL.ext.depth = depth ∧ wB.ext.depth = depth)
    (depthT : depth ≤ wT.maxDepth) (depthL : depth ≤ wL.maxDepth) (depthB : depth ≤ wB.maxDepth)
    (extT : ∀ p, wT.ext.which p = 0 ∧ wT.ext.leaf p = p.val)
    (extB : ∀ p, wB.ext.which p = 0 ∧ wB.ext.leaf p = p.val)
    (extL : (∀ p, wL.ext.which (.inl p) = 0 ∧ wL.ext.leaf (.inl p) = p.val) ∧
      (∀ p, wL.ext.which (.inr p) = 1 ∧ wL.ext.leaf (.inr p) = p.val))
    (hb : b.OK) (hS : S.OK) :
    OKC (wireOf2 K wT wL wB depth depthReq depthReqT depthReqL b) S where
  base :=
    { T := ⟨hT.sh, hT.ext, fun _ _ _ => Nat.zero_le _, hT.depth⟩
      Lk := ⟨hL.sh, hL.ext, fun _ _ _ => Nat.zero_le _, hL.depth⟩
      B := ⟨hB.sh, hB.ext, fun _ _ _ => Nat.zero_le _, hB.depth⟩
      fits := fits
      slots := slots
      extDepth := extDepth
      depthT := depthT
      depthL := depthL
      depthB := depthB
      extT := extT
      extB := extB
      extL := extL
      prjE_emb := hb.E
      prjT_emb := hb.T
      prjL_emb := hb.L
      prjB_emb := hb.B }
  T := hT
  Lk := hL
  B := hB
  seed := hS

end TypedOracleCompiler.Compile.Batch.Cms
