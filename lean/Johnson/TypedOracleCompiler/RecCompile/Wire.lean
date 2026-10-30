-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/Wire.lean: the condition `OKC` on the wires of the compiled verifier with a
record (Cms.lean of this folder) can be met, over the second form of the compiler's verifier side
(lean/OnBytes/TypedOracleCompiler/).

After lean/Johnson/RecCompile/Wire.lean.
  (1) `wireOf`, `okc_wireOf`: three lawful wires of the object's own protocols (Test and Link with
      any annotations of their rounds), with one K, three depths of request trees, and the library's
      tagged body of a leaf, give a wire of the carrier with `OKC`.
  (2) `okc_passed`: at the passed object (verifier messages drawn from hash blocks by the library's
      samplers, then proof-of-work bits) the library's own generic wires, carried to the types of
      this form (`Tagged.ofQB`, OnBytes/TypedOracleCompiler/Tagged.lean), meet `OKC`. Test and Link have local
      rounds only there, and the request trees of Test and Link have any depths, 0 among them.
  (3) `seedLaw_of_fibres`: the law of the seed's map from a bound on its fibres.

What this shows: the premises on the wire of the theorems of this folder can be met together at
some wire, so these theorems are not empty on that account.

Limits: a wire that `Tagged.ofQB` yields has at most one tree for a component of a round. No wire
with two trees for a component, and none at an annotation of Test or Link with shared rounds, is
made here: (1) takes such wires, (2) makes none. The law `S.OK` of the record's code is a premise of
(1) and of (2): no `OutOfDomainSampleQueryLayout` that has it is made (the limits of Cms.lean).

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.Pass
import OnBytes.TypedOracleCompiler.Tagged
import Johnson.RecCompile.Wire

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchWireDrawOK
open TypedOracleCompiler.Tagged (Body0 prjSym prjSym_emb ofQB ofQB_okg)
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- Three wires of the object's own protocols, as a wire of the carrier, with the library's tagged
body of a leaf. -/
def wireOf {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} (K : ℕ)
    (wT : ProtocolQueryLayout lam K (batTC L aT)) (wL : ProtocolQueryLayout lam K (batLC L aL)) (wB : ProtocolQueryLayout lam K L.onlineBatch)
    (depth depthReq depthReqT depthReqL : ℕ) :
    QueryLayout lam (typedOracleCarrier L (Body0 L.carrierC) aT aL) where
  K := K
  T := ⟨wT.sh, wT.ext, wT.decO, wT.nOpen, wT.maxDepth⟩
  Lk := ⟨wL.sh, wL.ext, wL.decO, wL.nOpen, wL.maxDepth⟩
  B := ⟨wB.sh, wB.ext, wB.decO, wB.nOpen, wB.maxDepth⟩
  depth := depth
  depthReq := depthReq
  depthReqT := depthReqT
  depthReqL := depthReqL
  embE := fun s => (some (.inl s) : Body0 L.carrierC)
  prjE := fun (b : Body0 L.carrierC) => match b with
    | some (.inl s) => some s
    | _ => none
  embT := fun p a => (some (.inr ⟨Tag.test, ⟨p, a⟩⟩) : Body0 L.carrierC)
  prjT := prjSym (L := L.carrierC) Tag.test
  embL := fun p a => (some (.inr ⟨Tag.link, ⟨p, a⟩⟩) : Body0 L.carrierC)
  prjL := prjSym (L := L.carrierC) Tag.link
  embB := fun p a => (some (.inr ⟨Tag.onl, ⟨p, a⟩⟩) : Body0 L.carrierC)
  prjB := prjSym (L := L.carrierC) Tag.onl

theorem okc_wireOf {L : HolographicProtocol I X} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape} {K : ℕ}
    {wT : ProtocolQueryLayout lam K (batTC L aT)} {wL : ProtocolQueryLayout lam K (batLC L aL)} {wB : ProtocolQueryLayout lam K L.onlineBatch}
    {depth depthReq depthReqT depthReqL : ℕ}
    (S : OutOfDomainSampleQueryLayout lam K L (Body0 L.carrierC) aT aL) (hT : wT.OKG) (hL : wL.OKG) (hB : wB.OKG)
    (fits : L.wordLength ≤ 2 ^ depth) (slots : L.maxBatchSize = 2 ^ depthReq)
    (extDepth : wT.ext.depth = depth ∧ wL.ext.depth = depth ∧ wB.ext.depth = depth)
    (depthT : depth ≤ wT.maxDepth) (depthL : depth ≤ wL.maxDepth) (depthB : depth ≤ wB.maxDepth)
    (extT : ∀ p, wT.ext.which p = 0 ∧ wT.ext.leaf p = p.val)
    (extB : ∀ p, wB.ext.which p = 0 ∧ wB.ext.leaf p = p.val)
    (extL : (∀ p, wL.ext.which (.inl p) = 0 ∧ wL.ext.leaf (.inl p) = p.val) ∧
      (∀ p, wL.ext.which (.inr p) = 1 ∧ wL.ext.leaf (.inr p) = p.val))
    (hS : S.OK) : OKC (wireOf K wT wL wB depth depthReq depthReqT depthReqL) S where
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
      prjE_emb := fun _ => rfl
      prjT_emb := fun p a => prjSym_emb (L := L.carrierC) Tag.test p a
      prjL_emb := fun p a => prjSym_emb (L := L.carrierC) Tag.link p a
      prjB_emb := fun p a => prjSym_emb (L := L.carrierC) Tag.onl p a }
  T := hT
  Lk := hL
  B := hB
  seed := hS

/-- The library's generic wires at the passed object, carried to the types of this form, meet `OKC`.
-/
theorem okc_passed (Nn : Type) [Inhabited Nn] (L : HolographicProtocol I X) (pT : L.offline.shape.IsPoint)
    (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint)
    (dT : L.offline.shape.Draws lam) (dL : L.link.shape.Draws lam) (dB : L.onlineBatch.loc.shape.Draws lam)
    (nT : L.offline.shape.NumPos pT) (nL : L.link.shape.NumPos pL)
    (nB : L.onlineBatch.loc.shape.NumPosB L.onlineBatch.ann pB) (z : L.Symbol)
    (oT oL oB K depthReq depthReqT depthReqL : ℕ)
    (hKT : Shape.Draws.maxB _ dT ≤ K) (hKL : Shape.Draws.maxB _ dL ≤ K)
    (hKB : Shape.Draws.maxB _ dB ≤ K)
    (hoT : ∀ x ρ pl, (L.offline.reads x ρ pl).card + (L.offline.extReads x ρ).card ≤ oT)
    (hoL : ∀ x ρ pl, (L.link.reads x ρ pl).card + (L.link.extReads x ρ).card ≤ oL)
    (hoB : ∀ x ρ pl, (L.onlineBatch.loc.reads x ρ pl).card + (L.onlineBatch.loc.extReads x ρ).card ≤ oB)
    (hN : L.maxBatchSize = 2 ^ depthReq) (D : GrData Nn) (n : ℕ) (hD : D.OK n) (hn : n ≤ lam)
    (gT : GBits (L.pull (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
      (Samplers.ofDraws _ dB)).offline.shape)
    (gL : GBits (L.pull (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
      (Samplers.ofDraws _ dB)).link.shape)
    (gB : GBits (L.pull (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
      (Samplers.ofDraws _ dB)).onlineBatch.loc.shape)
    (hgT : gT.AllLe n) (hgL : gL.AllLe n) (hgB : gB.AllLe n)
    (S : OutOfDomainSampleQueryLayout lam (K + 1) ((L.pull (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
                             (Samplers.ofDraws _ dB)).grind Nn gT gL gB) (Body0 _) (RoundSplits.allLocal _) (RoundSplits.allLocal _))
    (hS : S.OK) :
    OKC (L := (L.pull (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
        (Samplers.ofDraws _ dB)).grind Nn gT gL gB)
      (wireOf (K + 1)
        (ofQB ((_root_.Iop.ProtocolQueryLayout.ofLocalD lam K L.offline pT dT nT (WireE.one L.wordLength L.Symbol z) oT
          (Nat.clog 2 L.wordLength)).grindLocal D gT))
        (ofQB ((_root_.Iop.ProtocolQueryLayout.ofLocalD lam K L.link pL dL nL (WireE.two L.wordLength L.Symbol z) oL
          (Nat.clog 2 L.wordLength)).grindLocal D gL))
        (ofQB ((_root_.Iop.ProtocolQueryLayout.ofDraws lam K L.onlineBatch pB dB nB (WireE.one L.wordLength L.Symbol z) oB
          (Nat.clog 2 L.wordLength)).grind D gB))
        (Nat.clog 2 L.wordLength) depthReq depthReqT depthReqL) S :=
  okc_wireOf S
    (ofQB_okg ((qb_ofLocal_ok lam K L.offline pT dT nT _ oT _ hKT (WireE.one_ok _ _ _)
      hoT).toG.grindLocal hD hn hgT))
    (ofQB_okg ((qb_ofLocal_ok lam K L.link pL dL nL _ oL _ hKL (WireE.two_ok _ _ _)
      hoL).toG.grindLocal hD hn hgL))
    (ofQB_okg ((qb_ofPoint_ok lam K L.onlineBatch pB dB nB _ oB _ hKB (WireE.one_ok _ _ _)
      hoB).toG.grind hD hn hgB))
    (Nat.le_pow_clog (by norm_num) L.wordLength) hN ⟨rfl, rfl, rfl⟩ (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _) (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
    ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩ hS

/-- The law of the seed's map from a bound on its fibres: no exact uniformity. -/
theorem seedLaw_of_fibres {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} {K : ℕ} {S : OutOfDomainSampleQueryLayout lam K L Bd aT aL} {c eR : ℕ} {εs : ℝ≥0∞}
    (hc : ∀ s, cnt (fun a => S.seed a = s) ≤ c) (hrcd : ∀ y, cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (h : ((eR * c : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (Fin K → Dig lam) : ℝ≥0∞)) : S.Law εs := by
  intro y
  refine (pr_unif_le_iff _ _).2 (le_trans (Nat.cast_le.2 ?_) h)
  exact (cnt_comp_le S.seed hc fun s => L.hasCollisionAt y s).trans (Nat.mul_le_mul_right _ (hrcd y))

end TypedOracleCompiler.Compile.Batch.Cms
