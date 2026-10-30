-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/Wire.lean: THE CONDITIONS OKC AND S.Law OF Cms.lean CAN BE MET.
(1) wireOf, okc_wireOf: three wires of the object's TRUE protocols, with one K, give a wire of the
carrier with OKC.
(2) okc_passed: at the passed object (verifier messages drawn from hash blocks by the library's
samplers, then proof-of-work bits) the library's own generic wires (ProtocolQueryLayout.ofLocalD | ofDraws, then
grindLocal | grind) meet OKC: so W.OKG's law «K uniform blocks give a uniform verifier message»
(chal_unif) is met there, whatever the sizes of the object's verifier messages.
(3) seedLaw_of_fibres: if every seed has at most c preimages among the strings of K digests, and a
word has at most eR collision seeds, then S.Law εs as soon as eR · c ≤ εs · 2^(lam K) (as a count of
strings): no exact uniformity.

-/
import Johnson.RecCompile.Pass
import Iop.GrindWire
import Iop.BatchWireDrawOK
import Prob.Bias

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob
open Iop.BatchWireDrawOK
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- Three wires of the object's own protocols, as a wire of the carrier. -/
def wireOf {L : HolographicProtocol I X} (K : ℕ) (wT : ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto L.offline))
    (wL : ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto L.link)) (wB : ProtocolQueryLayout lam K L.onlineBatch)
    (depth depthReq : ℕ) : QueryLayout lam L.carrierC where
  K := K
  T := ⟨wT.sh, wT.ext, wT.decO, wT.nOpen, wT.maxDepth⟩
  Lk := ⟨wL.sh, wL.ext, wL.decO, wL.nOpen, wL.maxDepth⟩
  B := ⟨wB.sh, wB.ext, wB.decO, wB.nOpen, wB.maxDepth⟩
  depth := depth
  depthReq := depthReq

theorem okc_wireOf {L : HolographicProtocol I X} {K : ℕ} {wT : ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto L.offline)}
    {wL : ProtocolQueryLayout lam K (BatchInteractiveOracleProof.ofProto L.link)} {wB : ProtocolQueryLayout lam K L.onlineBatch}
    {depth depthReq : ℕ} (S : OutOfDomainSampleQueryLayout lam K L) (hT : wT.OKG) (hL : wL.OKG) (hB : wB.OKG)
    (fits : L.wordLength ≤ 2 ^ depth) (slots : L.maxBatchSize = 2 ^ depthReq)
    (extDepth : wT.ext.depth = depth ∧ wL.ext.depth = depth ∧ wB.ext.depth = depth)
    (depthT : depth ≤ wT.maxDepth) (depthL : depth ≤ wL.maxDepth) (depthB : depth ≤ wB.maxDepth)
    (extT : ∀ p, wT.ext.which p = 0 ∧ wT.ext.leaf p = p.val)
    (extB : ∀ p, wB.ext.which p = 0 ∧ wB.ext.leaf p = p.val)
    (extL : (∀ p, wL.ext.which (.inl p) = 0 ∧ wL.ext.leaf (.inl p) = p.val) ∧
      (∀ p, wL.ext.which (.inr p) = 1 ∧ wL.ext.leaf (.inr p) = p.val))
    (hS : S.OK) : OKC (wireOf K wT wL wB depth depthReq) S where
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
      extL := extL }
  T := hT
  Lk := hL
  B := hB
  seed := hS

/-- The library's generic wires at the passed object meet OKC. -/
theorem okc_passed (Nn : Type) [Inhabited Nn] (L : HolographicProtocol I X) (pT : L.offline.shape.IsPoint)
    (pL : L.link.shape.IsPoint) (pB : L.onlineBatch.loc.shape.IsPoint)
    (dT : L.offline.shape.Draws lam) (dL : L.link.shape.Draws lam) (dB : L.onlineBatch.loc.shape.Draws lam)
    (nT : L.offline.shape.NumPos pT) (nL : L.link.shape.NumPos pL)
    (nB : L.onlineBatch.loc.shape.NumPosB L.onlineBatch.ann pB) (z : L.Symbol) (oT oL oB K depthReq : ℕ)
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
                             (Samplers.ofDraws _ dB)).grind Nn gT gL gB)) (hS : S.OK) :
    OKC (L := (L.pull (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
        (Samplers.ofDraws _ dB)).grind Nn gT gL gB)
      (wireOf (K + 1)
        ((ProtocolQueryLayout.ofLocalD lam K L.offline pT dT nT (WireE.one L.wordLength L.Symbol z) oT
          (Nat.clog 2 L.wordLength)).grindLocal D gT)
        ((ProtocolQueryLayout.ofLocalD lam K L.link pL dL nL (WireE.two L.wordLength L.Symbol z) oL
          (Nat.clog 2 L.wordLength)).grindLocal D gL)
        ((ProtocolQueryLayout.ofDraws lam K L.onlineBatch pB dB nB (WireE.one L.wordLength L.Symbol z) oB
          (Nat.clog 2 L.wordLength)).grind D gB)
        (Nat.clog 2 L.wordLength) depthReq) S :=
  okc_wireOf S
    ((qb_ofLocal_ok lam K L.offline pT dT nT _ oT _ hKT (WireE.one_ok _ _ _) hoT).toG.grindLocal
      hD hn hgT)
    ((qb_ofLocal_ok lam K L.link pL dL nL _ oL _ hKL (WireE.two_ok _ _ _) hoL).toG.grindLocal
      hD hn hgL)
    ((qb_ofPoint_ok lam K L.onlineBatch pB dB nB _ oB _ hKB (WireE.one_ok _ _ _) hoB).toG.grind hD hn hgB)
    (Nat.le_pow_clog (by norm_num) L.wordLength) hN ⟨rfl, rfl, rfl⟩ (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _) (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
    ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩ hS

/-- The law of the seed's map from a bound on its fibres: no exact uniformity. -/
theorem seedLaw_of_fibres {L : HolographicProtocol I X} {K : ℕ} {S : OutOfDomainSampleQueryLayout lam K L} {c eR : ℕ} {εs : ℝ≥0∞}
    (hc : ∀ s, cnt (fun a => S.seed a = s) ≤ c) (hrcd : ∀ y, cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (h : ((eR * c : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (Fin K → Dig lam) : ℝ≥0∞)) : S.Law εs := by
  intro y
  refine (pr_unif_le_iff _ _).2 (le_trans (Nat.cast_le.2 ?_) h)
  exact (cnt_comp_le S.seed hc fun s => L.hasCollisionAt y s).trans (Nat.mul_le_mul_right _ (hrcd y))

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.okc_passed
#print axioms Compile.Batch.Cms.seedLaw_of_fibres
