-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/JoinAll.lean: join_conf (Join.lean) WITH ITS WIRE AND ITS SEED'S WIRE BUILT:
no premise on a wire W, on OKC, on Sd or on Sd.Law is left: they are replaced by the data and
numbers from which the library builds its own generic wires (okc_passed, Wire.lean) and by
exists_seedW (SeedBS.lean).
The conclusion: THERE ARE a wire W of the passed object's carrier and a wire Sd of the record, with
OKC, such that every scheme whose verifier is VC W Sd p binds at (queries) · κ₀^K · κ + the birthday
term.
The seed's sampler and the record's code are those of SeedBS.lean: an existence, not the programs'.

-/
import Johnson.RecCompile.Join
import Johnson.RecCompile.SeedBS
import Cond.ObjBounds
import Iop.GrindRecut

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob Hiop
open scoped ENNReal

theorem OutOfDomainSampleQueryLayout.Law.mono {I X : Type} {lam K : ℕ} {L : HolographicProtocol I X} {S : OutOfDomainSampleQueryLayout lam K L} {a b : ℝ≥0∞}
    (h : S.Law a) (hab : a ≤ b) : S.Law b := fun y => (h y).trans hab

/-- The wire of the passed object's carrier, from the library's generic wires. -/
def wireAll {lam : ℕ} (Nn : Type) [Inhabited Nn] {C : ConfigurationWithOutOfDomainSample} (S : SubsR C)
    (dT : S.lhr.offline.shape.Draws lam) (dL : S.lhr.link.shape.Draws lam)
    (dB : S.lhr.onlineBatch.loc.shape.Draws lam)
    (pT : S.lhr.offline.shape.IsPoint) (pL : S.lhr.link.shape.IsPoint)
    (pB : S.lhr.onlineBatch.loc.shape.IsPoint) (nT : S.lhr.offline.shape.NumPos pT)
    (nL : S.lhr.link.shape.NumPos pL) (nB : S.lhr.onlineBatch.loc.shape.NumPosB S.lhr.onlineBatch.ann pB)
    (z : S.lhr.Symbol) (oT oL oB K depthReq : ℕ) (D : GrData Nn) (g : S.Bits) :
    QueryLayout lam (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL) (Samplers.ofDraws _ dB) g).carrierC :=
  wireOf (K + 1)
    ((ProtocolQueryLayout.ofLocalD lam K S.lhr.offline pT dT nT (WireE.one S.lhr.wordLength S.lhr.Symbol z) oT
      (Nat.clog 2 S.lhr.wordLength)).grindLocal D (g.TR.pull _))
    ((ProtocolQueryLayout.ofLocalD lam K S.lhr.link pL dL nL (WireE.two S.lhr.wordLength S.lhr.Symbol z) oL
      (Nat.clog 2 S.lhr.wordLength)).grindLocal D (g.LR.pull _))
    ((ProtocolQueryLayout.ofDraws lam K S.lhr.onlineBatch pB dB nB (WireE.one S.lhr.wordLength S.lhr.Symbol z) oB
      (Nat.clog 2 S.lhr.wordLength)).grind D (g.BR.pull _))
    (Nat.clog 2 S.lhr.wordLength) depthReq

/-- join_conf with the wire named (wireAll) and the seed's wire built; ISK, the type of the prover's
keys, is quantified INSIDE (a scheme built from W has a key type that depends on what is chosen
inside). -/
theorem join_allW {lam : ℕ} (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C)
    (P : S.Nums) (b eR : ℕ) (hC : C.Props b eR) (hS : S.Hyp P)
    -- the samplers of the rounds
    (dT : S.lhr.offline.shape.Draws lam) (dL : S.lhr.link.shape.Draws lam)
    (dB : S.lhr.onlineBatch.loc.shape.Draws lam) (κ₀ : ℝ≥0∞) (h1 : 1 ≤ κ₀)
    (gdT : dT.Good κ₀ _) (gdL : dL.Good κ₀ _) (gdB : dB.Good κ₀ _) (K : ℕ)
    (hKT : Shape.Draws.maxB _ dT ≤ K) (hKL : Shape.Draws.maxB _ dL ≤ K)
    (hKB : Shape.Draws.maxB _ dB ≤ K)
    -- the data of the generic wires
    (pT : S.lhr.offline.shape.IsPoint) (pL : S.lhr.link.shape.IsPoint)
    (pB : S.lhr.onlineBatch.loc.shape.IsPoint) (nT : S.lhr.offline.shape.NumPos pT)
    (nL : S.lhr.link.shape.NumPos pL) (nB : S.lhr.onlineBatch.loc.shape.NumPosB S.lhr.onlineBatch.ann pB)
    (z : S.lhr.Symbol) (oT oL oB depthReq : ℕ)
    (hoT : ∀ x ρ pl, (S.lhr.offline.reads x ρ pl).card + (S.lhr.offline.extReads x ρ).card ≤ oT)
    (hoL : ∀ x ρ pl, (S.lhr.link.reads x ρ pl).card + (S.lhr.link.extReads x ρ).card ≤ oL)
    (hoB : ∀ x ρ pl, (S.lhr.onlineBatch.loc.reads x ρ pl).card + (S.lhr.onlineBatch.loc.extReads x ρ).card ≤ oB)
    (hN : S.lhr.maxBatchSize = 2 ^ depthReq)
    -- the work
    (D : GrData Nn) (n : ℕ) (hD : D.OK n) (hn : n ≤ lam) (g : S.Bits)
    (hgw : g.wf.AllLe n) (hgo : g.linOff.AllLe n) (hgl : g.link.AllLe n) (hgr : g.req.AllLe n)
    (hgn : g.linOn.AllLe n) (κ : ℝ≥0∞) (hG : P.BelowG g κ)
    -- the seed
    [Countable S.lhr.Rec] (sT : S.lhr.offline.shape ≠ []) (sL : S.lhr.link.shape ≠ [])
    (sB : S.lhr.onlineBatch.loc.shape ≠ []) (k e : ℕ) (c : ℝ≥0∞) (hk : k ≤ K + 1)
    (he : Fintype.card C.Seed * 2 ^ e ≤ 2 ^ (lam * k))
    (hc : (eR : ℝ≥0∞) ≤ c * (Fintype.card C.Seed : ℝ≥0∞))
    (hcκ : (1 + (2 ^ e : ℝ≥0∞)⁻¹) * c ≤ κ₀ ^ K * κ) :
    ∃ Sd : OutOfDomainSampleQueryLayout lam (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g).K (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL) (Samplers.ofDraws _ dB) g),
      OKC (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g) Sd ∧
      ∀ (ISK : Type) (p : Params)
        (A : ZKCP.Gen.Arg (spec lam (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g).K (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL) (Samplers.ofDraws _ dB) g).carrierC) C.I C.X Unit
          (FullKey lam (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL) (Samplers.ofDraws _ dB) g)) ISK (RequestProof lam (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL) (Samplers.ofDraws _ dB) g))),
        A.V = VC (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g) Sd p →
        ZKCP.Gen.HasIndexBindingWith
          (relPair (fun i x => ∃ w, C.Ryes i x w) (fun i x => ∃ w, C.Rno i x w)
            fun i x ⟨w, hw⟩ => ⟨w, hC.sub i x w hw⟩)
          A (extractorC0 (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g)) (epsC (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g) (κ₀ ^ K * κ)) := by
  have hne : ∀ {s : Shape} (σ : Samplers s) (gg : GBits (s.pull σ)), s ≠ [] →
      (s.pull σ).grind Nn gg ≠ [] := by
    intro s σ gg hs
    cases s with
    | nil => exact absurd rfl hs
    | cons r s => exact fun h => by cases h
  haveI : Countable (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
      (Samplers.ofDraws _ dB) g).Rec := inferInstanceAs (Countable S.lhr.Rec)
  obtain ⟨Sd, hSd, hLaw⟩ := exists_seedW (lam := lam)
    (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL) (Samplers.ofDraws _ dB) g)
    (hne _ _ sT) (hne _ _ sL) (hne _ _ sB) (K + 1) k e eR c hk he hC.rcd hc
  have hOK : OKC (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g) Sd :=
    okc_passed Nn S.lhr pT pL pB dT dL dB nT nL nB z oT oL oB K depthReq hKT hKL hKB
      hoT hoL hoB hN D n hD hn (g.TR.pull _) (g.LR.pull _) (g.BR.pull _)
      (GBits.AllLe.pull _ ((GBits.allLe_app g.wf g.linOff).2 ⟨hgw, hgo⟩))
      (GBits.AllLe.pull _ hgl)
      (GBits.AllLe.pull _ ((GBits.allLe_app g.req g.linOn).2 ⟨hgr, hgn⟩)) Sd hSd
  exact ⟨Sd, hOK, fun ISK p A hA =>
    join_conf Nn C S P b eR hC hS _ _ _ (κ₀ ^ K) _ _ _
      (drawsGood lam κ₀ h1 _ dT gdT K _ hKT le_rfl) (drawsGood lam κ₀ h1 _ dL gdL K _ hKL le_rfl)
      (drawsGood lam κ₀ h1 _ dB gdB K _ hKB le_rfl) g κ hG (wireAll Nn S dT dL dB pT pL pB nT nL nB z oT oL oB K depthReq D g) Sd p (hLaw.mono hcκ) hOK A hA⟩

theorem join_all {lam : ℕ} (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C)
    (P : S.Nums) (b eR : ℕ) (hC : C.Props b eR) (hS : S.Hyp P)
    -- the samplers of the rounds
    (dT : S.lhr.offline.shape.Draws lam) (dL : S.lhr.link.shape.Draws lam)
    (dB : S.lhr.onlineBatch.loc.shape.Draws lam) (κ₀ : ℝ≥0∞) (h1 : 1 ≤ κ₀)
    (gdT : dT.Good κ₀ _) (gdL : dL.Good κ₀ _) (gdB : dB.Good κ₀ _) (K : ℕ)
    (hKT : Shape.Draws.maxB _ dT ≤ K) (hKL : Shape.Draws.maxB _ dL ≤ K)
    (hKB : Shape.Draws.maxB _ dB ≤ K)
    -- the data of the generic wires
    (pT : S.lhr.offline.shape.IsPoint) (pL : S.lhr.link.shape.IsPoint)
    (pB : S.lhr.onlineBatch.loc.shape.IsPoint) (nT : S.lhr.offline.shape.NumPos pT)
    (nL : S.lhr.link.shape.NumPos pL) (nB : S.lhr.onlineBatch.loc.shape.NumPosB S.lhr.onlineBatch.ann pB)
    (z : S.lhr.Symbol) (oT oL oB depthReq : ℕ)
    (hoT : ∀ x ρ pl, (S.lhr.offline.reads x ρ pl).card + (S.lhr.offline.extReads x ρ).card ≤ oT)
    (hoL : ∀ x ρ pl, (S.lhr.link.reads x ρ pl).card + (S.lhr.link.extReads x ρ).card ≤ oL)
    (hoB : ∀ x ρ pl, (S.lhr.onlineBatch.loc.reads x ρ pl).card + (S.lhr.onlineBatch.loc.extReads x ρ).card ≤ oB)
    (hN : S.lhr.maxBatchSize = 2 ^ depthReq)
    -- the work
    (D : GrData Nn) (n : ℕ) (hD : D.OK n) (hn : n ≤ lam) (g : S.Bits)
    (hgw : g.wf.AllLe n) (hgo : g.linOff.AllLe n) (hgl : g.link.AllLe n) (hgr : g.req.AllLe n)
    (hgn : g.linOn.AllLe n) (κ : ℝ≥0∞) (hG : P.BelowG g κ)
    -- the seed
    [Countable S.lhr.Rec] (sT : S.lhr.offline.shape ≠ []) (sL : S.lhr.link.shape ≠ [])
    (sB : S.lhr.onlineBatch.loc.shape ≠ []) (k e : ℕ) (c : ℝ≥0∞) (hk : k ≤ K + 1)
    (he : Fintype.card C.Seed * 2 ^ e ≤ 2 ^ (lam * k))
    (hc : (eR : ℝ≥0∞) ≤ c * (Fintype.card C.Seed : ℝ≥0∞))
    (hcκ : (1 + (2 ^ e : ℝ≥0∞)⁻¹) * c ≤ κ₀ ^ K * κ) :
    ∃ (W : QueryLayout lam (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
                (Samplers.ofDraws _ dB) g).carrierC)
      (Sd : OutOfDomainSampleQueryLayout lam W.K (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
                                 (Samplers.ofDraws _ dB) g)),
      OKC W Sd ∧
      ∀ (ISK : Type) (p : Params)
        (A : ZKCP.Gen.Arg (spec lam W.K (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
            (Samplers.ofDraws _ dB) g).carrierC) C.I C.X Unit
          (FullKey lam (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
               (Samplers.ofDraws _ dB) g)) ISK
          (RequestProof lam (S.lhrW Nn (Samplers.ofDraws _ dT) (Samplers.ofDraws _ dL)
                    (Samplers.ofDraws _ dB) g))),
        A.V = VC W Sd p →
        ZKCP.Gen.HasIndexBindingWith
          (relPair (fun i x => ∃ w, C.Ryes i x w) (fun i x => ∃ w, C.Rno i x w)
            fun i x ⟨w, hw⟩ => ⟨w, hC.sub i x w hw⟩)
          A (extractorC0 W) (epsC W (κ₀ ^ K * κ)) :=
  let ⟨Sd, h1', h2'⟩ := join_allW Nn C S P b eR hC hS dT dL dB κ₀ h1 gdT gdL gdB K hKT hKL hKB pT pL pB nT nL nB z oT oL oB depthReq hoT hoL hoB hN D n hD hn g hgw hgo hgl hgr hgn κ hG sT sL sB k e c hk he hc hcκ
  ⟨_, Sd, h1', h2'⟩

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.join_allW
#print axioms Compile.Batch.Cms.join_all
