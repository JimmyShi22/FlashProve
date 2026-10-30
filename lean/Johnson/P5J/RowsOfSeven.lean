-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/RowsOfSeven.lean: THE ONE LEMMA, FIFTH STOREY: FROM THE SEVEN FIELDS THAT ARE LEFT OF THE PROOF
FILE'S HYPOTHESIS BESIDE THE DATA (`ProofPlainSevenAtF`, Johnson/Flat/Dec/ProofPlainLeft.lean) TO THE
PROOF FILE'S ONE STRUCTURE OF PREMISES (`RowsOfProofFile`). The proof is `proofSound_plain_of_left`'s
own, behind its first line, turned by program at its last call.
WHERE IT PARTS FROM THAT THEOREM: there, where the plan's test says no, nothing is owed (such a
description accepts no proof: `proofSoundOfFullD_of_planOk`). THE STRUCTURE HAS NO SUCH DOOR: so
`F.planOk = true` IS A PREMISE HERE (hp), with the data (hD) and the three lists' first blocks.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.ProofPlainLeft
import Johnson.P5J.RowsAtSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifierAndGoals.AtTheName

set_option maxHeartbeats 4000000 in
/-- **From the seven at named blocks, where the plan's test says yes.** -/
theorem rows_of_seven {X XiP : Type} (F : FileDescription XiP) (instP : X × RecFull → XiP)
    (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DP : WholeD) (rP : RecFull)
    (depthReq : ℕ) (early : X → X) {W : Type}
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (e₁ : (i : ℕ) → (ds : List RDT) → (F.XiPub × F.S₁) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₂ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁) × F.S₂) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (e₃ : (i : ℕ) → (ds : List RDT) → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber).E.Str →
      Iop.Tr (uLT (ckP .two) ds) → W → W)
    (dW wEnd : W)
    (Pl : PPlaces (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (M : (X × RecFull) × (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str →
      (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
    (w₀ : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Cells)
    (kS₂ : RecFull → F.S₂)
    {DK : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK : RecFull} {salt K : ℕ}
    {b : Bool} (hb : b = true)
    {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
    (er : runP = gatedFileDecision b (F.pull instP).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hp' : F.planOk = true) (hD : F.data "proof file" = .ok (DP.at frS.P.T.a))
    (q₁ : F.first.blocksInOrder = c₁ :: k₁) (q₂ : F.shared.blocksInOrder = c₂ :: k₂)
    (q₃ : F.second.blocksInOrder = c₃ :: k₃)
    (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str)
    (g : ProofPlainSevenAtF F instP A E DP rP depthReq early c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd Pl M
      L₁ L₂ w₀ kS₂) :
    ∃ h₁ h₂ h₃, RowsOfProofFile (b := soundnessAnalysisDataAtFullSize Tl)
      (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP)
      { w₀ := w₀
        P := plainP (lettersAt A (relationsAndEncodingOfClaims A E)) DP (front₀ rP) (join₀ rP) ByteArray.empty
          (F.pull instP) (allOf (DP.at frS.P.T.a))
          (piecesAt (ckP .two) (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
            (restCap e₂) (restCap e₃) dW wEnd)
          Pl h₁ h₂ h₃ M L₁ L₂ d
        κ₁ := _
        k₁ := fun b => keyAt Prod.snd (DP.at frS.P.T.a).t₁
          (atDesc (F.pull instP) (piecesAt (ckP .two) (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
            (restCap e₂) (restCap e₃) dW wEnd)).p₂
          (atDesc (F.pull instP) (piecesAt (ckP .two) (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
            (restCap e₂) (restCap e₃) dW wEnd)).l₂ 0
          ((atDesc (F.pull instP) (piecesAt (ckP .two) (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
            (restCap e₂) (restCap e₃) dW wEnd)).in₂ b.1, b.2)
        F₁ := fun rec y => (kS₂ rec, y, fun _ _ => none) } (soundnessAnalysisDataAtFullSize Tl).εs := by
  have hp : (F.pull instP).planOk = true := (FileDescription.pull_planOk instP F).trans hp'
  obtain ⟨h₁, h₂, h₃⟩ := shapesOfData (ckP .two) F "proof file" _ hD (sealLast_of_planOk F hp')
    c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd
  exact ⟨h₁, h₂, h₃, rowsOfFullD_byMake_at (F := (F.pull instP)) "proof file" c₁ k₁ c₂ k₂ c₃ k₃
    (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd Pl
    h₁ h₂ h₃ M L₁ L₂ hb er Tl d w₀ hD
    (sealLast_of_planOk (F.pull instP) hp) q₁ q₂ q₃ g.leads₁ g.leads₂
    (sharedOpens_of_data F "proof file" _ hD) g.leads₃ g.glues g.pubEarly kS₂ g.one g.tie
    (below_atCap₁ (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂)
      (restCap e₃) dW wEnd _ Tl.hε (atCap_restCap _) h₁)
    (below_atCap₂ (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂)
      (restCap e₃) dW wEnd _ Tl.hε (atCap_restCap _) h₂)
    (below_atCap₃ (F.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂)
      (restCap e₃) dW wEnd _ Tl.hε (atCap_restCap _) h₃)⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.rows_of_seven
