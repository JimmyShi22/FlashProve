-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyOfRowsEach.lean (the type of requests is a letter Xr; the conclusion stands at every record Tl of the frame's letters, as in KeyOfRows.lean): at the full size: a rider to KeyOfRows.lean: THE THREE BOUNDS FROM ONE BOUND A BLOCK; the three equations of shapes leave the statement.
Main name. `keySound_of_rows_each`: the five facts on values · `RowsOwed` · `EachBelow εs` at each chain's pieces (every block's own errors, as shares, at most εs) give `CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl)`. CALLED: `keySound_of_rows` ·
`ownBelow` (Johnson/Desc/Sound/BelowOfBlocks.lean).
SO THE KEY FILE's DEBT ON THE PLAIN ROAD IS, BLOCK BY BLOCK: one law (`Keeps`) and one bound; AND, ONCE: two seams · one end · two facts at the first boundary · six facts on values.
Limits. Those of KeyOfRows.lean's head. `Err.Below` counts a round's bad challenges against all its challenges. THE SHARED CHAIN IS HELD AT εs ITSELF: that is enough where the key file's request tree has one leaf (`Tl.depthReqT = 0`, a premise). Nothing says that εs is small.

-/
import Johnson.Top.Fire.Code.KeyOfRows
import Johnson.Desc.Sound.BelowOfBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

set_option maxHeartbeats 4000000 in
/-- **From the key file's rows and one bound a block to its hypothesis on soundness.** -/
theorem keySound_of_rows_each {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) (εs : ℝ≥0∞)
    {W : Type} (file : String)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)
    (data : F.data file = .ok (DK.at frS.P.T.a)) (sealed : F.sealLast = true)
    (head₁ : F.first.blocksInOrder = c₁ :: k₁) (head₂ : F.shared.blocksInOrder = c₂ :: k₂) (head₃ : F.second.blocksInOrder = c₃ :: k₃)
    (on₁ L₁ : ℕ → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₂ L₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₃ L₃ : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (rows : RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃)
    (dS : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)
    (below₁ : EachBelow εs ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁))
    (below₂ : EachBelow εs ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂))
    (below₃ : EachBelow εs ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃))
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (hb : b = true) (er : runK = gatedFileDecision b (F.pull instK).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hd : Tl.depthReqT = 0) (hε : Tl.εs = εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) := by
  obtain ⟨h₁, h₂, h₃, k⟩ := keySound_of_rows F instK A E DK εs file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd data sealed head₁ head₂ head₃
    on₁ L₁ on₂ L₂ on₃ L₃ rows dS
  exact k (ownBelow _ _ _ _ _ εs _ _ _ h₁ below₁) (ownBelow _ _ _ _ _ εs _ _ _ h₂ below₂) (ownBelow _ _ _ _ _ εs _ _ _ h₃ below₃)
    hb er Tl hd hε

end LPFD

#print axioms LPFD.keySound_of_rows_each
