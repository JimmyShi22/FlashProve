-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyPlain.lean: at the full size: THE KEY FILE's NAMED HYPOTHESIS ON SOUNDNESS AT EVERY RECORD OF THE FRAME's LETTERS WITH THE DESCRIPTION's OWN DECISION, ON THE PLAIN ROAD: from `keySoundOfFullD_plain` (Johnson/Flat/Dec/PlainAtSizes.lean): no witness, no extractor: for each block
«on the statements with the promise the prover has lost towards: whatever the block puts out stands in Q to the statement in front». The list is said AT THE KEY FILE's OWN DESCRIPTION F.

Why. The road on which the laws' files are to pay is the plain form; the field for the key file in a file of evaluations (AllAt.lean, not in this library) stood at the other road's rule. The rule speaks of a description FK over the RECORDS; a file that evaluates a run lays `F.pull instK`; the laws' files work at F.
Main names. `KeyPlainOwedAtF`: WHAT IS LEFT ON THAT ROAD, AT F: fourteen fields: FIVE FACTS ON VALUES (data · sealed · three heads) · leads₁ leads₂ leads₃ (`EachLeads`: one law a block, and that the promise is handed on) · glues (three implications without any game, at the
chains' ends: ASKED ALONG THE RECORDS ALONE: at `F.pull instK`, as the rule itself asks them) · tie (where the instance's test, the silent rounds' test and THE WHOLE LAST TEST say yes, and the first chain's claim M holds under the first promise: the stored table has a collision at the record's seed or decodes with the record) · three bounds · the number.
`keySound_plain_of_F`: they give `CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl)`: one call, at FK := `F.pull instK`, the gate open. M IS A LETTER OVER THE RECORDS.
Limits. A RULE: NOTHING IS PAID HERE; by report the list has no member. THE LAST TEST STANDS WHOLE IN `tie` ON THIS ROAD (no letter g). The three equations of shapes h₁ h₂ h₃ are letters of the statement: by `shapesOfData` (Johnson/Flat/PlainOfData.lean) they hold at the maker's pieces: not called here.
Over the description's format. Nothing on completeness or hiding.

-/
import Johnson.Top.Fire.Code.SealLastPull
import Johnson.Flat.Dec.TwoSizesAt
import Johnson.Desc.BlockSlot
import Johnson.Flat.Dec.PlainAtSizes

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

/-- **What is left of the key file's hypothesis on the plain road, as it is said at the key file's own description.** -/
structure KeyPlainOwedAtF {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) (depthT : ℕ) (DK : WholeD) (εs : ℝ≥0∞)
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
    (Pl : PPlaces (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂) ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (h₁ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₁)
    (h₂ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₂)
    (h₃ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₃)
    (M : RecFull × (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (L₁ : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (cS : ℝ≥0∞) : Prop where
  data : F.data file = .ok (DK.at frS.P.T.a)
  sealed : F.sealLast = true
  head₁ : F.first.blocksInOrder = c₁ :: k₁
  head₂ : F.shared.blocksInOrder = c₂ :: k₂
  head₃ : F.second.blocksInOrder = c₃ :: k₃
  leads₁ : EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)
  leads₂ : EachLeads Pl.on₂ Pl.Q₂ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)
  leads₃ : EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)
  glues : Glues (atDesc (F.pull instK) (piecesAt (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)) Pl M L₁ L₂
  tie : ∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str) (τ : Tr (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      F.okStart (instK rec) = true →
      silK rec ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msgF τ).2 ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msgJ τ).2 ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msg3 τ).2 = true →
      F.fin (instK rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).in₁ (instK rec), (y, fun _ => [])) → M (rec, y) ((F.pub (instK rec), s₁), z)) →
      (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 ∨ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec ≠ none
  below₁ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁ (DK.at frS.P.T.a).ds₁ h₁) εs
  below₂ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂ (DK.at frS.P.T.a).ds₂ h₂) cS
  number : ((2 ^ depthT : ℕ) : ℝ≥0∞) * cS ≤ εs
  below₃ : Err.Below (errOwn (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃ (DK.at frS.P.T.a).ds₃ h₃) εs

set_option maxHeartbeats 4000000 in
/-- **It gives the key file's hypothesis AT EVERY RECORD OF THE FRAME's LETTERS whose decision on the key file is the description's own behind an open gate.** -/
theorem keySound_plain_of_F {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD)
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
    (Pl : PPlaces (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂) ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (h₁ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₁)
    (h₂ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₂)
    (h₃ : (rowIOR (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃).shape = uLT (ckP .two) (DK.at frS.P.T.a).ds₃)
    (M : RecFull × (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (L₁ : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (cS : ℝ≥0∞)
    (dS : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (hb : b = true) (er : runK = gatedFileDecision b (F.pull instK).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (h : KeyPlainOwedAtF F instK A E rK Tl.depthReqT DK Tl.εs file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Pl h₁ h₂ h₃ M L₁ L₂ cS) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) := by
  subst er
  exact keySoundOfFullD_plain (FK := F.pull instK) file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Pl h₁ h₂ h₃
    M L₁ L₂ dS hb Tl
    h.data ((sealLast_pull instK F).trans h.sealed) h.head₁ h.head₂ h.head₃ h.leads₁ h.leads₂ h.leads₃
    h.glues
    h.tie cS h.below₁ h.below₂ h.number h.below₃

end LPFD

#print axioms LPFD.keySound_plain_of_F
