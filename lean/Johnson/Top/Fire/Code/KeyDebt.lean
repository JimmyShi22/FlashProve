-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyDebt.lean: at the full size: ON THE PLAIN ROAD: THE KEY FILE's WHOLE DEBT AS ONE PROPOSITION ON A DESCRIPTION F; that proposition asked OVER A SET OF DESCRIPTIONS, a letter; and from it the key file's named hypothesis on soundness AT EVERY RECORD OF THE FRAME's LETTERS whose decision on the key
file is the description's own behind a gate.

WHY THE DEBT IS ASKED OVER A SET OF DESCRIPTIONS, AND AT EVERY RECORD.
(1) A statement that asks the debt at EVERY three public files Z at which a maker returns, with the bound εs outside «for all Z», and hands the payer nothing of what the caller holds, fails in this way: at ONE Z where the maker returns a description whose rounds are dearer than εs the
premise is false and the theorem above it true and empty AT EVERY Z. EVALUATED: at one candidate Z (the stored files with the target line lowered) and at eight neighbours a maker that goes through the planner of all seven chains REFUSES (that planner holds the target against other lines): so no witness is known and none is
excluded: THE FAULT IS ONE OF FORM. THIS FILE STATES NO DEBT OF THAT FORM, BUT `KeyDebtOn S A E εs`: the debt is asked AT THE DESCRIPTIONS OF A SET S alone, and the payer holds «F is of S» and THE DESCRIPTION's OWN TESTS ON THE PLAN (`F.planOk = true`). `keySound_on`: where these tests say
no the description's decision never says yes and the hypothesis holds for nothing (`keySoundOfFullD_of_planOk`); where they say yes: the debt.
(2) The rule beneath is general in the record. The conclusions stand at every `Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK …` with `runK = gatedFileDecision b (F.pull instK).run` (b = true in `keySound_of_debt`; any b in `keySound_on`), `Tl.depthReqT = 0` (the key file's request tree has one leaf) and `Tl.εs = εs`. So
the public files, the plan `GF Z`, the test on the planner's bytes and the test on the data's numbers ARE OUTSIDE IT; `tReal` is one member (KeyAtTReal.lean, not in this library; `tReal` itself: Johnson/Top/Fire/Code/NamedReal.lean).
In `KeyDebt` the type of requests is a letter Xr.
Main names.
  `KeyDebt F instK A E DK εs file`: THERE ARE a type of witnesses, the three chains' first blocks and the rest, the pieces' letters, a statement, and three tables (a promise and a claim at each boundary) SUCH THAT: the description's data are DK's · its first chain's last block has a round · the three
    heads · `RowsOwed` · one bound a block. ONE PROPOSITION ON F.
  `keySound_of_debt` · `KeyDebtOn` · `keyDebtOn_mono` · `keySound_on`: as above. WHICH SET: `FkInScopeD` (KeyFkAtD.lean); the statement over it: `KeyOwedAtD` (KeyAtFkD.lean).
Every «there is», walked. All stand ON THE PREMISE's SIDE: whoever pays `KeyDebt` names the tables and the pieces' letters; the conclusion's own «there is a list of errors» is the rule's.
THE SILLY MEMBERS. Those of KeyOfRows.lean's head. AT S := «no description»: `KeyDebtOn` holds for nothing and `keySound_on` says nothing: a set is worth what lies in it.
Limits. A JOINING AND DEFINITIONS: NOTHING IS PAID; no member of `KeyDebt` that says yes somewhere is known at any F; `KeyDebtOn` is a statement, not a theorem. A · E · εs are letters. εs stands outside «for all F»: KeyDebtCap.lean has the form without it. THE DESCRIPTION's LAST TEST IS READ NOWHERE (KeyOfRows.lean's head).

-/
import Johnson.Top.Fire.Code.KeyOfRowsEach
import Johnson.Flat.Dec.PlanOkForFree

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

/-- **The key file's whole debt on the plain road, as one proposition on a description.** -/
def KeyDebt {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) (εs : ℝ≥0∞) (file : String) : Prop :=
  ∃ (W : Type)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W) (_ : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)
    (on₁ L₁ : ℕ → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₂ L₂ : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop) (on₃ L₃ : ℕ → ((F.XiPub × F.S₁ × F.S₂) × F.S₃) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop),
    F.data file = .ok (DK.at frS.P.T.a) ∧ F.sealLast = true ∧
    F.first.blocksInOrder = c₁ :: k₁ ∧ F.shared.blocksInOrder = c₂ :: k₂ ∧ F.second.blocksInOrder = c₃ :: k₃ ∧
    RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃ ∧
    EachBelow εs ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) ∧
    EachBelow εs ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) ∧
    EachBelow εs ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)

set_option maxHeartbeats 4000000 in
/-- **The debt gives the key file's hypothesis, at every record of the frame's letters with the description's own decision behind an open gate, one leaf, and the bound εs.** -/
theorem keySound_of_debt {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) (εs : ℝ≥0∞) (file : String)
    (h : KeyDebt F instK A E DK εs file)
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (hb : b = true) (er : runK = gatedFileDecision b (F.pull instK).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hd : Tl.depthReqT = 0) (hε : Tl.εs = εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) := by
  obtain ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, dS, on₁, L₁, on₂, L₂, on₃, L₃, data, sealed, q₁, q₂, q₃, rows, b₁, b₂, b₃⟩ := h
  exact keySound_of_rows_each F instK A E DK εs file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd data sealed q₁ q₂ q₃
    on₁ L₁ on₂ L₂ on₃ L₃ rows dS b₁ b₂ b₃ hb er Tl hd hε

/-- **The debt, over a set of descriptions**: at every F of the set whose data are made; the payer holds that F is of the set and the description's own tests on the plan. -/
def KeyDebtOn {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (εs : ℝ≥0∞) : Prop :=
  ∀ (F : FileDescription XiK) (DK : WholeD),
    S F → F.data "key file" = .ok (DK.at frS.P.T.a) → F.planOk = true →
    KeyDebt F instK A E DK εs "key file"

/-- A debt over a larger set pays the debt over a smaller. -/
theorem keyDebtOn_mono {XiK : Type} {instK : RecFull → XiK} {S S' : FileDescription XiK → Prop} (hS : ∀ F, S F → S' F)
    {Xr : Type} {A : (frS.toDecR frZ 402653181).Claims Xr} {E : Coding A} {εs : ℝ≥0∞} (h : KeyDebtOn instK S' A E εs) : KeyDebtOn instK S A E εs :=
  fun F DK s => h F DK (hS F s)

set_option maxHeartbeats 4000000 in
/-- From it: the key file's hypothesis at every description of the set. -/
theorem keySound_on {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (εs : ℝ≥0∞) (h : KeyDebtOn instK S A E εs)
    (F : FileDescription XiK) (DK : WholeD)
    (hs : S F) (hD : F.data "key file" = .ok (DK.at frS.P.T.a))
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (er : runK = gatedFileDecision b (F.pull instK).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hd : Tl.depthReqT = 0) (hε : Tl.εs = εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) := by
  cases b with
  | false =>
    subst er
    exact keySoundOfFullD_of_never (fun _ _ _ _ => rfl) Tl
  | true =>
    exact keySoundOfFullD_of_planOk (F.pull instK) true er Tl fun hp =>
      keySound_of_debt F instK A E DK εs "key file" (h F DK hs hD hp) rfl er Tl hd hε

end LPFD

#print axioms LPFD.KeyDebt
#print axioms LPFD.keySound_of_debt
#print axioms LPFD.KeyDebtOn
#print axioms LPFD.keyDebtOn_mono
#print axioms LPFD.keySound_on
