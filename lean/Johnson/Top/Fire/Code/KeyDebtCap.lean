-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyDebtCap.lean, general in the instance's type (`KeyCapOn instK S …` · `keySound_on_cap instK S …`): at the full size: a rider to KeyDebt.lean: THE KEY FILE's DEBT WITHOUT ITS THREE BOUNDS AND WITHOUT εs.

Why. Other files name the pieces' errors: the cap (`Err.cap 128`, Iop/ErrCap.lean: at each written round the number of its challenges / 2^128, rounded down), and have the three bounds as theorems there, at every description and every εs of at least 2^-128 (`eachBelow_atCap₁ | ₂ | ₃`, Johnson/Desc/Sound/BoundsAtCap.lean).
So the debt can be said once, with no εs in it.
WHERE THE CAP IS 0 [read at the text: OnBytes/TypedOracleCompiler/Run/PlanQS.lean · Iop/Grind.lean · Run/PlanPull.lean: a written round's challenges are its hash blocks `Fin b → Dig 256` TIMES THE WORK's TEST BITS `Fin work → Bool`]: at the rounds that draw no block (b = 0: 2^work challenges: at most 2^32 where the key file's description's clause «prices» says yes: `keyOk`, Johnson/Desc/MadeOk.lean: a round's work is at most 32) alone: every round that draws a block has at least 2^256.
Main names. `KeyDebtCap F instK A E DK file`: `KeyDebt`'s list with «the pieces' errors are the cap» thrice in place of the three bounds, AND WITHOUT «the first chain's last block has a round»: in the format (`FileDescription.planOk`, Johnson/Desc/Block.lean) that test is the second half of the description's own tests on the plan, which the payer of `KeyCapOn` holds. `keyDebt_of_cap`: with that test's yes it gives `KeyDebt` at every εs ≥ 2^-128. `KeyCapOn S A E`: it, asked over a set of descriptions, the payer holding what `KeyDebtOn`'s holds. `keyCapOn_mono`. `keySound_on_cap`: from it
`CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl)` at every record Tl as in KeyDebt.lean's head, whatever `Tl.εs` is (the record itself holds 2^-128 ≤ εs).
WHAT THE CAP DOES NOT PAY (by report): it prices nothing: EVERY BLOCK's LAW (`RowsOwed`'s keeps₁ | ₂ | ₃) IS OWED AT THE CAP: at most a share of 2^-128 of each round's written challenges, the bits of work among them, may be bad. (Where
this and lean/THEOREM.md differ, the page holds.) At a round with fewer than 2^128 written challenges the cap is 0.
Limits. Those of KeyDebt.lean's head. A JOINING: NOTHING IS PAID.

-/
import Johnson.Top.Fire.Code.KeyDebt
import Johnson.Desc.Sound.BoundsAtCap

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

/-- **The key file's debt where every piece's errors are the cap**: `KeyDebt` with its three bounds replaced by «the pieces' errors are the cap», and without the test on the seal: no bound is read. -/
def KeyDebtCap {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) (file : String) : Prop :=
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
    F.data file = .ok (DK.at frS.P.T.a) ∧
    F.first.blocksInOrder = c₁ :: k₁ ∧ F.shared.blocksInOrder = c₂ :: k₂ ∧ F.second.blocksInOrder = c₃ :: k₃ ∧
    RowsOwed F instK A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd on₁ L₁ on₂ L₂ on₃ L₃ ∧
    AtCap rest₁ ∧ AtCap rest₂ ∧ AtCap rest₃

/-- It gives the debt at every bound of at least 2^-128. -/
theorem keyDebt_of_cap {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) (file : String)
    (sealed : F.sealLast = true) (h : KeyDebtCap F instK A E DK file) : KeyDebt F instK A E DK εs file := by
  obtain ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, dS, on₁, L₁, on₂, L₂, on₃, L₃, data, q₁, q₂, q₃, rows, a₁, a₂, a₃⟩ := h
  exact ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, dS, on₁, L₁, on₂, L₂, on₃, L₃, data, sealed, q₁, q₂, q₃, rows,
    eachBelow_atCap₁ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd εs hε a₁,
    eachBelow_atCap₂ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd εs hε a₂,
    eachBelow_atCap₃ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd εs hε a₃⟩

/-- **The debt at the cap, over a set of descriptions.** No bound stands in it. -/
def KeyCapOn {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) : Prop :=
  ∀ (F : FileDescription XiK) (DK : WholeD),
    S F → F.data "key file" = .ok (DK.at frS.P.T.a) → F.planOk = true →
    KeyDebtCap F instK A E DK "key file"

/-- A debt over a larger set pays the debt over a smaller. -/
theorem keyCapOn_mono {XiK : Type} {instK : RecFull → XiK} {S S' : FileDescription XiK → Prop} (hS : ∀ F, S F → S' F)
    {Xr : Type} {A : (frS.toDecR frZ 402653181).Claims Xr} {E : Coding A} (h : KeyCapOn instK S' A E) : KeyCapOn instK S A E :=
  fun F DK s => h F DK (hS F s)

theorem keyDebtOn_of_cap {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (h : KeyCapOn instK S A E) (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) :
    KeyDebtOn instK S A E εs :=
  fun F DK hs hD hp =>
    keyDebt_of_cap F instK A E DK εs hε "key file"
      (Sound.sealLast_of_planOk F hp) (h F DK hs hD hp)

/-- From it: the key file's hypothesis, at every record with the description's own decision behind a gate and one leaf (that its bound is at least 2^-128 rides in the record). -/
theorem keySound_on_cap {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (h : KeyCapOn instK S A E)
    (F : FileDescription XiK) (DK : WholeD)
    (hs : S F) (hD : F.data "key file" = .ok (DK.at frS.P.T.a))
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (er : runK = gatedFileDecision b (F.pull instK).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hd : Tl.depthReqT = 0) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) :=
  keySound_on instK S A E Tl.εs (keyDebtOn_of_cap instK S A E h Tl.εs Tl.hε) F DK hs hD er Tl hd rfl

end LPFD

#print axioms LPFD.KeyDebtCap
#print axioms LPFD.keyDebt_of_cap
#print axioms LPFD.KeyCapOn
#print axioms LPFD.keyCapOn_mono
#print axioms LPFD.keyDebtOn_of_cap
#print axioms LPFD.keySound_on_cap
