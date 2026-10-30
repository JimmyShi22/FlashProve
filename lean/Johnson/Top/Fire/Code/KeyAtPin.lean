-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyAtPin.lean: at the full size: WHAT IS OWED FOR THE KEY FILE WITH THE FOUR FACTS ON BASES PAID FROM ONE PUBLIC EQUATION: the record's data of the key file are the written data.
Main names.
  `The21Last A E X N P DK`: `The21AtName` (KeyAtName.lean) without its four facts on bases: beside the 21 laws: off · HeldAtName · `The21AtPin`: that equation and `The21Last`.
  `name_of_pin`: in scope, under the description's tests on the plan and `wantedOk`: it gives `The21AtName`: by `basesAll_at_six` (KeyBasesAtSix.lean) and `four_of_all` (BasesOk.lean).
OBJECT: `Key.descriptionFromSource X N P` in scope · USER: Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: A · E; under the ∃: tab · enc · rad · off₂ · off₃.
Limits. NO LAW IS PAID. THE EQUATION IS ASKED, NOT SHOWN: other files have it as a theorem over the key file's door with its second test. `The21AtName`, `The21AtBase` and `The21Handed` stay beside. The full size alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyAtName
import Johnson.Top.Fire.Code.KeyBasesAtSix
import Johnson.Top.Fire.Code.BasesOk

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
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (atSix)

/-- **WHAT IS LEFT WHEN THE FOUR FACTS ON BASES ARE GONE**: beside the 21 laws: off · HeldAtName. -/
def The21Last {Xr : Type} (A : DN.Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (x₀ x₁ : Lookup) (bw : Block FirstState Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ → (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    ∃ (tab : MsgN → ℕ → ℕ → OnBytes.F)
      (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
      (off₂ off₃ : ℕ → ℕ)
      (_ : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tab) enc rad collN off₂ off₃ ∧
      (∀ k ∈ [0, 2], off₃ (atSix k).1 = (atSix k).1) ∧
      HeldAtName A E X tab

/-- **WHAT IS OWED, WITH ONE PUBLIC EQUATION IN THE PLACE OF THE FOUR FACTS ON BASES.** -/
def The21AtPin {Xr : Type} (A : DN.Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  DK.at frS.P.T.a = Johnson.G.writtenKFull ∧ The21Last A E X N P DK

/-- **In scope it gives what is owed at the name's seven.** -/
theorem name_of_pin {Xr : Type} (A : DN.Claims Xr) (E : Coding A) {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (DK : WholeD)
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hw : (Fk X N P).wantedOk = true) (h : The21AtPin A E X N P DK) : The21AtName A E X N P DK := by
  intro c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  obtain ⟨tab, enc, rad, off₂, off₃, dS, H, off, hh⟩ := h.2 c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  obtain ⟨hb₁, hb₂₀, hb₂₁₁, hb₃₁⟩ := four_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix
    (basesAll_at_six hZ hP hm hX hp hw h.1) q₁ q₂ q₃
  exact ⟨tab, enc, rad, off₂, off₃, dS, H, off, hh, hb₁, hb₂₀, hb₂₁₁, hb₃₁⟩

end LPFD

#print axioms LPFD.The21Last
#print axioms LPFD.The21AtPin
#print axioms LPFD.name_of_pin
