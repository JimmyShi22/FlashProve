-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyAtRest.lean: at the full size: WHAT IS OWED FOR THE KEY FILE WITH THE ROWS THAT HAVE A THEOREM LAID IN: ONE LIST, ONE LINE A ROW.
Main names.
  `paidNow`: THE LIST of the rows that are laid in here.
  `paid_in_scope`: in scope, where the description's data are DK's and are the written data, and its test on the places passes: each row of the list has its law at `The21Off`'s terms: EACH BY A THEOREM OF OTHER FILES, CALLED: one line a row:
    r1_0 · r1_1: `r1_0_at_name` | `r1_1_at_name` (RowsAtName.lean).
    r1_4 · r1_10: `r1_4_in_scope` | `r1_10_in_scope` (Johnson/RunOne/Law/FieldsAtNameScope.lean) · r1_5 · r1_11: `r1_5_in_scope` | `r1_11_in_scope` (FieldsLayerScope.lean): at tab := tabN; their one premise on this frame, the first chain's bases, is paid here from «DK's data are the written data» (`basesAll_at_six` · `four_of_all`). BENEATH THE FOUR LIE 109 FILES BY A LIST THAT IS NOT IN THIS REPOSITORY: rough working files beside rough working files. (Where
    this and lean/THEOREM.md differ, the page holds.)
    r1_16: `r1_16_at_name_ten` (Row116Ten.lean): the same premises as r1_17's, and the other two chains' heads.
    r2_3 · r2_6 · r2_8: `r2_3_at_name` | `r2_6_at_name` | `r2_8_at_name` (Rows2AtName.lean) · r3_0: `r3_0_at_name` (Row30AtName.lean): calls of further files' laws at the maker's own pieces; premises: the three chains' heads · the five in scope · the test on the places · «DK's data are the written data». BENEATH THE FOUR LIE 25 FILES BY A LIST THAT IS NOT IN THIS REPOSITORY. (Where
    this and lean/THEOREM.md differ, the page holds.)
    r1_17: `r1_17_at_name` (Row117AtName.lean): it spends besides the description's test on the places and «DK's data are the written data».
  `RestOff paid X N P DK`: `The21Off` (KeyAtOff.lean) with `TheRest … paid` (TheRest.lean) in `The21`'s place: the same written terms, the same two letters under the ∃ (enc · rad).
  `off_of_rest`: in scope: `RestOff paidNow` gives `The21Off`.
In this file the digest cfg is FREE: `madeAt X₀ Zp.lay cfg` at any cfg.
OBJECT: `Key.descriptionFromSource X N P` in scope · USER: Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: under the ∃: enc · rad.
Limits. THE ROWS THAT ARE NOT IN THE LIST ARE ALL OPEN. (Where
this and lean/THEOREM.md differ, the page holds.) Whether a row of the list counts toward the key file's soundness is not judged in this file: here it is a theorem that fits a field. The full size alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.TheRest
import Johnson.Top.Fire.Code.RowsAtName
import Johnson.Top.Fire.Code.Row117AtName
import Johnson.Top.Fire.Code.Row116Ten
import Johnson.Top.Fire.Code.KeyAtPin
import Johnson.RunOne.Law.FieldsLayerScope
import Johnson.Top.Fire.Code.Rows2AtName
import Johnson.Top.Fire.Code.Row30AtName

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

/-- **THE ROWS THAT ARE LAID IN.** -/
def paidNow : List Row := [.r1_0, .r1_1, .r1_4, .r1_5, .r1_10, .r1_11, .r1_16, .r1_17, .r2_3, .r2_6, .r2_8, .r3_0]

theorem paidNow_nodup : paidNow.Nodup := by decide

/-- **WHAT IS OWED, WITH THE ROWS OF A LIST LAID IN.** -/
def RestOff (paid : List Row) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (x₀ x₁ : Lookup) (bw : Block FirstState Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ → (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    ∃ (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
      (_ : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      TheRest X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N paid

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (DK : WholeD)
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
include hZ hP hm hX hp hwant hdata hDK

/-- **EACH ROW OF THE LIST HAS ITS LAW AT THE WRITTEN TERMS: ONE LINE A ROW.** -/
theorem paid_in_scope (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) :
    ∀ r ∈ paidNow, lawAt X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N r := by
  intro r hr
  obtain ⟨hb₁, -, -, -⟩ := four_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix
    (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃
  cases r <;> first
    | exact absurd hr (by decide)
    | exact r1_0_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ hZ hP hm hX hp hdata
    | exact r1_1_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ hZ hP hm hX hp hdata
    | exact Johnson.RunOne.Law.FieldsAtNameScope.r1_4_in_scope DK tabN c₁ k₁ c₂ k₂ c₃ k₃ hZ hP hm hX hp "key file" hdata q₁ q₂ q₃ hb₁
    | exact Johnson.RunOne.Law.FieldsLayerScope.r1_5_in_scope DK tabN c₁ k₁ c₂ k₂ c₃ k₃ hZ hP hm hX hp q₁ hb₁
    | exact Johnson.RunOne.Law.FieldsAtNameScope.r1_10_in_scope DK tabN c₁ k₁ c₂ k₂ c₃ k₃ hZ hP hm hX hp "key file" hdata q₁ q₂ q₃ hb₁
    | exact Johnson.RunOne.Law.FieldsLayerScope.r1_11_in_scope DK tabN c₁ k₁ c₂ k₂ c₃ k₃ hZ hP hm hX hp q₁ hb₁
    | exact r1_16_at_name_ten X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
    | exact r1_17_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ hZ hP hm hX hp hwant hdata hDK
    | exact r2_3_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hDK
    | exact r2_6_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hDK
    | exact r2_8_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hDK
    | exact r3_0_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hDK

/-- **In scope the rest gives the 21 at the same terms.** -/
theorem off_of_rest (h : RestOff paidNow X N P DK) : The21Off X N P DK := by
  intro c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  obtain ⟨enc, rad, dS, H⟩ := h c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  exact ⟨enc, rad, dS, the21_of_rest paidNow (paid_in_scope DK hZ hP hm hX hp hwant hdata hDK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ enc rad) H⟩

end

end LPFD

#print axioms LPFD.paidNow_nodup
#print axioms LPFD.RestOff
#print axioms LPFD.paid_in_scope
#print axioms LPFD.off_of_rest
