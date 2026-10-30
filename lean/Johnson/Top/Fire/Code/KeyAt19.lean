-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyAt19.lean: at the full size: WHAT IS OWED FOR THE KEY FILE WITH ROWS 1.0 AND 1.1 LAID IN: NINETEEN LAWS.
Main names.
  `The19Off X N P DK`: `The21Off` (KeyAtOff.lean) with `The19` (The19.lean) in `The21`'s place: the same terms, the same two letters under the ∃ (enc · rad).
  `off_of_19`: in scope, where the description's data are DK's: it gives `The21Off`: the two fields r1_0 | r1_1 are theorems `r1_0_at_name` | `r1_1_at_name` (RowsAtName.lean), CALLED.
In this file the digest cfg is FREE: `madeAt X₀ Zp.lay cfg` at any cfg.
OBJECT: `Key.descriptionFromSource X N P` in scope · USER: Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: under the ∃: enc · rad.
Limits. THE NINETEEN ARE ALL OPEN. (Where
this and lean/THEOREM.md differ, the page holds.) Whether rows 1.0 | 1.1 count toward the key file's soundness is not judged in this file: here they are two theorems that fit two fields. The seven elder forms stay beside. The full size alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.The19
import Johnson.Top.Fire.Code.RowsAtName

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

/-- **WHAT IS OWED, WITH ROWS 1.0 AND 1.1 LAID IN: NINETEEN LAWS AND NOTHING BESIDE THEM.** -/
def The19Off (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
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
      The19 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N

/-- **In scope it gives the 21 at the same terms.** -/
theorem off_of_19 {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (DK : WholeD)
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (h : The19Off X N P DK) : The21Off X N P DK := by
  intro c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  obtain ⟨enc, rad, dS, H⟩ := h c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  exact ⟨enc, rad, dS, the21_of_19 H (r1_0_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ hZ hP hm hX hp hdata)
    (r1_1_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ hZ hP hm hX hp hdata)⟩

end LPFD

#print axioms LPFD.The19Off
#print axioms LPFD.off_of_19
