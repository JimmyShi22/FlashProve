-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowsAtName.lean: THE KEY FILE's ROWS 1.0 | 1.1: «THE CALL»: The21's FIELDS
  r1_0 | r1_1 AT THE WRITTEN TERMS (The21Off's, Johnson/Top/Fire/Code/KeyAtOff.lean: the rests
  capRest · the witnesses' type Unit · B := baseAt X decN recBack · at_ := atSix · R := readAt tabN
  · coll := collN), IN THE GOALS' SCOPE. On one reading of level 9: «ROW 1.1 IS
  ONE CALL AND ONE GROUND FROM COUNTING».
OBJECT: The21.r1_0 | r1_1 (Johnson/Top/Fire/Code/The35.lean) at these terms · USER: whoever fills
  The21Off · LETTERS: X N P DK · the maker's cut · the scope's Zp X₀ cfg m.
  r1_0_at_name | r1_1_at_name   PROVED: := r1_0_nine | r1_1_nine at atCap_capRest ·
    cellOnly_collN; at 1.1 the second block and «it is the second» are MADE (second_is)
  fit_01       THE FIT, BY LEAN's OWN CHECK OF TYPES: a The21 at The21Off's terms, at ANY enc rad,
    with its two fields r1_0 | r1_1 laid anew by these two theorems, is a The21 at these terms
WHAT STANDS IN FRONT: q₁ · the five in scope · «the description's data are DK's, set to the frame's
  depth». NOTHING ELSE.
NO MEMBER OF THE ROWS' GUARDS IS SHOWN IN THIS FILE. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowsNine
import Johnson.Top.Fire.Code.KeyAtOff

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
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃
    seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt
    errPort seedMaps seedEntry Tie planOkOwn)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)
open Johnson.RunOne.KeyRows23 (baseK tieS_fam readerOf readerIn words_zero seatAt)
open VerifiableInference.Desc.Key.Fill (ShapesApart symsW six)
open Johnson.RunOne.KeySendGood (SendAsks asks_in_scope cond_of parIdx parMsg fullIdx fullMsg idx_at
    msg_at idx_pays msg_pays pays_bare rounds_idx rounds_msg seed_kind)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.KeyRows23 (numSix atSix kreadFam)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ :
        Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ :
        List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}

/-- **The21's FIELD r1_0 AT The21Off's TERMS, IN SCOPE.** -/
theorem r1_0_at_name (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) collN) (Cl₁ X
        N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc (Fk X N P)
        (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest
        () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 0 :=
  r1_0_nine X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () collN (readAt tabN) decN
      recBack q₁ hZ hP hm hX hp hdata atCap_capRest cellOnly_collN

/-- **The21's FIELD r1_1 AT The21Off's TERMS, IN SCOPE.** The second block is made:
second_is. -/
theorem r1_1_at_name (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) collN) (Cl₁ X
        N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc (Fk X N P)
        (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest
        () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 1 := by
  obtain ⟨c, l', hk⟩ := second_is X N P c₁ k₁ q₁
  exact r1_1_nine X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () collN tabN decN recBack c
      q₁ (by rw [hk]; rfl) hZ hP hm hX hp hdata atCap_capRest cellOnly_collN

/-- **THE FIT**: the two theorems' conclusions ARE The21's fields r1_0 | r1_1 at The21Off's terms,
at any enc rad: by Lean's own check of types. -/
def fit_01 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack)
        atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix
        (readAt tabN) enc rad collN off₂N off₃N :=
  { H with
    r1_0 := r1_0_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ hZ hP hm hX hp hdata
    r1_1 := r1_1_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ hZ hP hm hX hp hdata }

end

end LPFD

#print axioms LPFD.r1_0_at_name
#print axioms LPFD.r1_1_at_name
#print axioms LPFD.fit_01
