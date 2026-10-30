-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Rows2SendAtName.lean: THE KEY FILE, THE SHARED CHAIN: «THE CALL» OF ROWS 2.2
  ("send o_u") AND 2.5 ("send o_omega"): The21's fields r2_2 · r2_5 AT The21Off's WRITTEN TERMS, IN
  THE GOALS' SCOPE, AT ANY enc rad.
  r2_2_at_name | r2_5_at_name   PROVED: := r2_2_new | r2_5_new
      (Johnson/Top/Fire/Code/Rows2Send.lean) at new22' | new25'
      (Johnson/RunOne/KeyNewAtSend2Paid.lean):
      "behind the maker's piece every leaf is shown at the new pins".
  fit_2225     THE FIT, BY LEAN's OWN CHECK OF TYPES: a The21 at The21Off's terms with its two
      fields r2_2 | r2_5 laid anew by these two theorems is a The21 at these terms.
IN FRONT STAND: the three heads · the five in scope · wantedOk · the data · the pin on the data.
  NOTHING ELSE: no binder on a state, on a letter or on a tie.
NO MEMBER OF THE ROWS' GUARDS (On₂' … 2 | 5) IS SHOWN IN THIS FILE: until one is shown, each may
  be true and empty at the real protocol, and counts as closing nothing.
Limits. Calls alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Rows2Send
import Johnson.RunOne.KeyNewAtSend2Paid
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
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁ plan₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)
open VerifiableInference.Desc.Key.Fill (six OmAt symsW)
open Johnson.RunOne.KeyRows23 (numSix atSix kreadFam baseK)
open Johnson.RunOne.KeyRows23 (p14Key p14At_key key_of_scope sentUKey withU_key len2 len5 smp2 smp50
    smp51 tieS2 tieS50 tieS51 readerOf readerIn words_zero words_fam last₁At shared_2 shared_5
    yes22_seat yes25_seat keeps₂_send2_seat keeps₂_send5_seat tie3_scope tie4_scope tie5_scope)
open Johnson.RunOne.KeyMsg (cond_u_key cond_omega_key below_u_key below_omega_key)
open VerifiableInference.Desc.K1 (condPort sendPiece Sealed shapeAt shapesOf sampledAt errPort
    seedMaps seedEntry seeds_one seed_draws)
open _root_.Desc.K14 (parK1 withU withOmega)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ :
        Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ :
        List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m :
            Johnson.G.OfPlan.Made}

/-- **The21's FIELD r2_2 AT The21Off's TERMS, IN SCOPE.** -/
theorem r2_2_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder =
    c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 2 :=
  r2_2_new X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK fun b base d₁
      d₂ hrow _ _ =>
    Johnson.RunOne.KeyNew2.new22' (W' := Unit) X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest ()
        () hZ hP hm hX hp hwant hdata hDK q₂ b base d₁ d₂ [] hrow _ _ _

/-- **The21's FIELD r2_5 AT The21Off's TERMS, IN SCOPE.** -/
theorem r2_5_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder =
    c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 5 :=
  r2_5_new X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK fun b base d₁
      d₂ hrow _ _ =>
    Johnson.RunOne.KeyNew2.new25' (W' := Unit) X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest ()
        () hZ hP hm hX hp hwant hdata hDK q₂ b base d₁ d₂ [] hrow _ _ _

/-- **THE FIT**: the two theorems' conclusions ARE The21's fields r2_2 | r2_5 at The21Off's terms,
  at any enc rad: by Lean's own check of types. -/
def fit_2225 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ ::
    k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack)
        atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix
        (readAt tabN) enc rad collN off₂N off₃N :=
  { H with
    r2_2 := r2_2_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
    r2_5 := r2_5_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
        }

end

end LPFD

#print axioms LPFD.r2_2_at_name
#print axioms LPFD.r2_5_at_name
#print axioms LPFD.fit_2225
