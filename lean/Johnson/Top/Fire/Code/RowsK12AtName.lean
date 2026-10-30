-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowsK12AtName.lean: THE KEY FILE: «THE CALL» OF ROWS 2.9 · 2.10 · 3.2 (the
  three proximity tests behind the first chain): The21's fields r2_9 · r2_10 · r3_2 AT The21Off's
  WRITTEN TERMS, IN THE GOALS' SCOPE; rows 2.9 | 2.10 at any enc rad.
  r2_9_at_name | r2_10_at_name | r3_2_at_name   PROVED: := r2_9_of_owed | r2_10_of_owed |
      r3_2_of_owed (Johnson/Top/Fire/Code/RowsK12Owed.lean) at owed_29 | owed_210 |
      owed_32 (Johnson/RunOne/Law/K12Pays29Name.lean | K12Pays210Name.lean | K12Pays32Name.lean: the
      structures of public debts, paid in scope at the row's own look-up, at the planner's radii
      rKUFull | rKOFull | rKWFull and the file's numbering of the trees); at 2.10 the place nO by
      hO_in_scope (KeyPublicAtSeat.lean), the closed equation hlo by lo_six (K12PlaceAtName.lean);
      "the row's errors are the cap": rfl at capRest.
  fit_K12      THE FIT, BY LEAN's OWN CHECK OF TYPES: a The21 at The21Off's terms with its three
      fields r2_9 | r2_10 | r3_2 laid anew by these three theorems is a The21 at these terms.
IN FRONT STAND: the three heads · the five in scope · wantedOk · the data · the pin on the data
  (r2_7_at_name's eleven) AND THREE THAT THE SEAT HANDS ITS PAYER: hL (laterPlaces m = .ok P) · hN
  (rangesNumbers m = .ok N) · hasks (every test of Key.lawsAsk says yes). NO BINDER ON A STATE, ON A
  LETTER OR ON A TIE.
MARK: NO MEMBER OF THE ROWS' GUARDS (On₂' … 9 | 10 · On₃' … 2) IS SHOWN IN THIS FILE: until one is
  shown, each may be true and empty at the real protocol, and counts as closing nothing.
Limits. Calls alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.RowsK12Owed
import Johnson.Top.Fire.Code.KeyPublicAtSeat
import Johnson.RunOne.Law.K12PlaceAtName

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

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ :
        Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ :
        List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m :
            Johnson.G.OfPlan.Made}

open Johnson.RunOne.Law.K12AtField (Pays keepsAt_U keepsAt_own)
open Johnson.RunOne.Law.K12Pays29Name (pi9 B9 on9)
open Johnson.RunOne.Law.K12Pays32Name (pi32 B32 on32)
open Johnson.RunOne.Law.K12Pays210Name (pi10 B10 on10)
open Johnson.RunOne.Law.K12AtField (keepsAt_O)

open Johnson.RunOne.Law.K12Pays29Name (Owed29 pays_29_name)
open Johnson.RunOne.Law.K12Pays210Name (Owed210 pays_210_name)
open Johnson.RunOne.Law.K12Pays32Name (Owed32 pays_32_name)
open LPFD.CandLaid (sixS)

open Johnson.RunOne.Law.K12Pays29Name (owed_29)
open Johnson.RunOne.Law.K12Pays210Name (owed_210)
open Johnson.RunOne.Law.K12Pays32Name (owed_32)

/-- **The21's FIELD r2_9 AT The21Off's TERMS, IN SCOPE.** -/
theorem r2_9_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder =
    c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk
        X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    {Xa : OnBytes.Model.Verify.Public} {layA : ByteArray} {DA : WholeD} (hasks : ∀ t ∈ Key.lawsAsk
        Xa layA m (Fk X N P) DA, t.2 = true) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 9 :=
  r2_9_of_owed X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₂ hZ hP hm hX hL hN hp hwant hdata hDK _ _
    (owed_29 (W := Unit) X N P (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () hZ
        hP hm hX hL hp hwant DK rfl hdata hDK hasks q₁ q₂ q₃ (fun _ => rfl))

/-- **The21's FIELD r2_10 AT The21Off's TERMS, IN SCOPE.** -/
theorem r2_10_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder
    = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk
        X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    {Xa : OnBytes.Model.Verify.Public} {layA : ByteArray} {DA : WholeD} (hasks : ∀ t ∈ Key.lawsAsk
        Xa layA m (Fk X N P) DA, t.2 = true) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 10 := by
  obtain ⟨nO, hO⟩ := hO_in_scope (N := N) (P := P) hZ hP hm hX hp
  exact r2_10_of_owed X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₂ hZ hP hm hX hL hN hp hwant hdata hDK nO
      hO
    (Johnson.RunOne.Law.K12PlaceAtName.lo_six hZ hP hm hL X N hp hasks) _
    (owed_210 (W := Unit) X N P (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () hZ
        hP hm hX hL hp hwant DK rfl hdata hDK hasks nO hO 10 rfl q₁ q₂ q₃ (fun _ => rfl))

/-- **The21's FIELD r3_2 AT The21Off's TERMS, IN SCOPE.** -/
theorem r3_2_at_name (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ ::
             k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk
        X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    {Xa : OnBytes.Model.Verify.Public} {layA : ByteArray} {DA : WholeD} (hasks : ∀ t ∈ Key.lawsAsk
        Xa layA m (Fk X N P) DA, t.2 = true) :
    KeepsAt (On₃' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) collN off₂N
        off₃N) (Cl₃ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc
        (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
        capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at
        frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃) 2 :=
  r3_2_of_owed X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₃ hZ hP hm hX hL hN hp hwant hdata hDK _ _
    (owed_32 (W := Unit) X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () hZ hP hm hX hL hp
        hwant hdata hDK q₁ q₂ q₃ hasks (fun _ => rfl))

/-- **THE FIT**: the three theorems' conclusions ARE The21's fields r2_9 | r2_10 | r3_2 at
  The21Off's terms, at any enc rad: by Lean's own check of types. -/
def fit_K12 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ ::
    k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk
        X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    {Xa : OnBytes.Model.Verify.Public} {layA : ByteArray} {DA : WholeD} (hasks : ∀ t ∈ Key.lawsAsk
        Xa layA m (Fk X N P) DA, t.2 = true)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack)
        atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix
        (readAt tabN) enc rad collN off₂N off₃N :=
  { H with
    r2_9 := r2_9_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hL hN hp hwant
        hdata hDK hasks
    r2_10 := r2_10_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hL hN hp hwant
        hdata hDK hasks
    r3_2 := r3_2_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hL hN hp hwant hdata hDK
        hasks }

end

end LPFD

#print axioms LPFD.r2_9_at_name
#print axioms LPFD.r2_10_at_name
#print axioms LPFD.r3_2_at_name
#print axioms LPFD.fit_K12
