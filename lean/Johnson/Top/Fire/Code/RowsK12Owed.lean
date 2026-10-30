-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowsK12Owed.lean: THE KEY FILE: ROWS 2.9 · 2.10 · 3.2: FROM
  ONE STRUCTURE OF PUBLIC DEBTS (Owed29 | Owed210 | Owed32, at the row's own look-up) TO The21's
  FIELDS r2_9 | r2_10 | r3_2 AT The21Off's WRITTEN TERMS, IN THE GOALS' SCOPE. BENEATH THE CALLS
  (RowsK12AtName.lean), WHERE «owed» IS PAID.
  r2_9_of_owed | r2_10_of_owed | r3_2_of_owed   := the door's last mile (RowsK12Door.lean) at
      pays_29_name | pays_210_name | pays_32_name, WITH EVERY LETTER FILLED: n by rfl · off₂
      | off₃ := off₂N | off₃N · lo := 6 · rdN := 0 · oNo | mem: closed terms, their equations by rfl
      · rd := tabP's own reading · hrow := hrow_2 | hrow_32. LEFT AS LETTERS: r (the radii at the
      place) · num · (2.10) nO with P.O = some nO and one closed equation hlo: whoever pays «owed»
      picks them.
WHAT IT IS NOT. In this file «owed» is a premise: nothing is paid here. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.RowsK12Door

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

/-- **ROW 2.9 FROM Owed29.** -/
theorem r2_9_of_owed (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₂ : (Fk X N P).shared.blocksInOrder
    = c₂ :: k₂)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk
        X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (r : _root_.Fmt.M1.Stage → ℕ) (num : _root_.Fmt.TreeSource → ℕ)
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
          (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[9]? = some
          (pieceOf (held (B9 P)) base (dB :: dt) [] (capRest 9 (dB :: dt))) →
      Owed29 (W := Unit) P (DK.at frS.P.T.a) r 6 num base dB dt (capRest 9 (dB :: dt))) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 9 :=
  r2_9_of_pays X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₂ hp
    (pays_29_name (W := Unit) X N P (DK.at frS.P.T.a) tabN enc rad off₂N c₁ k₁ c₂ k₂ c₃ k₃ capRest
        capRest capRest () () hZ hP hm hX hL hN hp hwant hdata DK hdata hDK (fun _ => rfl) 9 rfl r 6
        rfl num (fun _ => 0)
      (fun x => if x.2.val = 3 then 0 else 3)
      (fun k => if k = 0 then some ⟨sixS, Johnson.RunOne.Law.K12Law29Core.i3⟩ else if k = 3 then
          some ⟨sixS, Johnson.RunOne.Law.K12Law29Core.i5⟩ else none)
      (fun x u part i => H2K.Pin.tabP Johnson.Top.H.csKey (x.1.l.get x.2).1 u part i) (fun _ _ _ _
          => rfl) rfl rfl rfl rfl
      (fun base ds back h => hrow_2 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₂ hZ hP hm hX hp hwant hdata 9
          (Or.inl rfl) (B9 P) base ds back h)
      owed)

/-- **ROW 2.10 FROM Owed210.** -/
theorem r2_10_of_owed (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₂ : (Fk X N P).shared.blocksInOrder
    = c₂ :: k₂)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk
        X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (nO : H2U.PlaceNums) (hO : P.O = some nO) (hlo : numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own 0) =
        6)
    (r : _root_.Fmt.M1.Stage → ℕ)
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
          (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[10]? = some
          (pieceOf (held (B10 nO)) base (dB :: dt) [] (capRest 10 (dB :: dt))) →
      Owed210 (W := Unit) X N P (DK.at frS.P.T.a) nO r base dB dt (capRest 10 (dB :: dt))) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 10 :=
  r2_10_of_pays X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₂ hp nO hO
    (pays_210_name (W := Unit) X N P (DK.at frS.P.T.a) tabN enc rad off₂N c₁ k₁ c₂ k₂ c₃ k₃ capRest
        capRest capRest () () hZ hP hm hX hL hN hp hwant DK hdata hDK hdata nO hO 10 rfl r (fun _ =>
        0)
      (fun x => if x.2.val = 4 then 2 else 3)
      (fun k => if k = 3 then some ⟨sixS, Johnson.RunOne.Law.K12Back210.i5⟩ else if k = 2 then some
          ⟨sixS, Johnson.RunOne.Law.K12Back210.i4⟩ else none)
      (fun x u part i => H2K.Pin.tabP Johnson.Top.H.csKey (x.1.l.get x.2).1 u part i) (fun _ _ _ _
          => rfl) rfl rfl rfl rfl (fun _ => rfl) hlo
      (fun base ds back h => hrow_2 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₂ hZ hP hm hX hp hwant hdata 10
          (Or.inr rfl) (B10 nO) base ds back h)
      owed)

/-- **ROW 3.2 FROM Owed32.** -/
theorem r3_2_of_owed (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P) (hN : rangesNumbers m = .ok N) (hp : (Fk
        X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
        frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (r : _root_.Fmt.M1.Stage → ℕ) (num : _root_.Fmt.TreeSource → ℕ)
    (owed : ∀ (base : ℕ) (dB : RDT) (dt : List RDT),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
          (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃)[2]? = some
          (pieceOf (held (B32 P)) base (dB :: dt) [] (capRest 2 (dB :: dt))) →
      Owed32 (W := Unit) X N P (DK.at frS.P.T.a) r num base dB dt (capRest 2 (dB :: dt))) :
    KeepsAt (On₃' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) collN off₂N
        off₃N) (Cl₃ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc
        (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
        capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at
        frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃) 2 :=
  r3_2_of_pays X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₃
    (pays_32_name (W := Unit) X N P (DK.at frS.P.T.a) tabN off₂N off₃N c₁ k₁ c₂ k₂ c₃ k₃ capRest
        capRest capRest () () hZ hP hm hX hL hp hwant hdata DK hdata hDK hN (fun _ => rfl) (fun _ =>
        rfl) 2 rfl r num (fun _ => 0)
      (fun x => if x.2.val = 0 then 0 else if x.2.val = 2 then 1 + 2 * (oneAt
          X).ranges.stages.length else 1 + 2 * (oneAt X).ranges.stages.length + 2)
      (fun k => if k = 0 then some ⟨sixS, Johnson.RunOne.Law.K12Law32Core.i0⟩ else if k = 1 + 2 *
          (oneAt X).ranges.stages.length then some ⟨sixS, Johnson.RunOne.Law.K12Law32Core.i2⟩ else
          if k = 1 + 2 * (oneAt X).ranges.stages.length + 2 then some ⟨sixS,
          Johnson.RunOne.Law.K12Law32Core.i4⟩ else none)
      (fun x u part i => H2K.Pin.tabP Johnson.Top.H.csKey (x.1.l.get x.2).1 u part i) (fun _ _ _ _
          => rfl) rfl rfl rfl rfl (by simp) (by simp)
      (fun base ds back h => hrow_32 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₃ hZ hP hm hX hp hwant hdata (B32
          P) base ds back h)
      owed)

end

end LPFD

#print axioms LPFD.r2_9_of_owed
#print axioms LPFD.r2_10_of_owed
#print axioms LPFD.r3_2_of_owed
