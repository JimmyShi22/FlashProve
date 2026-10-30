-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowsEightSix.lean: THE KEY FILE's ROWS
  1.0 | 1.1, LEVEL 8, AT THE FILLING's OWN LETTERS: l := six · num := numSix · at_ :=
  atSix · orc₁ := the first chain's plan's own: THE TIES AT THE CALL AND FOUR OF THE FIVE PREMISES
  ON baseK's FAMILY ARE PAID BY CALLS. «memberIs is the field for
  which neither row counts».
OBJECT: The35.r1_0 | r1_1 at B := baseK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc ·
  USER: The21AtBase's filler · LETTERS: X N P · the maker's cut and rests · R (1.0) | tab
  (1.1) · coll · decT recOf · the scope's.
  PAID AGAINST Left10f | Left11f: seat | seat0 | seat1 (atSix: rfl) · j := 0 | 1 · memberIs
    (member10_six | member11_six: rfl: the numerals 6130 | 3131959 ARE six's) · numIs (rfl) ·
    orcIs (rfl) · arr (arrOk_six₁) · inj (seat_inj_six) · apart (shapesApart_six) · tie
    (tie_six) · mains (hm_six)
  LeftSix k    WHAT IS LEFT AT EITHER ROW: Sound.SeatFits and its seat (cs m fam fits i seatIs)
    · cell (CollCell coll) · logs (what F_K tells of the tree at the seat has the log-length of the
    member's code)
  r1_0_eight_six | r1_1_eight_six   PROVED
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row11Eight
import Johnson.RunOne.KeyFillSeedAt

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
open Johnson.RunOne.KeyRows1 (Public11 SmpOwn smpOwn_base plan₁)
open Johnson.RunOne.KeyRows23 (smGroupsK kreadFam kreadFam_same numSix atSix seat_inj_six
    shapesApart_six arrOk_six₁ tie_six)
open VerifiableInference.Desc.Key.Fill (hm_six hmB_iff)

theorem mains_six (j : Fin six.length) : (six.get j).1.mainRows = 0 ∨ (Johnson.Pack.cMain
    Johnson.Top.H.csKey (six.get j).1).a = Johnson.Pack.aOf Johnson.Top.H.csKey (six.get j).1 :=
  (hmB_iff _ _).1 (List.all_eq_true.1 hm_six _ (List.get_mem six j))

section
variable {Cells Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ :
        Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ :
        List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N
          P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N
          P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N
          P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)

variable (R : KRead Cells Fill.Tab) (tab : Cells → ℕ → ℕ → OnBytes.F)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)
  (b₁ : Block (Fk X N P).S₁ (Fk X N P).Cl)

/-- **WHAT IS LEFT OF ROW 1.k (k = 0 | 1) IN SCOPE, AT THE SIX.** -/
structure LeftSix (k : Fin six.length) where
  cs : OnBytes.Codes
  m : List (OnBytes.OracleShape × ℕ)
  fam : Fin m.length → ℕ × ℕ
  fits : Sound.SeatFits (Fk X N P) cs m fam
  i : Fin m.length
  seatIs : fam i = atSix k.val
  cell : CollCell coll
  logs : ∀ o, (Fk X N P).oracleAt (seatAt six numSix atSix k).1 = some o → o.logLength =
      Johnson.Pack.aOf Johnson.Top.H.csKey (six.get k).1

variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}

/-- **THE FIELD r1_0 OF The35, IN SCOPE, AT THE SIX.** R is a letter. -/
theorem r1_0_eight_six (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hcap : AtCap rest₁)
    (H : LeftSix X N P coll ⟨0, by decide⟩) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf
        (plan₁ (oneAt X)).orc) atSix R coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey
        six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix R) ((atDesc (Fk X N P) (piecesAt
        (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ ::
        (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁
        rest₂ rest₃ dW wEnd)).l₁) 0 :=
  r1_0_eight X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd atSix coll R six numSix decT recOf
      (plan₁ (oneAt X)).orc q₁ hZ hP hm hX hp hdata hcap
    { cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i, seatIs := H.seatIs, seat := rfl,
      cell := H.cell
      j := ⟨0, by decide⟩, memberIs := member10_six, numIs := rfl, orcIs := rfl
      inj := seat_inj_six, apart := shapesApart_six, tie := tie_six _, logs := H.logs,
      mains := mains_six _ }

/-- **THE FIELD r1_1 OF The35, IN SCOPE, AT THE SIX.** R is fixed: kreadFam. -/
theorem r1_1_eight_six (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hcap : AtCap rest₁)
    (H : LeftSix X N P coll ⟨1, by decide⟩) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf
        (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab) coll) (Cl₁
        X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt
        X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab)) ((atDesc (Fk X N P)
        (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
        wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 1 :=
  r1_1_eight X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd atSix coll tab six numSix decT
      recOf (plan₁ (oneAt X)).orc b₁ q₁ hb hZ hP hm hX hp hdata hcap
    { cs := H.cs, m := H.m, fam := H.fam, fits := H.fits, i := H.i, seatIs := H.seatIs,
      seat0 := rfl, seat1 := rfl, cell := H.cell
      j := ⟨1, by decide⟩, memberIs := member11_six, numIs := rfl, orcIs := rfl
      arr := arrOk_six₁ _ decT recOf _
      inj := seat_inj_six, apart := shapesApart_six, tie := tie_six _, logs := H.logs,
      mains := mains_six _ }

end

end LPFD

#print axioms LPFD.mains_six
#print axioms LPFD.r1_0_eight_six
#print axioms LPFD.r1_1_eight_six
