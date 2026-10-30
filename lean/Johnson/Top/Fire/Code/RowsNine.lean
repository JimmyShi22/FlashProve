-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowsNine.lean: THE KEY FILE's ROWS 1.0 | 1.1, LEVEL 9: THE THREE THINGS THAT
  LEVEL 8 LEFT (LeftSix: SeatFits with its seat · logs · CollCell coll) ARE PAID BY CALLS:
  NO STRUCTURE OF DEBTS IS LEFT.
OBJECT: The35.r1_0 | r1_1 at B := baseK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc
  (the abbrev baseAt X decT recOf unfolds to it) · at_ := atSix · R a letter (1.0) | kreadFam
  csKey six numSix atSix tab (1.1; the abbrev readAt tab) · USER: The21AtBase |
  The21AtName's filler · LETTERS: X N P · the maker's cut and rests · R | tab · coll · decT recOf ·
  the scope's Zp X₀ cfg m.
  noFault0 | noFault1   IN SCOPE: the library's test on a seat finds no fault at (shIdx, tree 0,
    tenant 0) | (shMul, tree 1, tenant 0): n01_scope at five_in_scope's three equations
  fits_one     a list of ONE member whose seat has no fault fits: seatFits_iff |
    fitsAt_of_noFault (both in Johnson/RunOne/KeyFillMeet.lean; over seat_of_noFault)
  logs_of      what F tells of the tree at such a seat has the log-length of the member's code:
    seat_of_noFault (Johnson/Desc/Sound/PlanMemProofs.lean)
  leftSix0 | leftSix1   LeftSix, from CellOnly coll alone, in scope
  r1_0_nine | r1_1_nine   PROVED: from q₁ (· hb) · the five in scope · hdata · AtCap rest₁ ·
    CellOnly coll
SeatFits STANDS HERE AT A LIST OF ONE MEMBER: it says nothing of the other five seats: the two
  rows spend it for «shownAll» at their own seat alone.
NO MEMBER OF THE ROWS' GUARDS (On₁' … 0 | 1) IS SHOWN HERE. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowsEightSix
import Johnson.RunOne.KeyFillMeet

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
open Johnson.RunOne.KeyRows23 (smGroupsK kreadFam kreadFam_same numSix atSix seatFits_iff
    fitsAt_of_noFault)
open Johnson.RunOne.KeyLetters (n01_scope)

/-- A list of one member whose seat has no fault fits. -/
theorem fits_one {XI : Type} (F : FileDescription XI) (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (e j t
           : ℕ) (tag : String) (h : seatFaultAt F cs tag s j t = none) :
    Sound.SeatFits F cs [(s, e)] (fun _ => (j, t)) :=
  (seatFits_iff cs [(s, e)] (fun _ => (j, t)) F).2 fun i => fitsAt_of_noFault cs [(s, e)] (fun _ =>
      (j, t)) F i tag (by
    obtain ⟨v, hv⟩ := i
    obtain rfl : v = 0 := Nat.lt_one_iff.1 hv
    exact h)

/-- What F tells of the tree at a seat without a fault has the log-length of the member's code. -/
theorem logs_of {XI : Type} (F : FileDescription XI) (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (j t :
           ℕ) (tag : String) (h : seatFaultAt F cs tag s j t = none) :
    ∀ o, F.oracleAt j = some o → o.logLength = Johnson.Pack.aOf cs s := by
  obtain ⟨o', _, ho', _, hl, _⟩ := Sound.seat_of_noFault F cs tag s j t h
  intro o ho
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans ho)
  exact hl

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


variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}

theorem noFault0 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg
    = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    seatFaultAt (Fk X N P) Johnson.Top.H.csKey "row 1.0" Johnson.Top.H.shIdx 0 0 = none := by
  obtain ⟨-, hr, -, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  exact (n01_scope X N P hi hc hr "row 1.0" "row 1.1").1

theorem noFault1 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg
    = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) :
    seatFaultAt (Fk X N P) Johnson.Top.H.csKey "row 1.1" Johnson.Top.H.shMul 1 0 = none := by
  obtain ⟨-, hr, -, hi, hc⟩ := five_in_scope hZ hP hm hX hp
  exact (n01_scope X N P hi hc hr "row 1.0" "row 1.1").2

/-- **LeftSix at row 1.0, from CellOnly coll alone, in scope.** -/
def leftSix0 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg =
    .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hc : CellOnly coll) : LeftSix X N P coll ⟨0, by decide⟩ :=
  { cs := Johnson.Top.H.csKey, m := [(Johnson.Top.H.shIdx, 6130)], fam := fun _ => (0, 0)
    fits := fits_one _ _ _ _ _ _ _ (noFault0 X N P hZ hP hm hX hp), i := ⟨0, Nat.one_pos⟩,
    seatIs := rfl
    cell := fun y y' r e => (hc y y' r e).1
    logs := logs_of _ _ _ _ _ _ (noFault0 X N P hZ hP hm hX hp) }

/-- **LeftSix at row 1.1.** -/
def leftSix1 (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg =
    .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hc : CellOnly coll) : LeftSix X N P coll ⟨1, by decide⟩ :=
  { cs := Johnson.Top.H.csKey, m := [(Johnson.Top.H.shMul, 3131959)], fam := fun _ => (1, 0)
    fits := fits_one _ _ _ _ _ _ _ (noFault1 X N P hZ hP hm hX hp), i := ⟨0, Nat.one_pos⟩,
    seatIs := rfl
    cell := fun y y' r e => (hc y y' r e).1
    logs := logs_of _ _ _ _ _ _ (noFault1 X N P hZ hP hm hX hp) }

/-- **THE FIELD r1_0 OF The35, IN SCOPE, AT THE SIX: NO STRUCTURE OF DEBTS IS LEFT.** R is a letter.
-/
theorem r1_0_nine (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hcap : AtCap rest₁) (hc : CellOnly
        coll) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf
        (plan₁ (oneAt X)).orc) atSix R coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey
        six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix R) ((atDesc (Fk X N P) (piecesAt
        (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ ::
        (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁
        rest₂ rest₃ dW wEnd)).l₁) 0 :=
  r1_0_eight_six X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd coll R decT recOf q₁ hZ hP hm
      hX hp hdata hcap (leftSix0 X N P coll hZ hP hm hX hp hc)

/-- **THE FIELD r1_1 OF The35, IN SCOPE, AT THE SIX: NO STRUCTURE OF DEBTS IS LEFT.** R is fixed:
kreadFam. -/
theorem r1_1_nine (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hb : (c₁ :: k₁)[1]? = some b₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hcap : AtCap rest₁) (hc : CellOnly
        coll) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf
        (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab) coll) (Cl₁
        X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt
        X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab)) ((atDesc (Fk X N P)
        (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
        wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂
        k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 1 :=
  r1_1_eight_six X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd coll tab decT recOf b₁ q₁ hb
      hZ hP hm hX hp hdata hcap (leftSix1 X N P coll hZ hP hm hX hp hc)

end

end LPFD

#print axioms LPFD.fits_one
#print axioms LPFD.logs_of
#print axioms LPFD.noFault0
#print axioms LPFD.noFault1
#print axioms LPFD.leftSix0
#print axioms LPFD.leftSix1
#print axioms LPFD.r1_0_nine
#print axioms LPFD.r1_1_nine
