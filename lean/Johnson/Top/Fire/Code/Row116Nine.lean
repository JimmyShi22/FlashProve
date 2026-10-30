-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116Nine.lean: THE KEY FILE's ROW 1.16 (the batching of the table's rows: the kind K13), IN THE GOALS' SCOPE, AT THE FILLING's OWN LETTERS (baseK, Johnson/RunOne/KeyFillSeed.lean: the six written seats): every premise of r1_16_whole is paid by a call, but one (hB), which Row116Ten.lean pays.
OBJECT: The35.r1_16 at B := baseK csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc · R := kreadFam csKey six numSix atSix tab · USER: the filler of The21AtBase (KeyAtBase.lean) | The21AtName (KeyAtName.lean) · LETTERS: X N P · the maker's cut and rests · tab · coll · decT recOf · Zp X₀ cfg m.
  r1_16_nine      **THE FIELD r1_16** FROM q₁ · q₂ · q₃ (the three chains' heads: The21Handed hands them) · row 1.17's ten premises · hB : BelowAt116 X
  r1_16_at_name   «THE CALL»: the same at The21Off's written terms (KeyAtOff.lean) · fit_16: THE FIT BY LEAN's OWN CHECK OF TYPES
WHICH CALL PAYS WHICH PREMISE OF r1_16_whole: hl | hw: hl_in_scope | hw_in_scope (KeyPublicAtSeat.lean) · hG (ReadsL at the reading): readsLK (Johnson/RunOne/KeyFillSeed.lean) · hb₁ at 16 (the pinned trees lie below the piece's base): four_of_all (BasesOk.lean) at basesAll_at_six (KeyBasesAtSix.lean) · sealLast: sealLast_of_planOk (Johnson/Flat/Dec/PlanOkForFree.lean) · hst | PubPile: pub_of_full at five_in_scope's two equations · hsame: kreadFam_same (Johnson/RunOne/KeyFillSame.lean) · hle: hle_of at AtCap rest₁ and hB.
hB (BelowAt116 X: the half of hle that Row116Cap.lean leaves to the kind K13's files) is a theorem in scope: belowAt116_full (Row116Join.lean), from three facts that the kernel checks. Here hB stays a premise; Row116Ten.lean supplies it (r1_16_ten, r1_16_at_name_ten).
IT STANDS OVER Johnson/Desc/K13/Law/GoodAny.lean. NO MEMBER OF THE ROW's GUARD (On₁' … 16) IS SHOWN. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row116Cap
import Johnson.Top.Fire.Code.Row116PubFull
import Johnson.Top.Fire.Code.RowsNine
import Johnson.Top.Fire.Code.KeyBasesAtSix
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
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry Tie planOkOwn)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)
open Johnson.RunOne.KeyRows23 (baseK tieS_fam readerOf readerIn words_zero seatAt)
open VerifiableInference.Desc.Key.Fill (ShapesApart symsW six)
open Johnson.RunOne.KeySendGood (SendAsks asks_in_scope cond_of parIdx parMsg fullIdx fullMsg idx_at msg_at idx_pays msg_pays pays_bare rounds_idx rounds_msg seed_kind)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.KeyRows1 (Public11 SmpOwn smpOwn_base plan₁)
open Johnson.RunOne.KeyRows23 (smGroupsK kreadFam kreadFam_same numSix atSix seatFits_iff fitsAt_of_noFault)
open Johnson.RunOne.KeyLetters (n01_scope)

open Johnson.RunOne.KeyRows23 (readsLK)
open Johnson.G (writtenKFull)

section
variable {Cells Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)

variable (R : KRead Cells Fill.Tab) (tab : Cells → ℕ → ℕ → OnBytes.F)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec)


variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}


/-- **THE FIELD r1_16 OF The35, IN SCOPE, AT THE SIX.** R is fixed: kreadFam. -/
theorem r1_16_nine (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = writtenKFull)
    (hcap : AtCap rest₁) (hc : CellOnly coll) (hB : BelowAt116 X) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab) coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab)) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 16 := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
    (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1)))
  have h5s := five_in_scope hZ hP hm hX hp
  have hs := sealLast_of_planOk _ hp
  have hall := basesAll_at_six hZ hP hm hX hp hwant hDK
  have hb := (four_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd atSix hall q₁ q₂ q₃).1 16
  exact r1_16_whole X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab) coll x₀ x₁ bw q₁ hl hw hc
    (readsLK _ _ _ _ _ _ _) hb hs hdata (pub_of_full (oneAt X) h5s.2.1 h5s.2.2.1).1 (pub_of_full (oneAt X) h5s.2.1 h5s.2.2.1).2
    (kreadFam_same Johnson.Top.H.csKey six numSix atSix tab)
    (hle_of X N P DK c₁ k₁ rest₁ x₀ x₁ bw q₁ hl hw hs hdata hcap hB)

end

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **The21's FIELD r1_16 AT The21Off's TERMS, IN SCOPE.** -/
theorem r1_16_at_name (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) (hB : BelowAt116 X) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) collN) (Cl₁ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁) 16 :=
  r1_16_nine X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () collN tabN decN recBack q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK atCap_capRest cellOnly_collN hB

/-- **THE FIT**: by Lean's own check of types. -/
def fit_16 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) (hB : BelowAt116 X)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N :=
  { H with r1_16 := r1_16_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK hB }

end

end LPFD

#print axioms LPFD.r1_16_nine
#print axioms LPFD.r1_16_at_name
#print axioms LPFD.fit_16
