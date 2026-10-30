-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row117Scope.lean: THE KEY FILE's ROW 1.17: THE JOINT CLOSED.
  r1_17_scope   PROVED: THE FIELD r1_17 at the filling of the reading (baseK), FROM: q₁ · hl · hw · sealLast · hdata · AtCap rest₁ · THE THREE EQUATIONS IN SCOPE (ranges | lin | codes are the written key's: five_in_scope, Johnson/RunOne/Law/KeyInScope.lean) · «the plan's samples are 1» · the sending kind's own test on the plan at the place · Left117f AT EVERY Public117
Public117 · «the number is small» · «the place has a tree» ARE NO PREMISES ANY MORE.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row117Eight
import Johnson.Top.Fire.Code.Row117PubFull

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

open Johnson.RunOne.KeyRows1 (Public11 SmpOwn smpOwn_base plan₁)
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry Tie)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB)
open Johnson.RunOne.KeyRows23 (baseK tieS_fam readerOf readerIn words_zero seatAt smGroupsK)
open VerifiableInference.Desc.Key.Fill (ShapesApart symsW)

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
    (at_ : Where) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)


variable (R : KRead Cells Fill.Tab) (l : List (OnBytes.OracleShape × ℕ)) (num : Fin l.length → ℕ)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (bw b₁₇ : Block FirstState Claim) {Kr : Type} [CommRing Kr] (ρ : OnBytes.Model.Reading Kr)



theorem r1_17_scope (x₀ x₁ : Lookup) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hw : sendW (oneAt X) pieces (sent17 X) (g17 X) = some bw)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hcap : AtCap rest₁)
    (h1 : (oneAt X).ranges = Lk6.AtPlan.keyFull.ranges.x) (h2 : (oneAt X).lin = Lk6.AtPlan.keyFull.once.shape) (h5 : (oneAt X).codes = Lk6.AtPlan.keyFull.codes)
    (hsmp : (oneAt X).given.plan.samples = 1)
    (hplan : ∀ msg, linMessageW (oneAt X).lin = some msg → K1.planOkOwn (Johnson.RunOne.KeyRows1.parW' (oneAt X) pieces (g17 X) msg) = true)
    (HL : ∀ (Pb : Johnson.RunOne.KeyRows1.Public117 (oneAt X) pieces (g17 X)) b₁₇ d₁ d₂, (c₁ :: k₁)[17]? = some b₁₇ →
      cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 17 = [d₁, d₂] →
      Left117f X N P DK c₁ k₁ rest₁ at_ coll R l num decT recOf orc₁ b₁₇ ρ Pb d₁ d₂) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) (baseK (oneAt X).codes l num at_ decT recOf orc₁) at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) (baseK (oneAt X).codes l num at_ decT recOf orc₁) at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 17 := by
  obtain ⟨⟨Pb⟩, hsm⟩ := public117_full (oneAt X) pieces (g17 X) h1 h2 h5 hsmp hplan
  exact r1_17_eight X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd at_ coll R l num decT recOf orc₁ bw ρ x₀ x₁ hl hw q₁ hs hdata hcap Pb hsm
    (trees117_full (oneAt X) pieces (g17 X) h2 h5 Pb) (HL Pb)

end

end LPFD

#print axioms LPFD.r1_17_scope
