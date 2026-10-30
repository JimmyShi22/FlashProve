-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12AtThe21On.lean: THE FIELD 1.15 OF THE KEY FILE's TABLES FROM `Pays` AT THE PROMISE WITHOUT THE HISTORY. One statement; its proof is two calls. IT SHOWS A FORM; NOTHING ON WHETHER THE FIELD CAN BE PAID.
OBJECT. The field `r1_15` of `LPFD.The21` (Johnson/Top/Fire/Code/The35.lean), at the woven promise On₁' := On₁ ∧ the history (Johnson/Top/Fire/Code/KeyTablesR.lean).
USER. Whoever fills that field and does not spend the history.
LETTERS. Those of The35.lean. Premises: hf · hl · hpay: as r1_15_of's (Johnson/RunOne/Law/K12AtThe21.lean), BUT `Pays` AT On₁, NOT On₁'.

  r1_15_of_on: the statement: keepsAt_rng_15 (K12AtField.lean) at On₁ | Cl₁, lifted by `KeepsAt.reached` (Johnson/Top/Fire/Code/Reached.lean) and `rowBlocksF₁` (Johnson/Top/Fire/Code/RowsWoven.lean): the form in which the tables' files fill their own fourteen fields.
AGAINST r1_15_of: (I2) DOES NOT OWE THE HISTORY AT 16; in exchange (I1) | (I2) may not spend the history at 15.
Limits. hpay holds all the weight; no non-degenerate instance is shown. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12AtThe21

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.K12AtThe21
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
open VerifiableInference.Desc.K12
open Johnson.RunOne.Sound (bareB)
open LPFD

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
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
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (notBad : List OnBytes.E → Strs → Prop) (off₂ off₃ : ℕ → ℕ)

/-- **The field 1.15 from `Pays` at the promise without the history.** -/
theorem r1_15_of_on (hf : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hpay : ∀ (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[15]? =
        some (pieceOf (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))) base ds back (rest₁ 15 ds)) →
      K12AtField.Pays (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N)
        (fun s t => enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) s = .ok t)
        (fun s t' s' => leaveRanges s t' = .ok s') (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim)))
        (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 15 base ds back (rest₁ 15 ds)) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15 :=
  KeepsAt.reached _ _ (rowBlocksF₁ hf 15)
    (K12AtField.keepsAt_rng_15 X N P (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd _ _ hf hl hpay)

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_of_on
