-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12AtThe21.lean: IT SHOWS THAT THE FIELD 1.15 OF THE KEY FILE's TABLES TAKES A LAW OF THE PROXIMITY TEST AT ITS OWN RECORD, AND NOTHING ON WHETHER THAT FIELD CAN BE PAID. One statement with its proof: a call.
OBJECT. The field `r1_15` of `LPFD.The21` (Johnson/Top/Fire/Code/The35.lean): `KeepsAt` at the woven tables On₁' and Cl₁ (Johnson/Top/Fire/Code/KeyTablesR.lean; Johnson/RunOne/KeyRowsAtFk.lean), at the 15th piece of the maker's own cut of the first chain. The conclusion below is that field's type, taken over from that file sign for sign; so are the letters.
USER. Whoever fills `The21`.
LETTERS. Those of The35.lean. Premises: hf (the description's flat list is c₁ :: k₁) · hl (the plan has two lookups) · hpay: `Pays` (Johnson/RunOne/Law/K12AtField.lean) at these tables: at the maker's own base, stretch and "put behind": some law of the kind's block's piece at its own record, at errors that are at most the row's, and the two implications: (I1) On₁' 15 gives the law's promise at the record that the ranges' seat's entering makes; (I2) where the maker's piece puts out b: On₁' 15, the entering, the leaving and the law's conclusion give On₁' 16 at b, and Cl₁ 16 at b gives Cl₁ 15.

  r1_15_of: the statement: keepsAt_rng_15 (K12AtField.lean) called at these tables: that theorem is general in the tables, so there is no tie of tables and no second law.
Limits. hpay holds all the weight, and it is not shown that it can be met: row 15 of the tables closes "all open rows of the group hold at the witness" and "message 1 is a member of its committed word's list that meets its sample", and lays message 1: (I2) holds that whole way. A field alone is worth nothing (The35.lean's own Limits). Nothing on soundness, nothing on hiding.

-/
import Johnson.Top.Fire.Code.KeyTablesR
import Johnson.RunOne.Law.K12AtField

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

/-- **The field 1.15 from `Pays` at the woven tables.** -/
theorem r1_15_of (hf : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hpay : ∀ (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[15]? =
        some (pieceOf (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))) base ds back (rest₁ 15 ds)) →
      K12AtField.Pays (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N)
        (fun s t => enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) s = .ok t)
        (fun s t' s' => leaveRanges s t' = .ok s') (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim)))
        (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 15 base ds back (rest₁ 15 ds)) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15 :=
  K12AtField.keepsAt_rng_15 X N P (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd _ _ hf hl hpay

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_of
