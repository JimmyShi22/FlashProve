-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyAtWritten.lean: at the full size: WHAT IS OWED FOR THE KEY FILE WITH THE LAST TWO LETTERS WRITTEN: enc AND rad ARE TERMS, NOT BOUND BY ∃.
Main names.
  `encN X P`: `encOf` (Johnson/RunOne/KeyRow24.lean: a definition with code: row x of the code's generator matrix on the message and on the random tail) at the shared chain's fold's shape · `encIs_encN`: that file's `encIs_encOf`, called.
  `radN`: `OnBytes.Params.recordRadius`.
  `paidW`: THE LIST on this road: `paidNow` (KeyAtRest.lean) and six rows more.
  `paidW_in_scope`: each row of the list has its law at the written terms: the rows of `paidNow` by `paid_in_scope`, which holds at every enc rad, called at these; the others one line a row:
    r1_15: `r1_15_at_name` (Johnson/RunOne/Law/K12Row15AtName.lean), at tab := tabN: it reads neither enc nor rad; it spends one premise more than the others: the place's numbers are the maker's (`rangesNumbers m = .ok N`): at the seat one of the five equations. (It stands in this road's list, not in `paidNow`, as r2_7 does.)
    r2_2 · r2_5 (the shared chain's two sendings): `r2_2_at_name` | `r2_5_at_name` (Rows2SendAtName.lean): they hold at every enc rad; called at these two; in front of them stands just what stands in front of `r2_7_at_enc`.
    r2_1 · r2_4 · r2_7: `r2_1_at_enc` | `r2_4_at_enc` | `r2_7_at_enc` (Rows2TiesB.lean): stated at just these two terms; nothing in front but what the seat hands. (r2_7 holds at every enc rad: it stands in this road's list, not in `paidNow`.)
  `RestOffW paid X N P DK`: `RestOff`'s text (taken by program; its «Claim» written `Key.Claim`: with this file's imports the short name is ambiguous) with «∃ enc rad» struck and `encN X P` | `radN` in the letters' places.
  `off_of_restW`: in scope: `RestOffW paidW` gives `The21Off`: the witness under its ∃ is ⟨encN X P, radN, …⟩.
In this file the digest cfg is FREE.
OBJECT: `Key.descriptionFromSource X N P` in scope · USER: Johnson/Goal/Conditions/KeyAtTheSeatWritten.lean · LETTERS: none under the ∃; one statement (an inhabitant).
Limits. The three rows that are not in the list (2.9, 2.10, 3.2) are not proved in this file, and on this road they are asked at this enc and this rad. RowsK12AtName.lean proves them (`r2_9_at_name`, `r2_10_at_name`, `r3_2_at_name`), in scope, with two premises more than this file's list spends: laterPlaces m = .ok P, and that every test of Key.lawsAsk says yes; the seat hands both. `keyOpenAt_holds` (Johnson/Goal/Conditions/KeyOpenHolds.lean) supplies them at these terms; the limits in that file's head hold here too. Whether a row of the list counts toward the key file's soundness is not judged in this file. The full size alone. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyAtRest
import Johnson.Top.Fire.Code.Rows2TiesB
import Johnson.RunOne.Law.K12Row15AtName
import Johnson.Top.Fire.Code.Rows2SendAtName
import Johnson.RunOne.KeyRow24

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
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (atSix p14At)

/-- **THE WRITTEN enc.** -/
def encN (X : Source) (P : LaterPlaces) : (ℕ → OnBytes.E) → ℕ → OnBytes.E :=
  Johnson.RunOne.KeyRows23.encOf (p14At X P).par.S.fold

theorem encIs_encN (X : Source) (P : LaterPlaces) :
    Johnson.RunOne.KeyRows23.EncIs OnBytes.Model.Reading.gl (p14At X P).par.S.fold (encN X P) :=
  Johnson.RunOne.KeyRows23.encIs_encOf OnBytes.Model.Reading.gl (p14At X P).par.S.fold

/-- **THE WRITTEN rad.** -/
def radN : ℕ := OnBytes.Params.recordRadius

/-- **THE ROWS THAT ARE LAID IN ON THIS ROAD.** -/
def paidW : List Row := paidNow ++ [.r1_15, .r2_1, .r2_2, .r2_4, .r2_5, .r2_7]

theorem paidW_nodup : paidW.Nodup := by decide

/-- **WHAT IS OWED, AT THE WRITTEN enc AND rad.** -/
def RestOffW (paid : List Row) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (x₀ x₁ : Lookup) (bw : Block FirstState Key.Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ → (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    ∃ (_ : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      TheRest X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) (encN X P) radN collN off₂N off₃N paid

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (DK : WholeD)
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hN : rangesNumbers m = .ok N)
    (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
include hZ hP hm hX hp hN hwant hdata hDK

/-- **EACH ROW OF THE LIST HAS ITS LAW AT THE WRITTEN TERMS.** -/
theorem paidW_in_scope (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃) :
    ∀ r ∈ paidW, lawAt X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) (encN X P) radN collN off₂N off₃N r := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact paid_in_scope DK hZ hP hm hX hp hwant hdata hDK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ (encN X P) radN r h
  · cases r <;> first
      | exact absurd h (by decide)
      | exact Johnson.RunOne.Law.K12AtThe21.r1_15_at_name DK tabN c₁ k₁ c₂ k₂ c₃ k₃ hZ hP hm hX hN hp hwant hdata hDK q₁
      | exact r2_1_at_enc X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
      | exact r2_2_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ (encN X P) radN q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
      | exact r2_5_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ (encN X P) radN q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
      | exact r2_4_at_enc X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK
      | exact r2_7_at_enc X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hdata hDK

/-- **In scope the rest at the written terms gives the 21 at The21Off's.** -/
theorem off_of_restW (h : RestOffW paidW X N P DK) : The21Off X N P DK := by
  intro c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  obtain ⟨dS, H⟩ := h c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  exact ⟨encN X P, radN, dS, the21_of_rest paidW (paidW_in_scope DK hZ hP hm hX hp hN hwant hdata hDK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃) H⟩

end

end LPFD

#print axioms LPFD.encIs_encN
#print axioms LPFD.paidW_nodup
#print axioms LPFD.RestOffW
#print axioms LPFD.paidW_in_scope
#print axioms LPFD.off_of_restW
