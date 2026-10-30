-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyAtOff.lean: at the full size: WHAT IS OWED FOR THE KEY FILE WITH THE TWO LETTERS off₂ | off₃ WRITTEN: from a later chain's book's tree number to the file's.
Main names.
  `off₂N q` := 6 + q · `off₃N q` := q below 6; 7 at 6; 17 + (q - 7) behind: the tables' own member `atOk_member` (Johnson/RunOne/KeyRows23At.lean) at t₁ := 6 and t₂ := 11: the trees numbered through the file in the order of sending.
  `atOk_six`: `AtOk atSix off₂N off₃N 6`: what the laws of the two sendings and of the last chain's first block will want of these letters · `off_six`: the field `AtFk.off`.
  `The21Off X N P DK`: `The21Tab` (KeyAtTab.lean) at these two: BESIDE THE 21 LAWS NO FIELD IS LEFT. Letters under the ∃: enc · rad.
  `tab_of_off`: it gives `The21Tab`.
OBJECT: `Key.descriptionFromSource X N P` · USER: Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: under the ∃: enc · rad.
Limits. NO LAW IS PAID. The numerals 6 and 11 are THE FULL SIZE's numbers of trees of the first and the shared chain (at the small example the second is 8), TYPED BY HAND, as atSix is; that they are the written data's is a kernel fact in other files, not called here; of the rest: that the shared chain ends with 11 trees has been seen on an honest walk by evaluation; that the last chain's book's place q behind Omega's is the file's tree 17 + (q - 7) is a READING of the frame's bases: shown nowhere. Six other forms stand beside. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyAtTab

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
open Johnson.RunOne.KeyRows23 (atSix AtOk)

/-- The shared chain's book's tree number q is the file's tree 6 + q. -/
def off₂N (q : ℕ) : ℕ := 6 + q

/-- The last chain's book: the first chain's six trees, then Omega's (the shared chain's second), then its own. -/
def off₃N (q : ℕ) : ℕ := if q < 6 then q else if q = 6 then 7 else 17 + (q - 7)

theorem atOk_six : AtOk atSix off₂N off₃N 6 :=
  ⟨rfl, rfl, rfl, rfl, fun q hq => by simp [off₃N, hq]⟩

theorem off_six : ∀ k ∈ [0, 2], off₃N (atSix k).1 = (atSix k).1 := by decide

/-- A test that the field can fail: at the seat of Omega's tree. -/
theorem off_six_no : ¬ ∀ k ∈ [0, 4], off₃N (atSix k).1 = (atSix k).1 := by decide

/-- **WHAT IS OWED, WITH off₂ | off₃ WRITTEN: THE 21 LAWS AND NOTHING BESIDE THEM.** -/
def The21Off (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (x₀ x₁ : Lookup) (bw : Block FirstState Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ → (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    ∃ (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
      (_ : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N

theorem tab_of_off {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} {DK : WholeD} (h : The21Off X N P DK) : The21Tab X N P DK := by
  intro c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  obtain ⟨enc, rad, dS, H⟩ := h c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw' hin
  exact ⟨enc, rad, off₂N, off₃N, dS, H, off_six⟩

end LPFD

#print axioms LPFD.atOk_six
#print axioms LPFD.off_six
#print axioms LPFD.off_six_no
#print axioms LPFD.The21Off
#print axioms LPFD.tab_of_off
