-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASide2Two.lean: THE SHARED CHAIN's STATE's SIDE FROM THE HISTORY, IN SCOPE:
  ELEVEN OF THIRTEEN LEGS PAID: g9_scope | g10_scope (Johnson/RunOne/Law/StepSide2.lean:
  the two proximity tests) CALLED: Four₂ (KeyASide2Start.lean) FALLS TO TWO.
  Two₂            A NAMED PREMISE: THE TWO STEPS THAT ARE LEFT: g2 | g5 (the two sendings): part
    2's (tests₂_23 | tests₂_56 lie; its step₂_2 | step₂_5 in the pair form are at Lean)
  four₂_of_two      PROVED: Two₂ and the scope's six equations give Four₂
  aSide₂_two_left  PROVED: k ≤ 12: the fold in scope under Two₂ and fits
  guard_32_two     PROVED: row 3.2's guard at public numbers (KeyOmegaPublic.lean's
    guard_32_public) under Two₂ and fits
OBJECT · USER: as KeyASide2Start.lean | KeyOmegaPublic.lean · LETTERS: off₂ (the fold); none (the
  guard).
STILL AN IMPLICATION: FROM BORDER 3 ON IT SAYS NOTHING UNTIL g2 IS PAID.
(Where this and lean/THEOREM.md differ, the page holds.) EMPTY WHERE NOTHING IS
  REACHED. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyOmegaPublic
import Johnson.RunOne.Law.StepSide2

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

open OnBytes.Params (OneTime Setting)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (CellOnly)

open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.KeyRows23 (atSix)

open Johnson.RunOne.Law.StepSideGaps (gaps_of)
open Johnson.RunOne.Law.StepSideAtFk (H₀ H₁)

open Johnson.RunOne.KeyRows23
open VerifiableInference.Desc.K12 (T12)
open Johnson.RunOne.Law.StepSide2 (g9_scope g10_scope)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made}
variable (D : WholeD) (off₂ : ℕ → ℕ)

/-- **The two steps that are left**: the two sendings. -/
structure Two₂ : Prop where
  /-- 2 → 3: the sending of o_u with its mask -/
  g2 : ∀ b, (Fk X N P).shared.blocksInOrder[2]? = some b → StepInvP b (T₂ X atSix off₂ 2) (T₂ X atSix off₂ 3)
  /-- 5 → 6: the sending of Omega with the split -/
  g5 : ∀ b, (Fk X N P).shared.blocksInOrder[5]? = some b → StepInvP b (T₂ X atSix off₂ 5) (T₂ X atSix off₂ 6)

theorem four₂_of_two (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay
    cfg = .ok m) (hX : sourceOf m = .ok X)
    (hL : laterPlaces m = .ok P) (hp : (Fk X N P).planOk = true) (G : Two₂ X N P off₂) : Four₂ X N P
        off₂ :=
  ⟨G.g2, G.g5, g9_scope X N P atSix off₂ hZ hP hm hX hL hp, g10_scope X N P atSix off₂ hZ hP hm hX
      hL hp⟩

/-- **The fold in scope, under the two.** -/
theorem aSide₂_two_left (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
        (G : Two₂ X N P off₂)
    (k : ℕ) (a : P₂ × St₂) (hk : k ≤ 12) (hist : Hist₂ (Fk X N P) D k a)
    (hfit : a.1.1.key.fits (shapeAt X).fold.index = true) : T₂ X atSix off₂ k a :=
  aSide₂_made X N P c₁ k₁ D off₂ q₁ hZ hP hm hX hp hw hN (four₂_of_two X N P off₂ hZ hP hm hX hL hp
      G) k a hk hist hfit

/-- **Row 3.2's guard at public numbers, under the two.** -/
theorem guard_32_two (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX
        : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (hN : rangesNumbers m = .ok N)
        (G : Two₂ X N P off₂N)
    (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) (hfit : a.1.1.key.fits (shapeAt
        X).fold.index = true)
    (t : T12) (ht : VerifiableInference.Desc.K12.Seat.enterOwn a.2 = .ok t) :
    H2K.First.BookOrdW ((oneAt X).ranges.stages.length + 2) 1 t.book ∧ t.book.trees.size = (oneAt
        X).ranges.stages.length + 2 + 1 ∧ t.roots = 0 :=
  guard_32_public X N P c₁ k₁ D q₁ hZ hP hm hX hp hw hN (four₂_of_two X N P off₂N hZ hP hm hX hL hp
      G) a h hfit t ht

end

end LPFD

#print axioms LPFD.four₂_of_two
#print axioms LPFD.aSide₂_two_left
#print axioms LPFD.guard_32_two
#print axioms Johnson.RunOne.Law.StepSide2.g9_scope
#print axioms Johnson.RunOne.Law.StepSide2.g10_scope
