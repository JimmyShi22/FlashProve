-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Gaps2InScope.lean: THE KEY FILE, THE SHARED CHAIN: THE SIX BRIDGES OF Johnson/RunOne/KeyTestsBridge.lean IN THE GOALS' SCOPE, FROM WHAT THE SEAT HANDS ALONE: what the fold over the history asks of the steps 1 · 3 · 4 · 6 · 7 · 8, any at_ and off₂.
  gap₂_k   ∀ b, (Fk X N P).shared.blocksInOrder[k]? = some b → StepInvP b (TestsAt at_ off₂ X k) (TestsAt at_ off₂ X (k + 1)): the eight blocks by eight_said; «the shape splits» by split_in_scope (Rows2Public.lean).
  fit_left₂   THE FIT: the six ARE the fields g1 · g3 · g4 · g6 · g7 · g8 of Left₂ (Johnson/Top/Fire/Code/KeyASide2Paid.lean): «{ L with g1 := … }»: by Lean's own check of types.
IN FRONT STAND: at 3 · 4 · 7: the description's test on the plan alone (hp); at 1 · 6 · 8: the five in scope. NO NUMBER AND NO PUBLIC FACT IS LEFT AS A PREMISE.
Limits. Calls alone. No member is shown. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Rows2Public
import Johnson.RunOne.KeyTestsBridge
import Johnson.Top.Fire.Code.KeyASide2Paid

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
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)
open Johnson.RunOne.KeyRows23 (TestsAt bridge₂_1 bridge₂_3 bridge₂_4 bridge₂_6 bridge₂_7 bridge₂_8)

section
variable (at_ : Where) (off₂ : ℕ → ℕ) {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
include hZ hP hm hX hp

theorem gap₂_1 :
    ∀ b, (Fk X N P).shared.blocksInOrder[1]? = some b → StepInvP b (TestsAt at_ off₂ X 1) (TestsAt at_ off₂ X 2) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  exact bridge₂_1 at_ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 (split_in_scope hZ hP hm hX hp)

omit hZ hP hm hX in
theorem gap₂_3 :
    ∀ b, (Fk X N P).shared.blocksInOrder[3]? = some b → StepInvP b (TestsAt at_ off₂ X 3) (TestsAt at_ off₂ X 4) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  exact bridge₂_3 at_ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h8

omit hZ hP hm hX in
theorem gap₂_4 :
    ∀ b, (Fk X N P).shared.blocksInOrder[4]? = some b → StepInvP b (TestsAt at_ off₂ X 4) (TestsAt at_ off₂ X 5) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  exact bridge₂_4 at_ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h8

theorem gap₂_6 :
    ∀ b, (Fk X N P).shared.blocksInOrder[6]? = some b → StepInvP b (TestsAt at_ off₂ X 6) (TestsAt at_ off₂ X 7) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  exact bridge₂_6 at_ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 (split_in_scope hZ hP hm hX hp)

omit hZ hP hm hX in
theorem gap₂_7 :
    ∀ b, (Fk X N P).shared.blocksInOrder[7]? = some b → StepInvP b (TestsAt at_ off₂ X 7) (TestsAt at_ off₂ X 8) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  exact bridge₂_7 at_ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h8

theorem gap₂_8 :
    ∀ b, (Fk X N P).shared.blocksInOrder[8]? = some b → StepInvP b (TestsAt at_ off₂ X 8) (TestsAt at_ off₂ X 9) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  exact bridge₂_8 at_ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 (split_in_scope hZ hP hm hX hp)

/-- **THE FIT.** -/
def fit_left₂ (D : WholeD) (L : Left₂ X N P D at_ off₂) : Left₂ X N P D at_ off₂ :=
  { L with
    g1 := gap₂_1 at_ off₂ hZ hP hm hX hp, g3 := gap₂_3 at_ off₂ hp
    g4 := gap₂_4 at_ off₂ hp, g6 := gap₂_6 at_ off₂ hZ hP hm hX hp
    g7 := gap₂_7 at_ off₂ hp, g8 := gap₂_8 at_ off₂ hZ hP hm hX hp }

end

end LPFD

#print axioms LPFD.gap₂_1
#print axioms LPFD.gap₂_3
#print axioms LPFD.gap₂_4
#print axioms LPFD.gap₂_6
#print axioms LPFD.gap₂_7
#print axioms LPFD.gap₂_8
#print axioms LPFD.fit_left₂
