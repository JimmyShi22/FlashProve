-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row30AtName.lean: THE KEY FILE, THE LAST CHAIN: THE CALL OF ROW 3.0: The21's field r3_0 AT The21Off's WRITTEN TERMS, IN THE GOALS' SCOPE, FROM WHAT THE SEAT HANDS ALONE.
OBJECT. KeepsAt (On₃' …) (Cl₃ …) ‹the maker's row of chain 3› 0 at capRest ×3 · () () · baseAt X decN recBack · atSix · readAt tabN · collN · off₂N · off₃N.
HOW. r3_0_base (Johnson/RunOne/KeyPinsAtBase3.lean: the tables' Keeps at a piece that holds «held» of the description's own block, at the tables' own reading) CALLED at the maker's own piece (keepsAt_of_law₃, at the cap's own error) and lifted over the history (KeepsAt.reached). EVERY PREMISE OF IT IS PAID BY A CALL: the block at its place (the head q₃) · the piece holds it (rfl) · the open pins' trees lie below the piece's base (bases_of_all at basesAll_at_six) · the collision letter reads the stored cells alone (cellOnly_collN) · «same» is equality under a reading into a field (rfl, at Reading.gl) · the first chain's plan has the sized key's shape (one_full · shape_full) · the plan's two tables are inverse at W (num_at_w: the plan's own text, with the number of stages in scope) · the seats and the two offsets fit (atOk_six, at the number of stages in scope: one_full and stages_full, Johnson/RunOne/KeyScopeNums.lean) · the reading's numbers of the first chain are the plan's (rfl) · the letter sm goes with a message that is laid again under another number with its sample rows renamed (smMovesK).
  num_at_w          where the chain has a stage: the plan's number of W's message goes back to 2.
IN FRONT STAND: the three heads · the five in scope · wantedOk · the pin on the data. NO NUMBER AND NO PUBLIC FACT IS LEFT AS A PREMISE.
THE CAUTION STANDS: until a member of the promise at this border is shown, the law may be true and empty at the real protocol, and counts as closing nothing.
Limits. Calls alone: no new law. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.Top.Fire.Code.KeyBasesAtSix
import Johnson.Top.Fire.Code.PieceSame
import Johnson.RunOne.KeyPinsAtBase3
import Johnson.RunOne.KeyFillSmMoves
import Johnson.RunOne.KeyScopeNums

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
open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (numSix atSix kreadFam baseK)

/-- Where the chain has a stage, the plan's number of W's message goes back to 2. -/
theorem num_at_w (one : OnBytes.Params.OneTime) (h : 0 < one.ranges.stages.length) :
    ∀ o, (Johnson.RunOne.KeyRows1.plan₁ one).orc 2 = some o → (Johnson.RunOne.KeyRows1.plan₁ one).num o = some 2 := by
  intro o ho
  have e : o = 1 + 2 * one.ranges.stages.length := by
    have ho' : some (1 + 2 * one.ranges.stages.length) = some o := ho
    exact (Option.some.inj ho').symm
  subst e
  show (if (1 + 2 * one.ranges.stages.length == 0) = true then some 0
    else if (1 + 2 * one.ranges.stages.length == 1) = true then some 1
    else if (1 + 2 * one.ranges.stages.length == 1 + 2 * one.ranges.stages.length) = true then some 2 else none) = some 2
  have h0 : (1 + 2 * one.ranges.stages.length == 0) = false := beq_false_of_ne (by omega)
  have h1 : (1 + 2 * one.ranges.stages.length == 1) = false := beq_false_of_ne (by omega)
  simp [h0, h1]

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **The21's FIELD r3_0 AT The21Off's TERMS, IN SCOPE.** -/
theorem r3_0_at_name (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₃' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) collN off₂N off₃N) (Cl₃ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃) 0 := by
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.2
  have hst : (oneAt X).ranges.stages.length = 4 := by
    rw [(one_full hZ hP hm hX hp).1]
    exact Johnson.RunOne.KeyLetters.stages_full
  have hat : Johnson.RunOne.KeyRows23.AtOk atSix off₂N off₃N ((oneAt X).ranges.stages.length + 2) := by
    rw [hst]
    exact atOk_six
  refine KeepsAt.reached _ _ (rowBlocksF₃ q₃ 0) ?_
  show KeepsAt (On₃ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) collN off₂N off₃N) (Cl₃ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃) 0
  refine keepsAt_of_law₃ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () _ _ 0 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).second.blocksInOrder[0]? = some b := by
    rw [show (descriptionFromSource X N P).second.blocksInOrder = c₃ :: k₃ from q₃]
    exact hb
  refine ⟨capRest 0 ds, ?_, Err.le_refl _⟩
  exact Johnson.RunOne.KeyRows23.r3_0_base (Fk X N P) (fr₃ X N P (DK.at frS.P.T.a)) (baseAt X decN recBack) atSix (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN)
    (oneAt X).given.plan.samples [0] collN (Johnson.RunOne.KeyRows23.srcOk (ownTest P)) off₂N off₃N ((oneAt X).ranges.stages.length + 2) rdE X N P
    (pieceOf (held b) base ds back (capRest 0 ds)) b hb' rfl (hB 0 _ hrow) cellOnly_collN rfl
    ((one_full hZ hP hm hX hp).2.1.trans (shape_full hZ hP hm hX hp).symm) (num_at_w (oneAt X) (by omega)) hat rfl
    (Johnson.RunOne.KeyRows23.smMovesK Johnson.Top.H.csKey six numSix atSix decN recBack (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).orc)

/-- **THE FIT**: the theorem's conclusion IS The21's field r3_0 at The21Off's terms, at any enc rad: by Lean's own check of types. -/
def fit_30 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N :=
  { H with r3_0 := r3_0_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ hZ hP hm hX hp hwant hDK }

end

end LPFD

#print axioms LPFD.num_at_w
#print axioms LPFD.r3_0_at_name
#print axioms LPFD.fit_30
