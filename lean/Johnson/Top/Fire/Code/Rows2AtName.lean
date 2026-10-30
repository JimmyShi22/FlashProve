-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Rows2AtName.lean: THE KEY FILE, THE SHARED CHAIN: THE CALLS OF ROWS 2.3 · 2.6 · 2.8: The21's fields r2_3 · r2_6 · r2_8 AT The21Off's WRITTEN TERMS, IN THE GOALS' SCOPE, FROM WHAT THE SEAT HANDS ALONE.
OBJECT. KeepsAt (On₂' …) (Cl₂ …) ‹the maker's row of chain 2› k at capRest ×3 · () () · baseAt X decN recBack · atSix · readAt tabN · collN · off₂N, any enc rad.
HOW. r2_k_seat (Johnson/RunOne/KeyRowsAtSeat.lean: the tables' Keeps at a piece that holds «held» of the description's own block) CALLED at the maker's own piece (keepsAt_of_law₂, at the cap's own error) and lifted over the history (KeepsAt.reached). EVERY PREMISE OF IT IS PAID BY A CALL: the eight blocks (eight_said) · the shape splits (split_in_scope) · the block at its place (the head q₂) · the piece holds it (rfl) · the open pins' trees lie below the piece's base (bases_of_all at basesAll_at_six) · the collision letter reads the stored cells alone (cellOnly_collN) · «same» is equality under a reading into a field (rfl, at Reading.gl) · the letter sm reads neither a message's groups nor its ledger (smOnlyK).
IN FRONT STAND: the three heads · the five in scope · wantedOk · the pin on the data. NO NUMBER AND NO PUBLIC FACT IS LEFT AS A PREMISE.
THE CAUTION STANDS: until a member of the promise at these borders is shown, each of the three may be true and empty at the real protocol, and counts as closing nothing.
Limits. Calls alone: no new law. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Rows2Public
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.Top.Fire.Code.KeyBasesAtSix
import Johnson.Top.Fire.Code.PieceSame
import Johnson.RunOne.KeyRowsAtSeat
import Johnson.RunOne.KeyFillSmOnly

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

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **The21's FIELD r2_3 AT The21Off's TERMS, IN SCOPE.** -/
theorem r2_3_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 3 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.1
  refine KeepsAt.reached _ _ (rowBlocksF₂ q₂ 3) ?_
  show KeepsAt (On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 3
  refine keepsAt_of_law₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () _ _ 3 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).shared.blocksInOrder[3]? = some b := by
    rw [show (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂ from q₂]
    exact hb
  refine ⟨capRest 3 ds, ?_, Err.le_refl _⟩
  exact Johnson.RunOne.KeyRows23.r2_3_seat (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack) atSix (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc rad (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N rdE X N P b1 b2 b3 b4 b5 b6 b7 b8 h8
    (pieceOf (held b) base ds back (capRest 3 ds)) b hb' rfl (hB 3 _ hrow) cellOnly_collN rfl
    (Johnson.RunOne.KeyRows23.smGroups_of_only _ (Johnson.RunOne.KeyRows23.smOnlyK Johnson.Top.H.csKey six numSix atSix decN recBack (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).orc))

/-- **The21's FIELD r2_6 AT The21Off's TERMS, IN SCOPE.** -/
theorem r2_6_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 6 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.1
  refine KeepsAt.reached _ _ (rowBlocksF₂ q₂ 6) ?_
  show KeepsAt (On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 6
  refine keepsAt_of_law₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () _ _ 6 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).shared.blocksInOrder[6]? = some b := by
    rw [show (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂ from q₂]
    exact hb
  refine ⟨capRest 6 ds, ?_, Err.le_refl _⟩
  exact Johnson.RunOne.KeyRows23.r2_6_seat (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack) atSix (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc rad (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 (split_in_scope hZ hP hm hX hp)
    (pieceOf (held b) base ds back (capRest 6 ds)) b hb' rfl (hB 6 _ hrow) cellOnly_collN
    (Johnson.RunOne.KeyRows23.smGroups_of_only _ (Johnson.RunOne.KeyRows23.smOnlyK Johnson.Top.H.csKey six numSix atSix decN recBack (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).orc))

/-- **The21's FIELD r2_8 AT The21Off's TERMS, IN SCOPE.** -/
theorem r2_8_at_name (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 8 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, h8⟩ := eight_said X N P hp
  have hB := (bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () atSix (basesAll_at_six hZ hP hm hX hp hwant hDK) q₁ q₂ q₃).2.1
  refine KeepsAt.reached _ _ (rowBlocksF₂ q₂ 8) ?_
  show KeepsAt (On₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 8
  refine keepsAt_of_law₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () _ _ 8 ?_
  intro b base ds back hb hrow
  have hb' : (descriptionFromSource X N P).shared.blocksInOrder[8]? = some b := by
    rw [show (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂ from q₂]
    exact hb
  refine ⟨capRest 8 ds, ?_, Err.le_refl _⟩
  exact Johnson.RunOne.KeyRows23.r2_8_seat (Fk X N P) (fr₂ (DK.at frS.P.T.a)) (baseAt X decN recBack) atSix (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (readAt tabN) enc rad (oneAt X).given.plan.samples collN (Johnson.RunOne.KeyRows23.last₁At (oneAt X)) off₂N rdE X N P b1 b2 b3 b4 b5 b6 b7 b8 h8 (split_in_scope hZ hP hm hX hp)
    (pieceOf (held b) base ds back (capRest 8 ds)) b hb' rfl (hB 8 _ hrow) cellOnly_collN rfl
    (Johnson.RunOne.KeyRows23.smReads_of_only _ (Johnson.RunOne.KeyRows23.smOnlyK Johnson.Top.H.csKey six numSix atSix decN recBack (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).orc))

/-- **THE FIT**: the theorem's conclusion IS The21's field r2_3 at The21Off's terms: by Lean's own check of types. -/
def fit_23 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N :=
  { H with r2_3 := r2_3_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hDK }

/-- **THE FIT**: the theorem's conclusion IS The21's field r2_6 at The21Off's terms: by Lean's own check of types. -/
def fit_26 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N :=
  { H with r2_6 := r2_6_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hDK }

/-- **THE FIT**: the theorem's conclusion IS The21's field r2_8 at The21Off's terms: by Lean's own check of types. -/
def fit_28 (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hwant : (Fk X N P).wantedOk = true) (hDK : DK.at frS.P.T.a = Johnson.G.writtenKFull)
    (H : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () (baseAt X decN recBack) atSix (readAt tabN) enc rad collN off₂N off₃N :=
  { H with r2_8 := r2_8_at_name X N P DK c₁ k₁ c₂ k₂ c₃ k₃ enc rad q₁ q₂ q₃ hZ hP hm hX hp hwant hDK }

end

end LPFD

#print axioms LPFD.r2_3_at_name
#print axioms LPFD.r2_6_at_name
#print axioms LPFD.r2_8_at_name
#print axioms LPFD.fit_23
#print axioms LPFD.fit_26
#print axioms LPFD.fit_28
