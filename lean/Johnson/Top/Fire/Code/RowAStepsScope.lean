-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowAStepsScope.lean: RowASteps.lean's TWO STEPS AT THE KEY FILE's OWN BLOCKS 16 AND 17, AT THE SIX WRITTEN SEATS, IN THE GOALS' SCOPE: FROM q₁ AND THE FIVE (hZ · hP · hm · hX · hp) ALONE: EVERY PUBLIC PREMISE OF astep16 | astep17 IS PAID HERE BY A CALL: so that «each has a payer» is Lean's word, not a page's. THE FORM IS WHAT aSide_of_hist's premise Gaps (KeyASideAtFk.lean) asks at 16 | 17: ∀ b, blocksInOrder[k]? = some b → StepInv b (ASide (oneAt X) atSix k) (ASide (oneAt X) atSix (k + 1)), written out.
  astep16_scope   by block16 (the chain's block 16 is the bare form of the batching's seat: it decides as the seat: rfl) · pub_of_full at five_in_scope's two equations · hl_in_scope (KeyPublicAtSeat.lean)
  astep17_scope   by decide17 · rounds17 · public117_full (with samples_of_ranges · planOwn_w, Johnson/RunOne/KeySamples.lean) · stages_full of Johnson/RunOne/KeyScopeNums.lean (atSix 2 = (5, 0) = (stages + 1, 0)) · hl_in_scope | hw_in_scope (KeyPublicAtSeat.lean)
OBJECT: the first chain's state at borders 16 · 17 · 18 · USER: aSide_of_hist (KeyASideAtFk.lean) · LETTERS: X N P · c₁ k₁ · Zp X₀ cfg m. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowASteps
import Johnson.Top.Fire.Code.Row117Plan
import Johnson.Top.Fire.Code.Row116PubFull
import Johnson.Top.Fire.Code.KeyPublicAtSeat
import Johnson.RunOne.KeyScopeNums
import Johnson.RunOne.KeyFillBaseAt

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

open OnBytes.Params (OneTime Setting)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (CellOnly)

open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.KeyRows23 (atSix)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **StepInv b (ASide (oneAt X) atSix 16) (ASide (oneAt X) atSix 17), written out, at the chain's own block 16, in scope.** -/
theorem astep16_scope (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (b : Block FirstState Claim) (hb : (c₁ :: k₁)[16]? = some b) :
    ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))), roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 16 s = true ∧ Placed (plan₁ (oneAt X)).orc (fun o => s.d.book.place[o]?) id atSix (pinned (open₁ 2 16)) ∧ Means.InOrder s.d.st ∧ (2 ≤ 16 ∧ 16 ≤ 15 → MaskWith (fun o => s.d.book.place[o]?) 1 2)) →
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) (16 + 1) s' = true ∧ Placed (plan₁ (oneAt X)).orc (fun o => s'.d.book.place[o]?) id atSix (pinned (open₁ 2 (16 + 1))) ∧ Means.InOrder s'.d.st ∧ (2 ≤ (16 + 1) ∧ (16 + 1) ≤ 15 → MaskWith (fun o => s'.d.book.place[o]?) 1 2)) := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  have h5s := five_in_scope hZ hP hm hX hp
  have hpub := pub_of_full (oneAt X) h5s.2.1 h5s.2.2.1
  have eb := block16 (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b (by rw [← q₁] at hb; exact hb)
  exact astep16 (oneAt X) atSix pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) hpub.1 hpub.2 b (by rw [eb]; rfl)

/-- **StepInv b (ASide (oneAt X) atSix 17) (ASide (oneAt X) atSix 18), written out, at the chain's own block 17, in scope.** -/
theorem astep17_scope (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (b : Block FirstState Claim) (hb : (c₁ :: k₁)[17]? = some b) :
    ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))), roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 17 s = true ∧ Placed (plan₁ (oneAt X)).orc (fun o => s.d.book.place[o]?) id atSix (pinned (open₁ 2 17)) ∧ Means.InOrder s.d.st ∧ (2 ≤ 17 ∧ 17 ≤ 15 → MaskWith (fun o => s.d.book.place[o]?) 1 2)) →
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) (17 + 1) s' = true ∧ Placed (plan₁ (oneAt X)).orc (fun o => s'.d.book.place[o]?) id atSix (pinned (open₁ 2 (17 + 1))) ∧ Means.InOrder s'.d.st ∧ (2 ≤ (17 + 1) ∧ (17 + 1) ≤ 15 → MaskWith (fun o => s'.d.book.place[o]?) 1 2)) := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces (sent17 X) (g17 X)
  have h5s := five_in_scope hZ hP hm hX hp
  obtain ⟨⟨Pb⟩, hsm⟩ := public117_full (oneAt X) pieces (g17 X) h5s.2.1 h5s.2.2.1 h5s.2.2.2.2
    (Johnson.RunOne.KeySendGood.samples_of_ranges hp h5s.2.1) (fun _ hm' => Johnson.RunOne.KeySendGood.planOwn_w hp hm')
  have hat : atSix 2 = ((oneAt X).ranges.stages.length + 1, 0) := by
    rw [h5s.2.1, Johnson.RunOne.KeyLetters.stages_full]
    rfl
  exact astep17 (oneAt X) atSix pieces (sent17 X) (g17 X) Pb hsm hat bw hw b (decide17 X N P c₁ k₁ bw b x₀ x₁ hl hw q₁ hb)
    (rounds17 X N P c₁ k₁ bw b x₀ x₁ hl hw q₁ hb Pb.n₁ Pb.n₂ Pb.two)

end

end LPFD

#print axioms LPFD.astep16_scope
#print axioms LPFD.astep17_scope
