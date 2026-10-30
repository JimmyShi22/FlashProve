-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowAStepsE.lean: the key file's first chain: a second conclusion of the step at block 17, on the verifier's state alone: what the shared chain's start takes of the first chain's end and ASide lacks (by a paper of statements of this project, «aSide₂_of_hist», § 4, which is not in this library): free₁'s fourth, sixth and last conjuncts at 18 ≤ k, to the sign (RunOne/KeyRows1At.lean): the row (Eval) is laid and lies open on the own group · every open row of the last group lies on its members' tables · W's message and its mask share a tree.
**EvalIs is earned at 1.17, from ASide 17 and the block's yes alone**: all three follow from Laid17 (what the yes of W's sending lays), and laid17_at makes Laid17 from the book-keeping at 17, the order, and the yes: that the state in front holds a linear claim is told by the yes itself (w_yes). No new letter is wanted.
  e18_of_laid      Laid17 one s s' → the three at s'
  astep17E         astep17's premises ⊢ the step at 17 with both conclusions (ASide … 18 ∧ the three), in StepInv's form, written out
  astep17E_scope   the same at the chain's own block 17, at oneAt X and atSix, from q₁ and the five in scope alone
e18_of_laid's three proofs stand also inside free_send17's (RunOne/KeyWShape.lean): the text stands twice.
Object: the first chain's state at border 18 · user: aSide₂_of_hist's start · letters: one N sent groups · at_ · b. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowAStepsScope

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


theorem e18_of_laid (one : OneTime) (s s' : FirstState) (H : Laid17 one s s') :
    (Johnson.RunOne.KeyRows23.EvalIs one.lin s' ∧ Johnson.RunOne.KeyRows23.OpenIn s'.d.st (s'.d.st.groups.size - 1) ∧ ∀ o, (plan₁ one).orc 2 = some o → MaskWith (fun i => s'.d.book.place[i]?) o (o + 1)) := by
  obtain ⟨l, L, Gp, row, hl, hL, hcl, hw, hown, hmask, hGp, hGm, hGr, hGi, hk, hrow⟩ := H.lin
  refine ⟨⟨L, row, hL, ?_, ?_⟩, fun G' hG' r' hr' => H.order.rows _ G' hG' r' hr', fun o ho => ?_⟩
  · show linEvalRow one.lin L.claim L.w (linLayW s'.d.st.codes one.lin) = some row
    rw [hcl, hw, H.codes]
    exact hrow
  · show (s'.d.st.groups[L.own]?).bind (·.rows[0]?) = some row
    rw [hown, hGp]
    show Gp.rows[0]? = some row
    rw [hGr]
    rfl
  · obtain rfl : wAt one = o := Option.some.inj ho
    exact ⟨one.ranges.stages.length + 1, 0, H.placeW, H.placeM⟩

/-- **The step at 17 with both conclusions.** -/
theorem astep17E (one : OneTime) (at_ : Where) (N : Pieces) (sent : ℕ) (groups : List (List ℕ)) (Pb : Public117 one N groups) (hsm : wAt one + 1 < noId)
    (hat : at_ 2 = (one.ranges.stages.length + 1, 0)) (bw : Block FirstState Claim) (hb : sendW one N sent groups = some bw)
    (b : Block FirstState Claim) (hd : b.decide = bw.decide) (hr : b.rounds = K1.rounds (parW' one N groups #[Pb.n₁, Pb.n₂])) :
    ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))), roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 17 s = true ∧ Placed (plan₁ one).orc (fun o => s.d.book.place[o]?) id at_ (pinned (open₁ 2 17)) ∧ Means.InOrder s.d.st ∧ (2 ≤ 17 ∧ 17 ≤ 15 → MaskWith (fun o => s.d.book.place[o]?) 1 2)) →
      (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) (17 + 1) s' = true ∧ Placed (plan₁ one).orc (fun o => s'.d.book.place[o]?) id at_ (pinned (open₁ 2 (17 + 1))) ∧ Means.InOrder s'.d.st ∧ (2 ≤ (17 + 1) ∧ (17 + 1) ≤ 15 → MaskWith (fun o => s'.d.book.place[o]?) 1 2)) ∧
      (Johnson.RunOne.KeyRows23.EvalIs one.lin s' ∧ Johnson.RunOne.KeyRows23.OpenIn s'.d.st (s'.d.st.groups.size - 1) ∧ ∀ o, (plan₁ one).orc 2 = some o → MaskWith (fun i => s'.d.book.place[i]?) o (o + 1)) := by
  intro s s' rs gs hf hy hA
  exact ⟨astep17 one at_ N sent groups Pb hsm hat bw hb b hd hr s s' rs gs hf hy hA,
    e18_of_laid one s s' (laid17_at one N sent groups Pb bw hb b hd s s' rs gs (hr ▸ hf) hy hA.1 hA.2.2.1)⟩

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

/-- **The same at the chain's own block 17, in scope.** -/
theorem astep17E_scope (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (b : Block FirstState Claim) (hb : (c₁ :: k₁)[17]? = some b) :
    ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))), roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' →
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 17 s = true ∧ Placed (plan₁ (oneAt X)).orc (fun o => s.d.book.place[o]?) id atSix (pinned (open₁ 2 17)) ∧ Means.InOrder s.d.st ∧ (2 ≤ 17 ∧ 17 ≤ 15 → MaskWith (fun o => s.d.book.place[o]?) 1 2)) →
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) (17 + 1) s' = true ∧ Placed (plan₁ (oneAt X)).orc (fun o => s'.d.book.place[o]?) id atSix (pinned (open₁ 2 (17 + 1))) ∧ Means.InOrder s'.d.st ∧ (2 ≤ (17 + 1) ∧ (17 + 1) ≤ 15 → MaskWith (fun o => s'.d.book.place[o]?) 1 2)) ∧
      (Johnson.RunOne.KeyRows23.EvalIs (oneAt X).lin s' ∧ Johnson.RunOne.KeyRows23.OpenIn s'.d.st (s'.d.st.groups.size - 1) ∧ ∀ o, (plan₁ (oneAt X)).orc 2 = some o → MaskWith (fun i => s'.d.book.place[i]?) o (o + 1)) := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces (sent17 X) (g17 X)
  have h5s := five_in_scope hZ hP hm hX hp
  obtain ⟨⟨Pb⟩, hsm⟩ := public117_full (oneAt X) pieces (g17 X) h5s.2.1 h5s.2.2.1 h5s.2.2.2.2
    (Johnson.RunOne.KeySendGood.samples_of_ranges hp h5s.2.1) (fun _ hm' => Johnson.RunOne.KeySendGood.planOwn_w hp hm')
  have hat : atSix 2 = ((oneAt X).ranges.stages.length + 1, 0) := by
    rw [h5s.2.1, Johnson.RunOne.KeyLetters.stages_full]
    rfl
  exact astep17E (oneAt X) atSix pieces (sent17 X) (g17 X) Pb hsm hat bw hw b (decide17 X N P c₁ k₁ bw b x₀ x₁ hl hw q₁ hb)
    (rounds17 X N P c₁ k₁ bw b x₀ x₁ hl hw q₁ hb Pb.n₁ Pb.n₂ Pb.two)

end

end LPFD

#print axioms LPFD.e18_of_laid
#print axioms LPFD.astep17E
#print axioms LPFD.astep17E_scope
