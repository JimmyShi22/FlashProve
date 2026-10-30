-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASideAtFk.lean: THE STATE's SIDE OF THE TABLES' PROMISE FROM THE HISTORY, AT THE KEY FILE's OWN DESCRIPTION Fk X N P AND Hist₁: ASide (Johnson/RunOne/KeyASide.lean) is the «and» of four terms, here T1 · T2 · T3 · T5. Gaps takes two letters H₀ H₁: the layer's step at 5 | 11 wants of the state in front what ASide lacks, «what was heard is in order at the lookup's place»: K3's block's step at 4 | 10 earns it, the layer's spends it.
OBJECT: ASide (oneAt X) at_ k a.2 at Hist₁ (Fk X N P) D k a · USER: aSide_at_all (KeyASideAll.lean); row 3.2's guard (through shape₁ … 19's book) · LETTERS: X N P D · at_.
  aSide0_fk      PROVED: at the chain's start
  stepFk0 | stepFk1   PROVED; aStep2 | 3 | 6 … 9 | 12 … 14 | 18 (KeyASideHist.lean), called: the twelve steps at (Fk X N P).first.blocksInOrder[k]
  aSide_four   PROVED: k ≤ 4: NO GAP: from the history and public premises alone
  aSide_of_hist  PROVED: k ≤ 19, UNDER Gaps: the seven steps that are not proved here
  t1_of_aSide    the book-keeping at n₁ (oneAt X) in the place of 2
Gaps X N P at_ H₀ H₁: A NAMED PREMISE: SEVEN STEPS: g4 | g10 (K3's blocks: ASide k ⟹ ASide (k + 1) ∧ H) · g5 | g11 (the layers: ASide k ∧ H ⟹ ASide (k + 1)) · g15 (the ranges' test): TAKEN ON REPORT, NOT AT LEAN, NOT CHECKED HERE (Where
this and lean/THEOREM.md differ, the page holds.) · g16 | g17: astep16_scope | astep17_scope (Top/Fire/Code/RowAStepsScope.lean: in scope, at atSix).
THE FOLD's INVARIANT: I k s := ASide … k s ∧ (k = 5 → H₀ s) ∧ (k = 11 → H₁ s).
AN IMPLICATION: EMPTY WHERE NOTHING IS REACHED. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyASideHist
import Johnson.Top.Fire.Code.Row10Paid
import Johnson.Top.Fire.Code.Row11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup Xi)
open Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (at_ : Where)

theorem aSide0_fk (h2 : (lookupsOf (oneAt X)).length = 2) (hm : (oneAt X).ranges.messageId = 1) (x : Xi) : ASide (oneAt X) at_ 0 ((Fk X N P).start₁ x) := by
  refine ⟨start_shape (oneAt X) h2 hm, fun k hk => ?_, Means.InOrder.start _, fun h => absurd h.1 (by decide)⟩
  rw [show pinned (open₁ 2 0) = [] from by decide] at hk
  cases hk

theorem cons_of_zero {α : Type} {l : List α} {b : α} (h : l[0]? = some b) : ∃ t, l = b :: t := by
  cases l with
  | nil => cases h
  | cons c t => exact ⟨t, by rw [Option.some.inj h]⟩

theorem stepFk0 (Pb : Public10 (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0))) (hat : at_ 0 = (0, 0))
    (b : Block FirstState Claim) (h : (Fk X N P).first.blocksInOrder[0]? = some b) : StepInv b (ASide (oneAt X) at_ 0) (ASide (oneAt X) at_ 1) := by
  obtain ⟨t, q₁⟩ := cons_of_zero h
  exact aStep0 (oneAt X) at_ pieces _ Pb hat b (decide10 X N P b t q₁) (rounds10 X N P b t q₁)

theorem stepFk1 (Pb : Public11 (oneAt X) pieces (g11 X)) (hst : 1 ≤ (oneAt X).ranges.stages.length) (hat : at_ 1 = (1, 0))
    (b : Block FirstState Claim) (h : (Fk X N P).first.blocksInOrder[1]? = some b) : StepInv b (ASide (oneAt X) at_ 1) (ASide (oneAt X) at_ 2) := by
  cases hq : (Fk X N P).first.blocksInOrder with
  | nil => rw [hq] at h; cases h
  | cons c t =>
    rw [hq] at h
    exact aStep1 (oneAt X) at_ pieces _ Pb hst hat b (decide11 X N P c t b hq h) (rounds11 X N P c t b hq h)

/-- **The seven steps that are other files'.** H₀ | H₁: what the layer of lookup 0 | 1 wants of the state in front beside ASide: letters. -/
structure Gaps (H₀ H₁ : FirstState → Prop) : Prop where
  g4 : ∀ b, (Fk X N P).first.blocksInOrder[4]? = some b → StepInv b (ASide (oneAt X) at_ 4) (fun s => ASide (oneAt X) at_ 5 s ∧ H₀ s)
  g5 : ∀ b, (Fk X N P).first.blocksInOrder[5]? = some b → StepInv b (fun s => ASide (oneAt X) at_ 5 s ∧ H₀ s) (ASide (oneAt X) at_ 6)
  g10 : ∀ b, (Fk X N P).first.blocksInOrder[10]? = some b → StepInv b (ASide (oneAt X) at_ 10) (fun s => ASide (oneAt X) at_ 11 s ∧ H₁ s)
  g11 : ∀ b, (Fk X N P).first.blocksInOrder[11]? = some b → StepInv b (fun s => ASide (oneAt X) at_ 11 s ∧ H₁ s) (ASide (oneAt X) at_ 12)
  g15 : ∀ b, (Fk X N P).first.blocksInOrder[15]? = some b → StepInv b (ASide (oneAt X) at_ 15) (ASide (oneAt X) at_ 16)
  g16 : ∀ b, (Fk X N P).first.blocksInOrder[16]? = some b → StepInv b (ASide (oneAt X) at_ 16) (ASide (oneAt X) at_ 17)
  g17 : ∀ b, (Fk X N P).first.blocksInOrder[17]? = some b → StepInv b (ASide (oneAt X) at_ 17) (ASide (oneAt X) at_ 18)

variable (D : WholeD) (x₀ x₁ : Lookup)

/-- **Borders 0 … 4: no gap.** -/
theorem aSide_four (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hm : (oneAt X).ranges.messageId = 1)
    (P10 : Public10 (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0))) (P11 : Public11 (oneAt X) pieces (g11 X))
    (hst : 1 ≤ (oneAt X).ranges.stages.length) (hat0 : at_ 0 = (0, 0)) (hat1 : at_ 1 = (1, 0))
    (k : ℕ) (a : Xi × FirstState) (hk : k ≤ 4) (hist : Hist₁ (Fk X N P) D k a) : ASide (oneAt X) at_ k a.2 := by
  refine aSide_upto (oneAt X) at_ _ (Fk X N P).first.blocksInOrder (st₁ (Fk X N P)) 4 (fun a ha => ?_) (fun j hj b hb => ?_) k a hk hist
  · rw [show a.2 = (Fk X N P).start₁ a.1 from ha]
    exact aSide0_fk X N P at_ (by rw [hl]; rfl) hm a.1
  · match j, hj with
    | 0, _ => exact stepFk0 X N P at_ P10 hat0 b hb
    | 1, _ => exact stepFk1 X N P at_ P11 hst hat1 b hb
    | 2, _ => exact aStep2 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb
    | 3, _ => exact aStep3 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb

/-- The fold's invariant. -/
def ASideH (one : OneTime) (at_ : Where) (H₀ H₁ : FirstState → Prop) (k : ℕ) (s : FirstState) : Prop := ASide one at_ k s ∧ (k = 5 → H₀ s) ∧ (k = 11 → H₁ s)

/-- A step of ASide alone is a step of the invariant, where the border behind is neither 5 nor 11. -/
theorem plainStep (one : OneTime) (at_ : Where) (H₀ H₁ : FirstState → Prop) (k : ℕ) (h5 : k + 1 ≠ 5) (h11 : k + 1 ≠ 11) (b : Block FirstState Claim)
    (h : StepInv b (ASide one at_ k) (ASide one at_ (k + 1))) : StepInv b (ASideH one at_ H₀ H₁ k) (ASideH one at_ H₀ H₁ (k + 1)) :=
  fun s s' rs gs hf hy hA => ⟨h s s' rs gs hf hy hA.1, fun e => absurd e h5, fun e => absurd e h11⟩

/-- **All nineteen, under the seven.** -/
theorem aSide_of_hist (H₀ H₁ : FirstState → Prop) (hl : lookupsOf (oneAt X) = [x₀, x₁]) (hm : (oneAt X).ranges.messageId = 1)
    (P10 : Public10 (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0))) (P11 : Public11 (oneAt X) pieces (g11 X))
    (hst : 1 ≤ (oneAt X).ranges.stages.length) (hat0 : at_ 0 = (0, 0)) (hat1 : at_ 1 = (1, 0))
    (bw : Block FirstState Claim)
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (G : Gaps X N P at_ H₀ H₁)
    (k : ℕ) (a : Xi × FirstState) (hk : k ≤ 19) (hist : Hist₁ (Fk X N P) D k a) : ASide (oneAt X) at_ k a.2 := by
  refine (reached_held_inv _ (Fk X N P).first.blocksInOrder (st₁ (Fk X N P)) (ASideH (oneAt X) at_ H₀ H₁) 19 (fun a ha => ?_) (fun j hj b hb => ?_) k a hk hist).1
  · rw [show a.2 = (Fk X N P).start₁ a.1 from ha]
    exact ⟨aSide0_fk X N P at_ (by rw [hl]; rfl) hm a.1, fun e => absurd e (by decide), fun e => absurd e (by decide)⟩
  · match j, hj with
    | 0, _ => exact plainStep (oneAt X) at_ H₀ H₁ 0 (by decide) (by decide) b (stepFk0 X N P at_ P10 hat0 b hb)
    | 1, _ => exact plainStep (oneAt X) at_ H₀ H₁ 1 (by decide) (by decide) b (stepFk1 X N P at_ P11 hst hat1 b hb)
    | 2, _ => exact plainStep (oneAt X) at_ H₀ H₁ 2 (by decide) (by decide) b (aStep2 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 3, _ => exact plainStep (oneAt X) at_ H₀ H₁ 3 (by decide) (by decide) b (aStep3 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 4, _ => exact fun s s' rs gs hf hy hA => ⟨(G.g4 b hb s s' rs gs hf hy hA.1).1, fun _ => (G.g4 b hb s s' rs gs hf hy hA.1).2, fun e => absurd e (by decide)⟩
    | 5, _ => exact fun s s' rs gs hf hy hA => ⟨G.g5 b hb s s' rs gs hf hy ⟨hA.1, hA.2.1 rfl⟩, fun e => absurd e (by decide), fun e => absurd e (by decide)⟩
    | 6, _ => exact plainStep (oneAt X) at_ H₀ H₁ 6 (by decide) (by decide) b (aStep6 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 7, _ => exact plainStep (oneAt X) at_ H₀ H₁ 7 (by decide) (by decide) b (aStep7 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 8, _ => exact plainStep (oneAt X) at_ H₀ H₁ 8 (by decide) (by decide) b (aStep8 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 9, _ => exact plainStep (oneAt X) at_ H₀ H₁ 9 (by decide) (by decide) b (aStep9 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 10, _ => exact fun s s' rs gs hf hy hA => ⟨(G.g10 b hb s s' rs gs hf hy hA.1).1, fun e => absurd e (by decide), fun _ => (G.g10 b hb s s' rs gs hf hy hA.1).2⟩
    | 11, _ => exact fun s s' rs gs hf hy hA => ⟨G.g11 b hb s s' rs gs hf hy ⟨hA.1, hA.2.2 rfl⟩, fun e => absurd e (by decide), fun e => absurd e (by decide)⟩
    | 12, _ => exact plainStep (oneAt X) at_ H₀ H₁ 12 (by decide) (by decide) b (aStep12 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 13, _ => exact plainStep (oneAt X) at_ H₀ H₁ 13 (by decide) (by decide) b (aStep13 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 14, _ => exact plainStep (oneAt X) at_ H₀ H₁ 14 (by decide) (by decide) b (aStep14 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
    | 15, _ => exact plainStep (oneAt X) at_ H₀ H₁ 15 (by decide) (by decide) b (G.g15 b hb)
    | 16, _ => exact plainStep (oneAt X) at_ H₀ H₁ 16 (by decide) (by decide) b (G.g16 b hb)
    | 17, _ => exact plainStep (oneAt X) at_ H₀ H₁ 17 (by decide) (by decide) b (G.g17 b hb)
    | 18, _ => exact plainStep (oneAt X) at_ H₀ H₁ 18 (by decide) (by decide) b (aStep18 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw b hb)
    | n + 19, h19 => exact absurd h19 (by omega)

/-- The book-keeping at n₁ (oneAt X), as T1 of on₁_of_tests, Johnson/RunOne/KeyFillOn.lean. -/
theorem t1_of_aSide (hl : lookupsOf (oneAt X) = [x₀, x₁]) (k : ℕ) (s : FirstState) (h : ASide (oneAt X) at_ k s) :
    shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) k s = true := by
  rw [n₁_two (oneAt X) x₀ x₁ hl]
  exact h.1

end

end LPFD

#print axioms LPFD.aSide0_fk
#print axioms LPFD.stepFk0
#print axioms LPFD.stepFk1
#print axioms LPFD.aSide_four
#print axioms LPFD.plainStep
#print axioms LPFD.aSide_of_hist
#print axioms LPFD.t1_of_aSide
