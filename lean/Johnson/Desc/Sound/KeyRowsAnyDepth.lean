-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyRowsAnyDepth.lean: THE KEY FILE'S RULE AT ROWS OF SEATS, AT ANY NUMBER OF
LEAVES of the request tree.

The setting. `KeyCore` (Johnson/Desc/Sound/KeyCore.lean) has a letter N: the number of leaves of
the request tree: the shared chain's errors count N times. `keyCoreAtRows`
(Johnson/Desc/Sound/KeyRows.lean) ends at N = 1.

What is said. `below_times`: errors that are shares of at most c are, N times, shares of at most N ·
c. `KeyCoreAtRowsN`, `keyCoreAtRowsN`: as `KeyCoreAtRows`, with the shared chain's seats meeting
their laws at a share c₂ with N · c₂ ≤ εs: `KeyCore` AT THE DECISION `F.run`, AT N LEAVES.

Limits. Those of KeyRows.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyRowsPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- Errors that are shares of at most c are, N times, shares of at most N · c. -/
theorem below_times (N : ℕ) (c : ℝ≥0∞) : ∀ {s : Shape} (ε : Err s), Err.Below ε c →
    Err.Below (Err.times N ε) ((N : ℝ≥0∞) * c)
  | [], _, _ => trivial
  | r :: _, (e, ε), h => by
    refine ⟨?_, below_times N c ε h.2⟩
    show ((N * e : ℕ) : ℝ≥0∞) ≤ (N : ℝ≥0∞) * c * (Fintype.card r.Chal : ℝ≥0∞)
    rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul_left' h.1 _

/-- **`KeyCore` at a description's own decision, from three rows of seats, at N leaves.** -/
def KeyCoreAtRowsN : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK : WholeD) (TFk TJk T3k : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (all : List LeftT) (X₁ X₂ W : Type) (F : FileDescription Kc.conf.Rec)
    (g₁ : List (Block F.S₁ F.Cl)) (g₂ : List (Block F.S₂ F.Cl)) (g₃ : List (Block F.S₃ F.Cl))
    (T : ThreeAt (ckP .two) (DK.at a) all F X₁ X₂ W)
    (A₁ Z₁ : JointRow (F.XiPub × F.S₁) (frameAt (DK.at a) all (DK.at a).key₁ T.ft₁))
    (A₂ Z₂ : JointRow ((F.XiPub × F.S₁) × F.S₂) (frameAt (DK.at a) all (DK.at a).key₂ T.ft₂))
    (A₃ Z₃ : JointRow ((F.XiPub × F.S₁ × F.S₂) × F.S₃)
      (frameAt (DK.at a) all (DK.at a).key₃ T.ft₃))
    (L₁ : SeatRow F.Cl W A₁ Z₁) (L₂ : SeatRow F.Cl W A₂ Z₂) (L₃ : SeatRow F.Cl W A₃ Z₃)
    (N : ℕ) (c₂ εs : ℝ≥0∞),
    (N : ℝ≥0∞) * c₂ ≤ εs →
    Gathers F.first.blocksInOrder g₁ → Gathers F.shared.blocksInOrder g₂ → Gathers F.second.blocksInOrder g₃ →
    OfGathered F g₁ g₂ g₃ T →
    T.p₁ :: T.l₁ = L₁.pieces → T.p₂ :: T.l₂ = L₂.pieces → T.p₃ :: T.l₃ = L₃.pieces →
    (atDesc F T).Fits → L₁.Laws εs → L₂.Laws c₂ → L₃.Laws εs →
    (∀ rec y, ¬ Kc.conf.coll y rec.1 →
      A₁.on ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => []))) →
    (∀ rec y, A₁.rel ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => [])) →
      Kc.conf.D y rec ≠ none) →
    (∀ b, Z₁.on b → A₂.on ((b.1, F.start₂ b.1.1), b.2) ∧
      (A₂.rel ((b.1, F.start₂ b.1.1), b.2) → Z₁.rel b)) →
    (∀ b s, F.start₃ b.1.1.1 b.1.1.2 b.1.2 = .ok s → Z₂.on b →
      A₃.on (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) ∧
      (A₃.rel (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) → Z₂.rel b)) →
    (∀ b, Z₃.on b → Z₃.rel b) →
    RowFit (DK.at a) all all →
    KeyCore Kc DK tFk tJk t3k silK F.run N εs

theorem keyCoreAtRowsN : KeyCoreAtRowsN := by
  intro a Kc DK TFk TJk T3k tFk tJk t3k silK all X₁ X₂ W F g₁ g₂ g₃ T A₁ Z₁ A₂ Z₂ A₃ Z₃ L₁ L₂ L₃ N
    c₂ εs hN G₁ G₂ G₃ hO e₁ e₂ e₃ hf w₁ w₂ w₃ hon hrel hs₁ hs₂ hlast hfit
  refine keyCoreAnti a Kc DK TFk TJk T3k tFk tJk t3k silK silK
    (runRow (atDesc F T).run₁ (atDesc F T).run₂ (atDesc F T).run₃) F.run N εs
    (fun _ _ _ _ h => h) (runGivesRowGathered F g₁ g₂ g₃ T hO G₁ G₂ G₃) ?_
  exact keyCoreOfBlocks a Kc DK TFk TJk T3k tFk tJk t3k silK all _ _ _ _ _ F.Cl W (atDesc F T)
    (rowsPlaces L₁ L₂ L₃) yes₂ yes₂ yes₂ hf.shape₁ hf.shape₂ hf.shape₃ N εs hf
    (rowsGood₁ εs e₁ w₁) (rowsGood₂ c₂ e₂ w₂) (rowsGood₃ εs e₃ w₃)
    (rowsGlued e₁ e₂ e₃ hs₁ hs₂ hlast) hfit
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    (fun rec y h => by
      have h' : (rowsPlaces L₁ L₂ L₃).on₁ 0 ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => [])) →
          ∃ w, (rowsPlaces L₁ L₂ L₃).R₁ 0
            ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => [])) w := h
      by_cases hc : Kc.conf.coll y rec.1
      · exact Or.inl hc
      · obtain ⟨w, hw⟩ := h' ((rowsFirstOn _).2 (hon rec y hc))
        exact Or.inr (hrel rec y ((rowsFirstRel _ w).1 hw)))
    (belowOfPieces (ckP .two) (DK.at a) all Kc.conf.Rec _ _ _ _ _ F.Cl W TFk TJk T3k tFk tJk t3k
      (atDesc F T) (rowsPlaces L₁ L₂ L₃) yes₂ yes₂ yes₂ hf.shape₁ hf.shape₂ hf.shape₃ N εs
      (rowsBelow₁ εs e₁ w₁)
      (fun q hq => Err.Below.mono_bound hN (below_times N c₂ q.err (rowsBelow₂ c₂ e₂ w₂ q hq)))
      (rowsBelow₃ εs e₃ w₃))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.below_times
#print axioms VerifiableInference.Desc.Sound.keyCoreAtRowsN
