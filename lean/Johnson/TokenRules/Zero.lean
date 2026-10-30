-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/Zero.lean: OUTSIDE THE ORACLES osAllT THE COUNTS OF THE TOKEN PROGRAMS ALLOW NO
MARKED EVALUATION: the proof of Spec.zeroOutside (Johnson/TokenRules/Spec.lean).

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

The names fbw t k are infinitely many. A search in round number i makes at most cap i + 1 tries, so
no try is written under fbw t k once k is at least every cap of the protocol's rounds (cTry_zero);
osAllT holds the names below the largest cap of the three protocols (capTop,
Johnson/TokenSide/Counts.lean).

-/
import Johnson.TokenRules.Spec

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks

variable {I X : Type} {lam K : ℕ}

/-- No round's search reaches try number k + 1, if k is at least the cap of each of the rounds. -/
theorem cTry_zero (k : ℕ) (cap : ℕ → ℕ) : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ),
    (∀ j, i ≤ j → j < i + s.length → cap j ≤ k) → cTry k cap s A W i = 0
  | [], _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), i, h => by
      have h0 : ¬ (TokenSide.hasTest w = true ∧ k < cap i) := fun hc =>
        absurd (h i le_rfl (by simp)) (Nat.not_le.mpr hc.2)
      have h1 := cTry_zero k cap s A W (i + 1) fun j hj hj' =>
        h j (Nat.le_of_succ_le hj) (by simp only [List.length_cons]; omega)
      rw [cTry, if_neg h0, h1]

theorem cTry_zero_of_sup (k : ℕ) (cap : ℕ → ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (h : capSup cap s.length ≤ k) : cTry k cap s A W 0 = 0 :=
  cTry_zero k cap s A W 0 fun j _ hj =>
    le_trans (Finset.le_sup (f := cap) (Finset.mem_range.mpr (by simpa using hj))) h

/-- **Outside osAllT the counts are 0.** -/
theorem zeroOutside : Spec.zeroOutside := by
  intro I X lam L Bd aT aL W h tl n o ho
  have hin : ∀ o', o' ∈ osT0 → o' ∈ osAllT h := fun o' h' => Finset.mem_union_left _ h'
  cases o with
  | leaf => exact absurd (hin _ (by decide)) ho
  | rleaf => exact absurd (hin _ (by decide)) ho
  | rnode => exact absurd (hin _ (by decide)) ho
  | fb t => exact absurd (hin _ (by cases t <;> decide)) ho
  | g t => exact absurd (hin _ (by cases t <;> decide)) ho
  | node =>
      show (h.M + 2) * 0 + 0 + (h.M + 1) * 0 + n * 0 = 0
      simp
  | ann =>
      show (h.M + 2) * 0 + 0 + (h.M + 1) * 0 + n * 0 = 0
      simp
  | other =>
      show (h.M + 2) * 0 + 0 + (h.M + 1) * 0 + n * 0 = 0
      simp
  | fbw t k =>
      have hk : capTop h ≤ k := by
        by_contra hlt
        have hr : k ∈ Finset.range (capTop h) := Finset.mem_range.mpr (Nat.lt_of_not_le hlt)
        refine ho (Finset.mem_union_right _ ?_)
        cases t with
        | test =>
            exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨k, hr, rfl⟩))
        | link =>
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨k, hr, rfl⟩))
        | onl => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hr, rfl⟩)
      have e1 : cTry k h.capT L.offline.shape aT (wTC W).sh 0 = 0 :=
        cTry_zero_of_sup k _ _ _ _ (le_trans (le_max_left _ _) hk)
      have e2 : cTry k h.capL L.link.shape aL (wLC W).sh 0 = 0 :=
        cTry_zero_of_sup k _ _ _ _
          (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk)
      have e3 : cTry k h.capB L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh 0 = 0 :=
        cTry_zero_of_sup k _ _ _ _
          (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk)
      show (h.M + 2) * 0 +
          (if t = Tag.test then cTry k h.capT L.offline.shape aT (wTC W).sh 0 else 0) +
          (h.M + 1) * (if t = Tag.link then cTry k h.capL L.link.shape aL (wLC W).sh 0 else 0) +
          n * (if t = Tag.onl then cTry k h.capB L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh 0 else 0) = 0
      rw [e1, e2, e3]
      simp

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.zeroOutside
