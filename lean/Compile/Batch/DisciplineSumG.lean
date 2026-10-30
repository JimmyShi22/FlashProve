-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineSumG.lean: the counts for the lemma on deferred programming with the ghost
names `fbw`: outside the ten oracles that can have marked queries and the ghost names `fbw t k`, k <
maxMoreB W (the later attempts of the rounds with proof-of-work bits), the count of marked queries
is 0. This file does not prove a bound for the sum over these oracles and ghost names.

Proved: `zeroBG : Spec.zeroBG` (the statement: Compile/Batch/SpecDiscipline.lean; the numbers:
Compile/Batch/Counts.lean; words of this library: lean/GLOSSARY.md). Arithmetic only.
 * The Fiat-Shamir family: `fb t` and `fbw t k`, for the three tags. No ordinary query. Their marked
   queries are together at most `xFbG`, which counts all attempts of every search. `Sum.fb_try_le`:
   (Ns + 1) · rounds + ∑ k < m, cTry k ≤ cFb, for every m (with `more` attempts after the first,
   attempt k + 1 is counted for k < `more`).
 * `Sum.cTry_zero`: from `maxMore` on no attempt is counted. `Sum.cTry_le`, `Sum.fb_le_xFb`,
   `Sum.fbw_le_xFb`: a single oracle of the family has at most `xFb` marked queries (attempts of one
   number).

Limits: it does not say that the programs keep these counts (`Spec.safeCB`, `Spec.safePB`).
-/
import Compile.Batch.DisciplineSum

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open scoped ENNReal

namespace Sum

section Shape
variable {lam K : ℕ}

theorem triesOf_eq {C P : Type} (g : Option (GrW C P)) : triesOf g = moreOf g + 1 := by
  cases g <;> rfl

/-- among the numbers below m, at most c are below c -/
theorem sum_lt_le (m c : ℕ) : ∑ k ∈ Finset.range m, (if k < c then 1 else 0) ≤ c := by
  rw [← Finset.card_filter]
  calc
    ((Finset.range m).filter fun k => k < c).card ≤ (Finset.range c).card :=
      Finset.card_le_card fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2
    _ = c := Finset.card_range c

/-- All attempts of all searches of one execution. -/
theorem fb_try_le (Ns m : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      (Ns + 1) * s.length + ∑ k ∈ Finset.range m, cTry k Ns s A W ≤ cFb Ns s A W
  | [], _, _ => by simp [cTry, cFb]
  | _ :: s, (_, A), (w, W) => by
      have ih := fb_try_le Ns m s A W
      have e : ∑ k ∈ Finset.range m, cTry k Ns (_ :: s) (_, A) (w, W) =
          Ns * ∑ k ∈ Finset.range m, (if k < moreOf w.grJ then 1 else 0) +
            ∑ k ∈ Finset.range m, (if k < moreOf w.gr0 then 1 else 0) +
            ∑ k ∈ Finset.range m, cTry k Ns s A W := by
        show ∑ k ∈ Finset.range m, (Ns * (if k < moreOf w.grJ then 1 else 0) +
            (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W) = _
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      rw [e]
      show (Ns + 1) * (s.length + 1) + _ ≤ Ns * triesOf w.grJ + triesOf w.gr0 + cFb Ns s A W
      rw [triesOf_eq, triesOf_eq]
      have h1 := Nat.mul_le_mul_left Ns (sum_lt_le m (moreOf w.grJ))
      have h2 := sum_lt_le m (moreOf w.gr0)
      have h3 : (Ns + 1) * (s.length + 1) = (Ns + 1) * s.length + Ns + 1 := by ring
      have h4 : Ns * (moreOf w.grJ + 1) = Ns * moreOf w.grJ + Ns := by ring
      omega

/-- an attempt of one number: at most one for each slot and one shared, in each round -/
theorem cTry_le (k Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), cTry k Ns s A W ≤ (Ns + 1) * s.length
  | [], _, _ => Nat.zero_le _
  | _ :: s, (_, A), (w, W) => by
      have ih := cTry_le k Ns s A W
      show Ns * (if k < moreOf w.grJ then 1 else 0) +
          (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W ≤
        (Ns + 1) * (s.length + 1)
      have h1 : Ns * (if k < moreOf w.grJ then 1 else 0) ≤ Ns := by split <;> simp
      have h2 : (if k < moreOf w.gr0 then 1 else 0) ≤ 1 := by split <;> simp
      have h3 : (Ns + 1) * (s.length + 1) = (Ns + 1) * s.length + Ns + 1 := by ring
      omega

/-- under `RoundsQueryLayout.OK` (no proof-of-work bits): one query for each slot and one shared, in each round
-/
theorem cFb_plain (Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      RoundsQueryLayout.OK s A W → cFb Ns s A W = (Ns + 1) * s.length
  | [], _, _, _ => by simp [cFb]
  | _ :: s, (_, A), (w, W), h => by
      show Ns * triesOf w.grJ + triesOf w.gr0 + cFb Ns s A W = (Ns + 1) * (s.length + 1)
      rw [h.1.grJ_none, h.1.gr0_none, cFb_plain Ns s A W h.2]
      show Ns * 1 + 1 + (Ns + 1) * s.length = _
      ring

/-- From maxMore on no attempt is counted. -/
theorem cTry_zero (Ns k : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), maxMore s A W ≤ k → cTry k Ns s A W = 0
  | [], _, _, _ => rfl
  | _ :: s, (_, A), (w, W), h => by
      have h' : max (max (moreOf w.grJ) (moreOf w.gr0)) (maxMore s A W) ≤ k := h
      have h1 : ¬ k < moreOf w.grJ := by
        have := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h'; omega
      have h2 : ¬ k < moreOf w.gr0 := by
        have := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h'; omega
      show Ns * (if k < moreOf w.grJ then 1 else 0) +
          (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W = 0
      rw [if_neg h1, if_neg h2, cTry_zero Ns k s A W (le_trans (le_max_right _ _) h')]
      simp

end Shape

section Counts
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (n : ℕ)

theorem fbw_e (tg : Tag) (k : ℕ) : eAllB W p n (OracleName.fbw tg k) = 0 := by
  show 0 + (p.M + 1) * 0 + n * 0 = 0
  simp

theorem fbw_test (k : ℕ) : mAllB W p n (OracleName.fbw Tag.test k) = cTry k 1 L.offline.shape _ W.T.sh := by
  show 0 + cTry k 1 L.offline.shape _ W.T.sh + (p.M + 1) * (0 + 0) + n * 0 = _
  simp

theorem fbw_link (k : ℕ) :
    mAllB W p n (OracleName.fbw Tag.link k) = (p.M + 1) * cTry k 1 L.link.shape _ W.Lk.sh := by
  show 0 + 0 + (p.M + 1) * (0 + cTry k 1 L.link.shape _ W.Lk.sh) + n * 0 = _
  simp

theorem fbw_onl (k : ℕ) :
    mAllB W p n (OracleName.fbw Tag.onl k) = n * cTry k L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh := by
  show 0 + 0 + (p.M + 1) * (0 + 0) + n * cTry k L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh = _
  simp

/-- each single oracle of the Fiat-Shamir family has at most xFb marked queries: attempts of one
number -/
theorem fb_le_xFb (tg : Tag) : mAllB W p n (OracleName.fb tg) ≤ xFb (L := L) p n := by
  have := fb_sum W p n
  cases tg <;> omega

theorem fbw_le_xFb (tg : Tag) (k : ℕ) : mAllB W p n (OracleName.fbw tg k) ≤ xFb (L := L) p n := by
  have h1 : cTry k 1 L.offline.shape _ W.T.sh ≤ 2 * L.offline.shape.length :=
    cTry_le k 1 L.offline.shape _ W.T.sh
  have h2 : (p.M + 1) * cTry k 1 L.link.shape _ W.Lk.sh ≤ (p.M + 1) * (2 * L.link.shape.length) :=
    Nat.mul_le_mul_left _ (cTry_le k 1 L.link.shape _ W.Lk.sh)
  have h3 : n * cTry k L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh ≤
      n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length) :=
    Nat.mul_le_mul_left _ (cTry_le k L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh)
  have e : xFb (L := L) p n =
      2 * L.offline.shape.length + (p.M + 1) * (2 * L.link.shape.length) +
        n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length) := rfl
  cases tg with
  | test => rw [fbw_test]; omega
  | link => rw [fbw_link]; omega
  | onl => rw [fbw_onl]; omega

/-- Under `W.OK` (no proof-of-work bits) xFbG is xFb. -/
theorem xFbG_plain (hW : W.OK) : xFbG W p n = xFb (L := L) p n := by
  unfold xFbG xFb
  rw [cFb_plain 1 _ _ _ hW.T.sh, cFb_plain 1 _ _ _ hW.Lk.sh, cFb_plain L.maxBatchSize _ _ _ hW.B.sh]

/-- The Fiat-Shamir family together: the three oracles `fb` and their ghost names `fbw` below m. -/
theorem fam_le (m : ℕ) :
    mAllB W p n (OracleName.fb Tag.test) + mAllB W p n (OracleName.fb Tag.link) + mAllB W p n (OracleName.fb Tag.onl) +
        (∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.test k) +
          ∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.link k) +
          ∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.onl k)) ≤ xFbG W p n := by
  rw [fb_sum W p n]
  simp only [fbw_test, fbw_link, fbw_onl]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : 2 * L.offline.shape.length + ∑ k ∈ Finset.range m, cTry k 1 L.offline.shape _ W.T.sh ≤
      cFb 1 L.offline.shape _ W.T.sh :=
    fb_try_le 1 m L.offline.shape _ W.T.sh
  have h2 : (p.M + 1) * (2 * L.link.shape.length) +
        (p.M + 1) * ∑ k ∈ Finset.range m, cTry k 1 L.link.shape _ W.Lk.sh ≤
      (p.M + 1) * cFb 1 L.link.shape _ W.Lk.sh := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left (p.M + 1) (fb_try_le 1 m L.link.shape _ W.Lk.sh)
  have h3 : n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length) +
        n * ∑ k ∈ Finset.range m, cTry k L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh ≤
      n * cFb L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left n (fb_try_le L.maxBatchSize m L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh)
  show 2 * L.offline.shape.length + (p.M + 1) * (2 * L.link.shape.length) +
      n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length) +
      (∑ k ∈ Finset.range m, cTry k 1 L.offline.shape _ W.T.sh +
        (p.M + 1) * ∑ k ∈ Finset.range m, cTry k 1 L.link.shape _ W.Lk.sh +
        n * ∑ k ∈ Finset.range m, cTry k L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh) ≤
    cFb 1 L.offline.shape _ W.T.sh + (p.M + 1) * cFb 1 L.link.shape _ W.Lk.sh +
      n * cFb L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh
  omega

end Counts

private theorem term_le' {M a B b : ℕ} (k : ℕ) (hM : M ≤ B) (ha : a ≤ b) :
    (M : ℝ≥0∞) * (a : ℕ) / 2 ^ k ≤ (B : ℝ≥0∞) * (b : ℕ) / 2 ^ k := by
  have h1 : (M : ℝ≥0∞) ≤ B := by exact_mod_cast hM
  have h2 : (a : ℝ≥0∞) ≤ b := by exact_mod_cast ha
  gcongr

private theorem term_zero' {M a : ℕ} (k : ℕ) (hM : M = 0) : (M : ℝ≥0∞) * (a : ℕ) / 2 ^ k = 0 := by
  rw [hM, Nat.cast_zero, zero_mul, ENNReal.zero_div]

/-- terms with one factor and one divisor in common -/
private theorem sum_terms (m : ℕ) (a : ℕ → ℕ) (c : ℕ) (d : ℕ) :
    ∑ k ∈ Finset.range m, (a k : ℝ≥0∞) * (c : ℕ) / 2 ^ d =
      ((∑ k ∈ Finset.range m, a k : ℕ) : ℝ≥0∞) * (c : ℕ) / 2 ^ d := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.sum_mul, Nat.cast_sum]

end Sum

open Sum in
/-- Outside the ten oracles and the ghost names `fbw` below maxMoreB W the count of marked queries
is 0. -/
theorem zeroBG : Spec.zeroBG := by
  intro I X lam L W p n o ho
  have hin : ∀ o' : OracleName, o' ∈ osB → o' ∈ osBG (maxMoreB W) := fun o' h => Finset.mem_union_left _ h
  cases o with
  | leaf => exact absurd (hin _ (by decide)) ho
  | node => exact absurd (hin _ (by decide)) ho
  | rleaf => exact absurd (hin _ (by decide)) ho
  | rnode => exact absurd (hin _ (by decide)) ho
  | fb tg => cases tg <;> exact absurd (hin _ (by decide)) ho
  | g tg => cases tg <;> exact absurd (hin _ (by decide)) ho
  | ann =>
    show 0 + 0 + (p.M + 1) * (0 + 0) + n * 0 = 0
    simp
  | other =>
    show 0 + 0 + (p.M + 1) * (0 + 0) + n * 0 = 0
    simp
  | fbw tg k =>
    have hk : maxMoreB W ≤ k := by
      by_contra hlt
      have hr : k ∈ Finset.range (maxMoreB W) := Finset.mem_range.2 (by omega)
      refine ho (Finset.mem_union_right _ ?_)
      cases tg with
      | test =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr))
      | link =>
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr))
      | onl => exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)
    cases tg with
    | test => rw [fbw_test, cTry_zero 1 k _ _ _ (le_trans (le_max_left _ _) hk)]
    | link =>
      rw [fbw_link,
        cTry_zero 1 k _ _ _ (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk),
        Nat.mul_zero]
    | onl =>
      rw [fbw_onl,
        cTry_zero L.maxBatchSize k _ _ _ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk),
        Nat.mul_zero]

end Compile.Batch.Disc
