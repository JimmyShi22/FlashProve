-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/TotalG.lean: the hash term of the scheme with proof-of-work bits, for one query bound:
the proofs of `Spec.supBG`, `Spec.sumSqBG` (Compile/Batch/SpecTotalG.lean). (Words of this library:
lean/GLOSSARY.md.)

`deferTot_counts`: the bound of the lemma on deferred programming for a total query bound, at the
counts of that scheme, is at most t * muB + hashSqBG. The counts are `mAllB`, `eAllB`
(Compile/Batch/SpecDiscipline.lean); lemmas on them: Compile/Batch/DisciplineSum.lean and
DisciplineSumG.lean.

Notation: the hash term: `zetaHashBGTot W p t n` without its first summand: t * `muB W p n` +
`hashSqBG W p n` (Compile/Batch/SpecTotalG.lean); the lemma on deferred programming for a total
query bound: `Spec.deferTotal` (Rom/SpecDeferTotal.lean); `eAllB W p n o`, `mAllB W p n o`: the
counts of the setup and n batches (Compile/Batch/SpecDiscipline.lean); `osB`: the oracles with
marked queries; `osBG m`: `osB` with the ghost names fbw t k, k < m; `(rulesB …).bits o`: a natural
number, the field `bits` of the rules of the scheme (same file); `xTree`, `xFb`, `xReq`, `xFbG`,
`maxMoreB`: counts of Compile/Batch/Counts.lean; `xGr`, `hashSqBG`: Compile/Batch/SpecTotalG.lean;
`muB`, `hashSqB`: Compile/Batch/SpecTotal.lean.

Limits: what the head of Compile/Batch/SpecTotalG.lean lists as not said is not said here either.
This file does not say that the programs keep these counts (`Spec.safeCB`, `Spec.safePB`).
-/
import Compile.Batch.SpecTotalG
import Compile.Batch.DisciplineSumG

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Disc Disc.Sum
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## 1. Searches -/

/-- The attempt after k + 1 failures is reached by no more searches than the attempt after one
failure. -/
theorem cTry_le_zero {K : ℕ} (k Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), cTry k Ns s A W ≤ cTry 0 Ns s A W
  | [], _, _ => le_rfl
  | _ :: s, (_, A), (w, W) => by
      have i1 : ∀ m : ℕ, (if k < m then 1 else 0) ≤ (if 0 < m then 1 else 0) :=
        fun m => by split_ifs <;> omega
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (i1 _)) (i1 _))
        (cTry_le_zero k Ns s A W)

/-- Without proof-of-work records (`RoundsQueryLayout.OK`) there is no search. -/
theorem cTry_plain {K : ℕ} (k Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OK s A W → cTry k Ns s A W = 0
  | [], _, _, _ => rfl
  | _ :: s, (_, A), (w, W), h => by
      show Ns * (if k < moreOf w.grJ then 1 else 0) +
          (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W = 0
      rw [h.1.grJ_none, h.1.gr0_none, cTry_plain k Ns s A W h.2]
      simp [moreOf]

variable (W : QueryLayout lam L) (p : Params) (n : ℕ)

theorem xGr_eq :
    xGr W p n =
      cTry 0 1 L.offline.shape _ W.T.sh + (p.M + 1) * cTry 0 1 L.link.shape _ W.Lk.sh +
        n * cTry 0 L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh := rfl

/-- In the counts `mAllB`, every ghost name fbw t k has at most xGr marked queries. -/
theorem fbw_le_xGr (tg : Tag) (k : ℕ) : mAllB W p n (OracleName.fbw tg k) ≤ xGr W p n := by
  have h1 := cTry_le_zero k 1 L.offline.shape _ W.T.sh
  have h2 := Nat.mul_le_mul_left (p.M + 1) (cTry_le_zero k 1 L.link.shape _ W.Lk.sh)
  have h3 := Nat.mul_le_mul_left n (cTry_le_zero k L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh)
  have e := xGr_eq W p n
  cases tg with
  | test => rw [fbw_test]; omega
  | link => rw [fbw_link]; omega
  | onl => rw [fbw_onl]; omega

/-- the first attempts, and one second attempt for each search, are among all attempts -/
theorem xFb_add_xGr_le : xFb (L := L) p n + xGr W p n ≤ xFbG W p n := by
  have h1 : 2 * L.offline.shape.length + cTry 0 1 L.offline.shape _ W.T.sh ≤
      cFb 1 L.offline.shape _ W.T.sh := by
    have := fb_try_le 1 1 L.offline.shape _ W.T.sh
    rwa [Finset.sum_range_one] at this
  have h2 : (p.M + 1) * (2 * L.link.shape.length) + (p.M + 1) * cTry 0 1 L.link.shape _ W.Lk.sh ≤
      (p.M + 1) * cFb 1 L.link.shape _ W.Lk.sh := by
    have := fb_try_le 1 1 L.link.shape _ W.Lk.sh
    rw [Finset.sum_range_one] at this
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ this
  have h3 : n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length) +
        n * cTry 0 L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh ≤
      n * cFb L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh := by
    have := fb_try_le L.maxBatchSize 1 L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh
    rw [Finset.sum_range_one] at this
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ this
  show 2 * L.offline.shape.length + (p.M + 1) * (2 * L.link.shape.length) +
      n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length) +
      (cTry 0 1 L.offline.shape _ W.T.sh + (p.M + 1) * cTry 0 1 L.link.shape _ W.Lk.sh +
        n * cTry 0 L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh) ≤
    cFb 1 L.offline.shape _ W.T.sh + (p.M + 1) * cFb 1 L.link.shape _ W.Lk.sh +
      n * cFb L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh
  omega

variable {W p n}

/-! ## 2. The maximum -/

/-- a fraction grows with its numerator -/
theorem fracG_le {a b : ℕ} (k : ℕ) (h : a ≤ b) : (a : ℝ≥0∞) / 2 ^ k ≤ (b : ℝ≥0∞) / 2 ^ k :=
  ENNReal.div_le_div_right (Nat.cast_le.2 h) _

theorem supBG : Spec.supBG := by
  intro I X lam L W p n
  have l1 : ∀ x : ℝ≥0∞, x ≤ (xTree W p n : ℝ≥0∞) / 2 ^ p.sMT → x ≤ muB W p n := fun x h =>
    h.trans (le_max_left _ _)
  have l2 : ∀ x : ℝ≥0∞, x ≤ (xTree W p n : ℝ≥0∞) / 2 ^ lam → x ≤ muB W p n := fun x h =>
    h.trans ((le_max_left _ _).trans (le_max_right _ _))
  have l3 : ∀ x : ℝ≥0∞, x ≤ (xFb (L := L) p n : ℝ≥0∞) / 2 ^ (min p.sFS lam) → x ≤ muB W p n :=
    fun x h => h.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have l4 : ∀ x : ℝ≥0∞, x ≤ (xReq L n : ℝ≥0∞) / 2 ^ lam → x ≤ muB W p n := fun x h =>
    h.trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hw : ∀ tg k, (mAllB W p n (OracleName.fbw tg k) : ℝ≥0∞) /
        2 ^ (rulesB W.K L lam p).bits (OracleName.fbw tg k) ≤ muB W p n :=
    fun tg k => l3 _ (fracG_le (min p.sFS lam) (fbw_le_xFb W p n tg k))
  refine Finset.sup_le fun o ho => ?_
  rcases Finset.mem_union.1 ho with ho | ho
  · simp only [osB, Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l1 _ (fracG_le p.sMT (by have := leaf_eq W p n; omega))
    · exact l2 _ (fracG_le lam (by have := node_eq W p n; omega))
    · exact l4 _ (fracG_le lam (rleaf_le W p n).1)
    · exact l4 _ (fracG_le lam (rnode_le W p n).1)
    · exact l3 _ (fracG_le (min p.sFS lam) (fb_le_xFb W p n _))
    · exact l3 _ (fracG_le (min p.sFS lam) (fb_le_xFb W p n _))
    · exact l3 _ (fracG_le (min p.sFS lam) (fb_le_xFb W p n _))
    · exact l4 _ (fracG_le lam (by rw [g_test_eq W p n]; exact Nat.zero_le _))
    · exact l4 _ (fracG_le lam (by rw [g_link_eq W p n]; exact Nat.zero_le _))
    · exact l4 _ (fracG_le lam (g_onl_le W p n).1)
  · rcases Finset.mem_union.1 ho with ho | ho
    · rcases Finset.mem_union.1 ho with ho | ho
        <;> obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 ho <;> exact hw _ k
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 ho
      exact hw _ k

/-! ## 3. The sum -/

/-- a sum over a union is at most the sum of the two sums -/
theorem sum_union_le' {ι : Type} [DecidableEq ι] (s t : Finset ι) (f : ι → ℝ≥0∞) :
    ∑ o ∈ s ∪ t, f o ≤ ∑ o ∈ s, f o + ∑ o ∈ t, f o := by
  rw [← Finset.sum_union_inter]
  exact le_add_right le_rfl

/-- The sum of squares over the ghost names of one tag is at most xGr times their sum. -/
theorem ghost_le (W : QueryLayout lam L) (p : Params) (n m : ℕ) (tg : Tag) :
    ∑ o ∈ (Finset.range m).image (OracleName.fbw tg), (mAllB W p n o : ℝ≥0∞) *
        (eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ (rulesB W.K L lam p).bits o ≤
      (xGr W p n : ℝ≥0∞) * ((∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw tg k) : ℕ) : ℝ≥0∞) /
        2 ^ (min p.sFS lam) := by
  rw [Finset.sum_image fun a _ b _ h => (OracleName.fbw.inj h).2, Nat.cast_sum, Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  show (mAllB W p n (OracleName.fbw tg k) : ℝ≥0∞) *
      (eAllB W p n (OracleName.fbw tg k) + mAllB W p n (OracleName.fbw tg k) : ℕ) / 2 ^ (min p.sFS lam) ≤ _
  rw [fbw_e, Nat.zero_add, div_eq_mul_inv]
  have : (mAllB W p n (OracleName.fbw tg k) : ℝ≥0∞) ≤ (xGr W p n : ℝ≥0∞) :=
    Nat.cast_le.2 (fbw_le_xGr W p n tg k)
  gcongr

theorem sumSqBG : Spec.sumSqBG := by
  intro I X lam L W p n
  set m := maxMoreB W
  set f : OracleName → ℝ≥0∞ := fun o =>
    (mAllB W p n o : ℝ≥0∞) * (eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ (rulesB W.K L lam p).bits o
  have h0 : ∑ o ∈ osB, f o ≤ hashSqB W p n := by
    have h := Disc.sumB I X lam L W p n (fun _ => 0) 0 fun _ => le_rfl
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun o _ => ?_)) h
    show _ = (mAllB W p n o : ℝ≥0∞) * (0 + eAllB W p n o + mAllB W p n o : ℕ) / _
    rw [Nat.zero_add]
  have hf := fam_le W p n m
  have hg : ∑ o ∈ (Finset.range m).image (OracleName.fbw Tag.test) ∪ (Finset.range m).image
            (OracleName.fbw Tag.link) ∪ (Finset.range m).image (OracleName.fbw Tag.onl),
          f o ≤
      (xGr W p n : ℝ≥0∞) * (xFbG W p n : ℕ) / 2 ^ (min p.sFS lam) := by
    refine le_trans (le_trans (sum_union_le' _ _ f) (add_le_add (sum_union_le' _ _ f) le_rfl)) ?_
    refine le_trans
      (add_le_add (add_le_add (ghost_le W p n m Tag.test) (ghost_le W p n m Tag.link))
        (ghost_le W p n m Tag.onl)) ?_
    have hs : ((∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.test k) : ℕ) : ℝ≥0∞) +
          ((∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.link k) : ℕ) : ℝ≥0∞) +
          ((∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.onl k) : ℕ) : ℝ≥0∞) ≤
        (xFbG W p n : ℕ) := by
      exact_mod_cast (by
        omega : ∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.test k) +
            ∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.link k) +
            ∑ k ∈ Finset.range m, mAllB W p n (OracleName.fbw Tag.onl k) ≤ xFbG W p n)
    simp only [div_eq_mul_inv]
    rw [← add_mul, ← add_mul, ← mul_add, ← mul_add]
    gcongr
  refine le_trans (sum_union_le' _ _ f) (le_trans (add_le_add h0 hg) (le_of_eq ?_))
  unfold hashSqB hashSqBG
  ring

/-- Used by `hopB_total` (Compile/Batch/HopTot.lean): the bound of the lemma on deferred programming
for a total query bound, at the counts of the scheme with proof-of-work bits. -/
theorem deferTot_counts (W : QueryLayout lam L) (p : Params) (t n : ℕ) :
    (t : ℝ≥0∞) * (osBG (maxMoreB W)).sup
            (fun o => (mAllB W p n o : ℝ≥0∞) / 2 ^ (rulesB W.K L lam p).bits o) +
        ∑ o ∈ osBG (maxMoreB W), (mAllB W p n o : ℝ≥0∞) *
          (eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ (rulesB W.K L lam p).bits o ≤
      (t : ℝ≥0∞) * muB W p n + hashSqBG W p n := by
  refine add_le_add ?_ (sumSqBG I X lam L W p n)
  gcongr
  exact supBG I X lam L W p n

end Compile.Batch
