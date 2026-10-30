-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineSum.lean: the sum in the lemma on deferred programming, over the ten oracles
`osB`, is at most explicit hash terms, for an adversary with at most T queries to each oracle (words
of this library: lean/GLOSSARY.md).

It proves `Compile.Batch.Disc.sumB : Spec.sumB` (the statement is in
Compile/Batch/SpecDiscipline.lean; the numbers are those of Compile/Batch/Counts.lean). Arithmetic
on the counts `eAllB`, `mAllB` only:
 * leaf oracle and node oracle: ordinary and marked queries together are exactly `xTree`;
 * the leaf oracle and the node oracle of request trees, and g with the tag of Batch: at most one
   marked query for each slot of each batch, `xReq`; Test and Link have local rounds only, so their
   chains never join, and g with their tags has no marked query;
 * the three Fiat-Shamir oracles: their marked queries together are exactly `xFb`, and ∑ a (T + a) ≤
   (∑ a) (T + ∑ a).

Limits: the ghost names `fbw t k` (Compile/Batch/DisciplineSumG.lean) are not in this sum.
-/
import Compile.Batch.SpecDiscipline
import Compile.DisciplineCounts

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open scoped ENNReal

namespace Sum

/-- With local rounds only the chains of an execution never join. -/
theorem joins_allLocal : ∀ s : Shape, joins s (RoundSplits.allLocal s) = 0
  | [] => rfl
  | _ :: s => joins_allLocal s

theorem joins_le_one : ∀ (s : Shape) (A : RoundSplits s), joins s A ≤ 1
  | [], _ => Nat.zero_le _
  | _ :: _, (⟨.sh, _, _, _, _, _, _, _, _, _⟩, _) => le_refl 1
  | _ :: s, (⟨.lo, _, _, _, _, _, _, _, _, _⟩, A) => joins_le_one s A

private theorem term_le {M a B b : ℕ} (k : ℕ) (hM : M ≤ B) (ha : a ≤ b) :
    (M : ℝ≥0∞) * (a : ℕ) / 2 ^ k ≤ (B : ℝ≥0∞) * (b : ℕ) / 2 ^ k := by
  have h1 : (M : ℝ≥0∞) ≤ B := by exact_mod_cast hM
  have h2 : (a : ℝ≥0∞) ≤ b := by exact_mod_cast ha
  gcongr

private theorem term_zero {M a : ℕ} (k : ℕ) (hM : M = 0) : (M : ℝ≥0∞) * (a : ℕ) / 2 ^ k = 0 := by
  rw [hM, Nat.cast_zero, zero_mul, ENNReal.zero_div]

section Counts
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (n : ℕ)

/-- Leaf oracle: ordinary and marked queries together. -/
theorem leaf_eq : eAllB W p n OracleName.leaf + mAllB W p n OracleName.leaf = xTree W p n := by
  have hab := Compile.Disc.Counts.cntLeaves_add W.depth fun j => decide (j < L.wordLength)
  show (Compile.Disc.cntLeaves W.depth (fun j => !decide (j < L.wordLength)) +
        (p.M + 1) * Compile.Disc.cntLeaves W.depth (fun j => !decide (j < L.wordLength)) + n * 0) +
      (Compile.Disc.cntLeaves W.depth (fun j => decide (j < L.wordLength)) + cTrees L.offline.shape _ W.T.sh 1 +
        (p.M + 1) *
          (Compile.Disc.cntLeaves W.depth (fun j => decide (j < L.wordLength)) +
            cTrees L.link.shape _ W.Lk.sh 1) +
        n * cTrees L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh L.maxBatchSize) =
    (p.M + 1 + 1) * 2 ^ W.depth + cTrees L.offline.shape _ W.T.sh 1 +
      (p.M + 1) * cTrees L.link.shape _ W.Lk.sh 1 + n * cTrees L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh L.maxBatchSize
  rw [← hab]
  ring

/-- Node oracle: ordinary and marked queries together. -/
theorem node_eq : eAllB W p n OracleName.node + mAllB W p n OracleName.node = xTree W p n := by
  show (2 ^ W.depth + (p.M + 1) * 2 ^ W.depth + n * 0) +
      (0 + cTrees L.offline.shape _ W.T.sh 1 + (p.M + 1) * (0 + cTrees L.link.shape _ W.Lk.sh 1) +
        n * cTrees L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh L.maxBatchSize) =
    (p.M + 1 + 1) * 2 ^ W.depth + cTrees L.offline.shape _ W.T.sh 1 +
      (p.M + 1) * cTrees L.link.shape _ W.Lk.sh 1 + n * cTrees L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh L.maxBatchSize
  ring

theorem joinsN_le : n * (joins L.onlineBatch.loc.shape L.onlineBatch.ann * L.maxBatchSize) ≤ xReq L n :=
  Nat.mul_le_mul_left n
    (le_trans (Nat.mul_le_mul_right _ (joins_le_one _ _)) (le_of_eq (Nat.one_mul _)))

/-- The oracles of request trees. -/
theorem rleaf_le : mAllB W p n OracleName.rleaf ≤ xReq L n ∧ eAllB W p n OracleName.rleaf = 0 := by
  refine ⟨?_, ?_⟩
  · show 0 + joins L.offline.shape (RoundSplits.allLocal _) * 1 +
        (p.M + 1) * (0 + joins L.link.shape (RoundSplits.allLocal _) * 1) +
        n * (joins L.onlineBatch.loc.shape L.onlineBatch.ann * L.maxBatchSize) ≤ _
    rw [joins_allLocal, joins_allLocal]
    simpa using joinsN_le (L := L) n
  · show 0 + (p.M + 1) * 0 + n * 0 = 0
    simp

theorem rnode_le : mAllB W p n OracleName.rnode ≤ xReq L n ∧ eAllB W p n OracleName.rnode = 0 := by
  refine ⟨?_, ?_⟩
  · show 0 + joins L.offline.shape (RoundSplits.allLocal _) * 1 +
        (p.M + 1) * (0 + joins L.link.shape (RoundSplits.allLocal _) * 1) +
        n * (joins L.onlineBatch.loc.shape L.onlineBatch.ann * L.maxBatchSize) ≤ _
    rw [joins_allLocal, joins_allLocal]
    simpa using joinsN_le (L := L) n
  · show 0 + (p.M + 1) * 0 + n * 0 = 0
    simp

/-- g. -/
theorem g_onl_le : mAllB W p n (OracleName.g Tag.onl) ≤ xReq L n ∧ eAllB W p n (OracleName.g Tag.onl) = 0 := by
  refine ⟨?_, ?_⟩
  · show 0 + 0 + (p.M + 1) * (0 + 0) + n * (joins L.onlineBatch.loc.shape L.onlineBatch.ann * L.maxBatchSize) ≤ _
    simpa using joinsN_le (L := L) n
  · show 0 + (p.M + 1) * 0 + n * 0 = 0
    simp

theorem g_test_eq : mAllB W p n (OracleName.g Tag.test) = 0 := by
  show 0 + joins L.offline.shape (RoundSplits.allLocal _) * 1 + (p.M + 1) * (0 + 0) + n * 0 = 0
  rw [joins_allLocal]
  simp

theorem g_link_eq : mAllB W p n (OracleName.g Tag.link) = 0 := by
  show 0 + 0 + (p.M + 1) * (0 + joins L.link.shape (RoundSplits.allLocal _) * 1) + n * 0 = 0
  rw [joins_allLocal]
  simp

/-- The Fiat-Shamir oracles. -/
theorem fb_e (tg : Tag) : eAllB W p n (OracleName.fb tg) = 0 := by
  show 0 + (p.M + 1) * 0 + n * 0 = 0
  simp

theorem fb_sum :
    mAllB W p n (OracleName.fb Tag.test) + mAllB W p n (OracleName.fb Tag.link) + mAllB W p n (OracleName.fb Tag.onl) =
      xFb (L := L) p n := by
  show (0 + (1 + 1) * L.offline.shape.length + (p.M + 1) * (0 + 0) + n * 0) +
      (0 + 0 + (p.M + 1) * (0 + (1 + 1) * L.link.shape.length) + n * 0) +
      (0 + 0 + (p.M + 1) * (0 + 0) + n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length)) =
    2 * L.offline.shape.length + (p.M + 1) * (2 * L.link.shape.length) +
      n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length)
  ring

end Counts

end Sum

open Sum in
/-- For an adversary with at most T queries to each oracle: the sum in the lemma on deferred
programming over the ten oracles `osB` is at most the four terms of `Spec.sumB`: the hash terms of
zetaHashB, which is not in this library. The four terms (Compile/Batch/SpecDiscipline.lean):
X (T + X) / 2^b at (X, b) = (`xTree`, `p.sMT`), (`xTree`, `lam`), (`xFb`, `min p.sFS lam`), and
3 times it at (`xReq`, `lam`). -/
theorem sumB : Spec.sumB := by
  intro I X lam L W p n t T ht
  have hsum : ∑ o ∈ osB, (mAllB W p n o : ℝ≥0∞) *
        (t o + eAllB W p n o + mAllB W p n o : ℕ) / 2 ^ (rulesB W.K L lam p).bits o =
      (mAllB W p n OracleName.leaf : ℝ≥0∞) *
          (t OracleName.leaf + eAllB W p n OracleName.leaf + mAllB W p n OracleName.leaf : ℕ) / 2 ^ p.sMT +
        ((mAllB W p n OracleName.node : ℝ≥0∞) *
            (t OracleName.node + eAllB W p n OracleName.node + mAllB W p n OracleName.node : ℕ) / 2 ^ lam +
          ((mAllB W p n OracleName.rleaf : ℝ≥0∞) *
              (t OracleName.rleaf + eAllB W p n OracleName.rleaf + mAllB W p n OracleName.rleaf : ℕ) / 2 ^ lam +
            ((mAllB W p n OracleName.rnode : ℝ≥0∞) *
                (t OracleName.rnode + eAllB W p n OracleName.rnode + mAllB W p n OracleName.rnode : ℕ) / 2 ^ lam +
              ((mAllB W p n (OracleName.fb Tag.test) : ℝ≥0∞) *
                  (t (OracleName.fb Tag.test) + eAllB W p n (OracleName.fb Tag.test) +
                    mAllB W p n (OracleName.fb Tag.test) : ℕ) /
                  2 ^ (min p.sFS lam) +
                ((mAllB W p n (OracleName.fb Tag.link) : ℝ≥0∞) *
                    (t (OracleName.fb Tag.link) + eAllB W p n (OracleName.fb Tag.link) +
                      mAllB W p n (OracleName.fb Tag.link) : ℕ) /
                    2 ^ (min p.sFS lam) +
                  ((mAllB W p n (OracleName.fb Tag.onl) : ℝ≥0∞) *
                      (t (OracleName.fb Tag.onl) + eAllB W p n (OracleName.fb Tag.onl) +
                        mAllB W p n (OracleName.fb Tag.onl) : ℕ) /
                      2 ^ (min p.sFS lam) +
                    ((mAllB W p n (OracleName.g Tag.test) : ℝ≥0∞) *
                        (t (OracleName.g Tag.test) + eAllB W p n (OracleName.g Tag.test) +
                          mAllB W p n (OracleName.g Tag.test) : ℕ) / 2 ^ lam +
                      ((mAllB W p n (OracleName.g Tag.link) : ℝ≥0∞) *
                          (t (OracleName.g Tag.link) + eAllB W p n (OracleName.g Tag.link) +
                            mAllB W p n (OracleName.g Tag.link) : ℕ) / 2 ^ lam +
                        (mAllB W p n (OracleName.g Tag.onl) : ℝ≥0∞) *
                          (t (OracleName.g Tag.onl) + eAllB W p n (OracleName.g Tag.onl) +
                            mAllB W p n (OracleName.g Tag.onl) : ℕ) /
                          2 ^ lam)))))))) := by
    unfold osB
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    rfl
  rw [hsum, term_zero lam (g_test_eq W p n), term_zero lam (g_link_eq W p n)]
  have hleaf := term_le (M := mAllB W p n OracleName.leaf)
    (a := t OracleName.leaf + eAllB W p n OracleName.leaf + mAllB W p n OracleName.leaf) (B := xTree W p n)
    (b := T + xTree W p n) p.sMT (by have := leaf_eq W p n; omega)
    (by have := leaf_eq W p n; have := ht OracleName.leaf; omega)
  have hnode := term_le (M := mAllB W p n OracleName.node)
    (a := t OracleName.node + eAllB W p n OracleName.node + mAllB W p n OracleName.node) (B := xTree W p n)
    (b := T + xTree W p n) lam (by have := node_eq W p n; omega)
    (by have := node_eq W p n; have := ht OracleName.node; omega)
  have hrl := term_le (M := mAllB W p n OracleName.rleaf)
    (a := t OracleName.rleaf + eAllB W p n OracleName.rleaf + mAllB W p n OracleName.rleaf) (B := xReq L n)
    (b := T + xReq L n) lam (rleaf_le W p n).1
    (by have := rleaf_le W p n; have := ht OracleName.rleaf; omega)
  have hrn := term_le (M := mAllB W p n OracleName.rnode)
    (a := t OracleName.rnode + eAllB W p n OracleName.rnode + mAllB W p n OracleName.rnode) (B := xReq L n)
    (b := T + xReq L n) lam (rnode_le W p n).1
    (by have := rnode_le W p n; have := ht OracleName.rnode; omega)
  have hg := term_le (M := mAllB W p n (OracleName.g Tag.onl))
    (a := t (OracleName.g Tag.onl) + eAllB W p n (OracleName.g Tag.onl) + mAllB W p n (OracleName.g Tag.onl))
    (B := xReq L n) (b := T + xReq L n) lam (g_onl_le W p n).1
    (by have := g_onl_le W p n; have := ht (OracleName.g Tag.onl); omega)
  have hfs := fb_sum W p n
  have step : ∀ tg : Tag, (mAllB W p n (OracleName.fb tg) : ℝ≥0∞) *
        (t (OracleName.fb tg) + eAllB W p n (OracleName.fb tg) + mAllB W p n (OracleName.fb tg) : ℕ) / 2 ^ (min p.sFS lam) ≤
      (mAllB W p n (OracleName.fb tg) : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) /
        2 ^ (min p.sFS lam) := fun tg =>
    term_le _ le_rfl (by
      have h1 := ht (OracleName.fb tg)
      have h2 := fb_e W p n tg
      have h3 : mAllB W p n (OracleName.fb tg) ≤ xFb (L := L) p n := by cases tg <;> omega
      omega)
  have hfb : (mAllB W p n (OracleName.fb Tag.test) : ℝ≥0∞) *
          (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
        ((mAllB W p n (OracleName.fb Tag.link) : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) +
          (mAllB W p n (OracleName.fb Tag.onl) : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam)) =
      (xFb (L := L) p n : ℝ≥0∞) * (T + xFb (L := L) p n : ℕ) / 2 ^ (min p.sFS lam) := by
    have hf' : (mAllB W p n (OracleName.fb Tag.test) : ℝ≥0∞) +
          ((mAllB W p n (OracleName.fb Tag.link) : ℝ≥0∞) + (mAllB W p n (OracleName.fb Tag.onl) : ℝ≥0∞)) =
        (xFb (L := L) p n : ℝ≥0∞) := by
      rw [← hfs]
      push_cast
      ring
    rw [← hf']
    simp only [div_eq_mul_inv]
    ring
  refine le_trans
    (add_le_add hleaf
      (add_le_add hnode
        (add_le_add hrl
          (add_le_add hrn
            (add_le_add (step Tag.test)
              (add_le_add (step Tag.link)
                (add_le_add (step Tag.onl) (add_le_add le_rfl (add_le_add le_rfl hg)))))))))
    (le_of_eq ?_)
  rw [← hfb]
  ring

end Compile.Batch.Disc
