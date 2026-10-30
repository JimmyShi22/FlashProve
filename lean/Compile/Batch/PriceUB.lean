-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PriceUB.lean: the marked queries of deferred programming (both notions: the head of
Rom/Defer.lean) in one setup and n batches of at most B requests, counted in B. A definition
(`mAllU`), and bounds oracle by oracle (words of this library: lean/GLOSSARY.md).
This file does not prove a bound for the sum of the lemma on deferred programming (`Rom.Spec.defer`,
Rom/Defer.lean).

The prover with no query for an empty slot (Compile/Batch/StarU.lean) makes, for such a batch, only
the marked queries of B slots, of the shared part and of the inner nodes of the request tree
(`mPU W B`, Compile/Batch/CountU.lean: `markPpU`, see its statement).
  `rleaf_leU`, `g_onl_leU`           at the leaf oracle of request trees and at g: at most n B
  `rnode_leU`                        at the node oracle of request trees: at most xReq L n
  `g_test_eqU`, `g_link_eqU`         none at g for Test and for Link
Limits: it does not say that the runs keep these numbers: that is Compile/Batch/CountURun.lean
(`countRunU`).
The analogue of Compile/Batch/DisciplineSum.lean, for `mAllU`: of its lemmas `rleaf_le`, `rnode_le`,
`g_onl_le`, `g_test_eq`, `g_link_eq`.
-/
import Compile.Batch.CountU
import Compile.Batch.DisciplineSum

noncomputable section

namespace Compile.Batch
open Iop Rom
open scoped ENNReal
open Disc Disc.Sum

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}


/-- the marked queries of the setup and of n batches of at most B requests -/
def mAllU (W : QueryLayout lam L) (p : Params) (B n : ℕ) : OracleName → ℕ := fun o => mCB W p o + n * mPU W B o

namespace SumU

theorem term_le {M a B b : ℕ} (k : ℕ) (hM : M ≤ B) (ha : a ≤ b) :
    (M : ℝ≥0∞) * (a : ℕ) / 2 ^ k ≤ (B : ℝ≥0∞) * (b : ℕ) / 2 ^ k := by
  have h1 : (M : ℝ≥0∞) ≤ B := by exact_mod_cast hM
  have h2 : (a : ℝ≥0∞) ≤ b := by exact_mod_cast ha
  gcongr

theorem term_zero {M a : ℕ} (k : ℕ) (hM : M = 0) : (M : ℝ≥0∞) * (a : ℕ) / 2 ^ k = 0 := by
  rw [hM, Nat.cast_zero, zero_mul, ENNReal.zero_div]

variable (W : QueryLayout lam L) (p : Params) (B n : ℕ)


omit W p in
theorem joinsB_le (c : ℕ) : n * (joins L.onlineBatch.loc.shape L.onlineBatch.ann * c) ≤ n * c :=
  Nat.mul_le_mul_left n
    (le_trans (Nat.mul_le_mul_right _ (joins_le_one _ _)) (le_of_eq (Nat.one_mul _)))

theorem rleaf_leU : mAllU W p B n OracleName.rleaf ≤ n * B ∧ eAllB W p n OracleName.rleaf = 0 := by
  refine ⟨?_, (rleaf_le W p n).2⟩
  show 0 + joins L.offline.shape (RoundSplits.allLocal _) * 1 +
      (p.M + 1) * (0 + joins L.link.shape (RoundSplits.allLocal _) * 1) +
      n * (joins L.onlineBatch.loc.shape L.onlineBatch.ann * B) ≤ _
  rw [joins_allLocal, joins_allLocal]
  simpa using joinsB_le (L := L) n B

theorem rnode_leU : mAllU W p B n OracleName.rnode ≤ xReq L n ∧ eAllB W p n OracleName.rnode = 0 := rnode_le W p n

theorem g_onl_leU : mAllU W p B n (OracleName.g Tag.onl) ≤ n * B ∧ eAllB W p n (OracleName.g Tag.onl) = 0 := by
  refine ⟨?_, (g_onl_le W p n).2⟩
  show 0 + 0 + (p.M + 1) * (0 + 0) + n * (joins L.onlineBatch.loc.shape L.onlineBatch.ann * B) ≤ _
  simpa using joinsB_le (L := L) n B

theorem g_test_eqU : mAllU W p B n (OracleName.g Tag.test) = 0 := g_test_eq W p n
theorem g_link_eqU : mAllU W p B n (OracleName.g Tag.link) = 0 := g_link_eq W p n

end SumU

theorem cTrees_mono {K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) {a b : ℕ},
      a ≤ b → cTrees s A W a ≤ cTrees s A W b
  | [], _, _, _, _, _ => le_rfl
  | _ :: s, (_, A), (_, W), _, _, h =>
    Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _) (cTrees_mono s A W h)


end Compile.Batch
