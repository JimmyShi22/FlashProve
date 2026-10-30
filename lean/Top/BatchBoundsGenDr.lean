-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/BatchBoundsGenDr.lean: two counts (`xTree`, `xReq` of Compile/Batch/; what each
  bounds: the docstrings of `A`, `Rq`, Top/BatchBoundsGen.lean) and the completeness
  bound α of the compiled scheme, for any challenge samplers, as formulas in a record of counts.
  (Terms: lean/GLOSSARY.md.)

  The statements are at the record of protocols `LBd` and its wire record `WBd` of
  Top/BatchDraw.lean. The record `CountNumsB`, what it has to bound (`CountsB`), and the formulas
  `tv`, `A`, `Bf`, `Rq` are those of Top/BatchBoundsGen.lean. The reason: a wire record depends on
  the samplers only through the number of blocks of a round, and that number enters none of them.
  Below, κ₀ and n0 are free (the binders of `alphaB_le`), and kt = κ₀^n0; under `BatchProtocol.Draws.Good` and
  `BatchProtocol.Draws.TotLe` (Iop/BatchWireDraw.lean) κ₀ is the bias of one block and n0 a bound on the
  blocks of all rounds of one protocol.
    `alphaD kt`    = kt · pT + kt · pL + N · kt · pO, where pT, pL, pO are the abort probabilities
                   in the record of counts and N is its number of slots.
    `CountsBD.xTree_le`, `xReq_eq`, `alphaB_le`:
        under `CountsB`, `A` bounds the term `xTree` of `Compile.Batch`;
        `Rq` is `xReq`; `alphaD (κ₀^n0)` bounds `alphaB`.
    `alphaD_mono`  Monotone in kt: a numeral that bounds κ₀^n0 may replace it.

  Notation: `LBd`: `L` with challenges derived from hash blocks; `WBd`: `QueryLayout.ofDraws ..` (both:
  Top/BatchDraw.lean); `CountNumsB`: the counts of the three protocols, numbers only
  (Top/BatchBoundsGen.lean).

  Limits: This file has no formula and no bound for ε or ζ.
-/
import Top.BatchBoundsGen
import Top.BatchDraw

noncomputable section

namespace Top
open Iop Rom ZKCP Compile Compile.Batch Blocks Top.Batch Top.BatchLeaves
open scoped ENNReal

/-! ## The wire records -/

theorem maxDepth_ofLocalD_le (lam K : ℕ) :
    ∀ (s : Shape) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPos pts),
      RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps) ≤ depths s pts
  | [], _, _, _ => Nat.le_refl _
  | _ :: s, (_, pts), (_, ds), (_, nps) =>
      max_le_max (max_le (Nat.zero_le _) (Nat.le_refl _)) (maxDepth_ofLocalD_le lam K s pts ds nps)

theorem maxDepth_ofDraws_le (lam K : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPosB A pts),
      RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps) ≤ depths s pts
  | [], _, _, _, _ => Nat.le_refl _
  | r :: s, (a, A), (pt, pts), (_, ds), (_, _, nps) => by
      letI := pt.finPos
      exact max_le_max
        (max_le (Nat.clog_mono_right 2 (Fintype.card_subtype_le _))
          (Nat.clog_mono_right 2 (Fintype.card_subtype_le _)))
        (maxDepth_ofDraws_le lam K s A pts ds nps)

theorem cTrees_ofLocalD_le (lam K : ℕ) :
    ∀ (s : Shape) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPos pts),
      cTrees _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps) 1 ≤ leaves s pts + s.length
  | [], _, _, _ => Nat.zero_le _
  | r :: s, (pt, pts), (_, ds), (_, nps) => by
      have ih := cTrees_ofLocalD_le lam K s pts ds nps
      show 1 * 2 ^ depthR pt + 2 ^ 0 + cTrees _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps) 1 ≤
        (2 ^ depthR pt + leaves s pts) + (s.length + 1)
      omega

theorem cTrees_ofDraws (lam K Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPosB A pts),
      cTrees _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps) Ns = Ns * lvJ s A pts + lv0 s A pts
  | [], _, _, _, _ => rfl
  | _ :: s, (a, A), (pt, pts), (_, ds), (_, _, nps) => by
      have ih := cTrees_ofDraws lam K Ns s A pts ds nps
      show Ns * 2 ^ Nat.clog 2 (a.cardJ pt) + 2 ^ Nat.clog 2 (a.card0 pt) +
          cTrees _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps) Ns =
        Ns * (2 ^ Nat.clog 2 (a.cardJ pt) + lvJ s A pts) +
          (2 ^ Nat.clog 2 (a.card0 pt) + lv0 s A pts)
      rw [ih, Nat.mul_add]
      omega

/-! ## The formulas -/

namespace CountNumsB
variable (c : CountNumsB) (no : OpenNums) (p : Params) (lam : ℕ)

def alphaD (kt : ℝ≥0∞) : ℝ≥0∞ := kt * c.pT + kt * c.pL + (c.N : ℝ≥0∞) * (kt * c.pO)

theorem alphaD_mono {kt kt' : ℝ≥0∞} (h : kt ≤ kt') : c.alphaD kt ≤ c.alphaD kt' := by
  unfold alphaD; gcongr

/-! ### Under `CountsB`, the formulas bound the terms of `Compile.Batch` at `LBd` and `WBd`
(namespace `CountsBD`, below) -/

end CountNumsB

open CountsB (arV)

namespace CountsBD
variable {I X : Type} (lam : ℕ) {L : BatchProtocol I X} {pT : L.offline.shape.IsPoint}
  {pL : L.link.shape.IsPoint} {pB : L.onlineBatch.loc.shape.IsPoint} (z : L.Symbol)
  (no : OpenNums) (dr : L.Draws lam) {ax : L.Aux pT pL pB} {M : LH.Nums}
  {c : CountNumsB} (h : CountsB L pT pL pB ax M c)
include h

theorem xTree_le (p : Params) (n : ℕ) : xTree (WBd lam L pT pL pB z no dr ax) p n ≤ c.A p n := by
  show (p.leaves + 1) * 2 ^ Nat.clog 2 L.wordLength +
      cTrees _ _ (RoundsQueryLayout.ofLocalD lam (dr.K) L.offline.shape pT dr.T ax.posT) 1 +
      p.leaves * cTrees _ _ (RoundsQueryLayout.ofLocalD lam (dr.K) L.link.shape pL dr.Lk ax.posL) 1 +
      n * cTrees _ _ (RoundsQueryLayout.ofDraws lam (dr.K) L.onlineBatch.loc.shape L.onlineBatch.ann pB dr.B ax.posB) L.maxBatchSize ≤ _
  rw [cTrees_ofDraws, h.N]
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left _ h.lI)
        (le_trans (cTrees_ofLocalD_le _ _ _ _ _ _) (Nat.add_le_add h.lT h.rT)))
      (Nat.mul_le_mul_left _
        (le_trans (cTrees_ofLocalD_le _ _ _ _ _ _) (Nat.add_le_add h.lL h.rL))))
    (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ h.lJ) h.l0))

theorem xReq_eq (n : ℕ) : xReq (LBd lam L dr) n = c.Rq n := by
  show n * L.maxBatchSize = n * c.N
  rw [h.N]

theorem alphaB_le (κ₀ : ℝ≥0∞) (n0 : ℕ) :
    alphaB (LBd lam L dr) (numsDraw lam L dr M κ₀ n0) ≤ c.alphaD (κ₀ ^ n0) := by
  show κ₀ ^ n0 * M.pT + κ₀ ^ n0 * M.pL + (L.maxBatchSize : ℝ≥0∞) * (κ₀ ^ n0 * M.pO) ≤ _
  rw [h.N]
  unfold CountNumsB.alphaD
  have h1 := h.pT
  have h2 := h.pL
  have h3 := h.pO
  gcongr

end CountsBD

end Top
