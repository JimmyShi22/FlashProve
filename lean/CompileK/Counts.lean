-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Counts.lean: the compiler's counts in closed form, for any interface L and any data D of
the compilation (`DataK`, CompileK/Main.lean; the generic wires).

Statements and proofs.

The three bounds of the compiler's theorem (α = `alphaBG`, ε = `epsB`, ζ = `zetaBGen`)
read numbers of the wire and of the scheme.
Here each of these numbers is written out, exactly, in numbers of the shapes of the three IOPs, and
then bounded with free numbers as hypotheses, so that numerals follow by arithmetic.

Main names, by the parts of the file:
  Part 1, numbers of a shape whose oracles are strings (`Shape.IsPoint`): `lvOf`, `Shape.lvLoc`,
    `Shape.dpLoc`, `Shape.lvJ`, `Shape.lv0`, `Shape.dpB`. For local rounds in which only the slots
    speak: `lvJ_allLocal`, `lv0_allLocal` (an empty tree has one leaf), `dpB_allLocal`.
  Part 2, the generic wires have these numbers: `cTrees_ofLocalD`, `maxDepth_ofLocalD`,
    `cTrees_ofDraws`, `maxDepth_ofDraws`.
  Part 3, exact: `tVB_data`, `xTree_data` (evaluations of the leaf oracle in setup and n batches),
    `xFb_data`, `xReq_data`.
  Part 4, wires without tests (`W.OK`, Iop/BatchWire.lean): `alphaBG_of_ok` (α = pT + pL + maxBatchSize pO),
    `xGr_of_ok` (no searches), `hashTerms_le_of`: hashTermsBGTot W p q n ≤ (q Y + 6 Y²) / 2^e for
    every Y at least xTree, xFb, xReq and every e at most the two salt lengths and λ.
  Part 5, with free numbers, each under the hypotheses of its statement: `tVB_le_of`:
    tVB ≤ r + 3 + o (d + 1) + 3 (depthReq + 1); `alphaBG_data`; `epsB_data` (ε unfolded; bounds on
    it: Cm/ParBounds.lean); `zetaBGen_le_of`; `overrun_zero` (the overrun term:
    0 for n ≤ s1); `deltaB_data`.

Limits: this file says nothing on numerals, and nothing on any security level. The counts are those
of the bounds as the library states them (upper bounds on what the algorithms do: for instance the
node oracle is counted like the leaf oracle). `hashTerms_le_of` is loose: one number Y for three
counts, one exponent e for three.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Main
import Compile.Batch.TotalG
import Blocks.Basic
import Blocks.Numbering
import Blocks.Batch.Numbering
import Rom.ExitPriv
import Iop.WireOf
import Iop.PullProofs
import Code.FieldEnum
import ZKCP.Defs
import Mathlib.Data.Matrix.Mul
import Code.RS
import Code.Field
import Iop.Univ
import Blocks.Opens
import Blocks.LowerKit
import Blocks.SerS
import Iop.WireOK
import Blocks.Small
import Blocks.Leaves
import Prob.Tail
import Rom.EagerAudited
import Compile.Extraction
import Top.Extraction
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.FinEnum
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

noncomputable section

namespace Iop

/-! ## Part 1. Numbers of a shape whose oracles are strings (`Shape.IsPoint`) -/

/-- the leaves of the tree over c positions -/
def lvOf (c : ℕ) : ℕ := 2 ^ Nat.clog 2 c

theorem lvOf_le (c : ℕ) : lvOf c ≤ 2 * c + 1 := by
  unfold lvOf
  rcases Nat.lt_or_ge 1 c with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h2 : Nat.clog 2 c = (Nat.clog 2 c).pred + 1 :=
      (Nat.succ_pred_eq_of_pos (Nat.clog_pos (by norm_num) h)).symm
    rw [h2, pow_succ]
    omega
  · rw [Nat.clog_of_right_le_one h]
    omega

theorem lvOf_pow (k : ℕ) : lvOf (2 ^ k) = 2 ^ k := by
  unfold lvOf
  rw [Nat.clog_pow _ _ (by norm_num)]

namespace Shape

/-- an ordinary IOP: the leaves of the trees over all its oracles -/
def lvLoc : (s : Shape) → s.IsPoint → ℕ
  | [], _ => 0
  | r :: s, (pt, pts) => lvOf (@Fintype.card r.Pos pt.finPos) + lvLoc s pts

/-- an ordinary IOP: the depth of its deepest tree -/
def dpLoc : (s : Shape) → s.IsPoint → ℕ
  | [], _ => 0
  | r :: s, (pt, pts) => max (Nat.clog 2 (@Fintype.card r.Pos pt.finPos)) (dpLoc s pts)

/-- a batch IOP: the leaves of the trees over the components of one slot -/
def lvJ : (s : Shape) → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (pt, pts) => lvOf (a.cardJ pt) + lvJ s A pts

/-- a batch IOP: the leaves of the trees over the shared components -/
def lv0 : (s : Shape) → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (pt, pts) => lvOf (a.card0 pt) + lv0 s A pts

/-- a batch IOP: the depth of its deepest tree -/
def dpB : (s : Shape) → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (pt, pts) =>
    max (max (Nat.clog 2 (a.card0 pt)) (Nat.clog 2 (a.cardJ pt))) (dpB s A pts)

theorem length_pull : ∀ (s : Shape) (σ : Samplers s), (s.pull σ).length = s.length
  | [], _ => rfl
  | _ :: s, (_, σs) => congrArg (· + 1) (length_pull s σs)

/-! ### two shapes in a row -/

theorem lvLoc_app :
    ∀ {s t : Shape} (a : s.IsPoint) (b : t.IsPoint),
      lvLoc (s ++ t) (Blocks.pointApp a b) = lvLoc s a + lvLoc t b
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, as), b => by
      show _ + lvLoc _ (Blocks.pointApp as b) = _ + lvLoc _ as + _
      rw [lvLoc_app as b, Nat.add_assoc]

theorem dpLoc_app :
    ∀ {s t : Shape} (a : s.IsPoint) (b : t.IsPoint),
      dpLoc (s ++ t) (Blocks.pointApp a b) = max (dpLoc s a) (dpLoc t b)
  | [], _, _, _ => (Nat.zero_max _).symm
  | _ :: _, _, (_, as), b => by
      show max _ (dpLoc _ (Blocks.pointApp as b)) = max (max _ (dpLoc _ as)) _
      rw [dpLoc_app as b, max_assoc]

theorem lvJ_app :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (a : s.IsPoint) (b : t.IsPoint),
      lvJ (s ++ t) (RoundSplits.app A B) (Blocks.pointApp a b) = lvJ s A a + lvJ t B b
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, A), B, (_, as), b => by
      show _ + lvJ _ (RoundSplits.app A B) (Blocks.pointApp as b) = _ + lvJ _ A as + _
      rw [lvJ_app A B as b, Nat.add_assoc]

theorem lv0_app :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (a : s.IsPoint) (b : t.IsPoint),
      lv0 (s ++ t) (RoundSplits.app A B) (Blocks.pointApp a b) = lv0 s A a + lv0 t B b
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, A), B, (_, as), b => by
      show _ + lv0 _ (RoundSplits.app A B) (Blocks.pointApp as b) = _ + lv0 _ A as + _
      rw [lv0_app A B as b, Nat.add_assoc]

theorem dpB_app :
    ∀ {s t : Shape} (A : RoundSplits s) (B : RoundSplits t) (a : s.IsPoint) (b : t.IsPoint),
      dpB (s ++ t) (RoundSplits.app A B) (Blocks.pointApp a b) = max (dpB s A a) (dpB t B b)
  | [], _, _, _, _, _ => (Nat.zero_max _).symm
  | _ :: _, _, (_, A), B, (_, as), b => by
      show max _ (dpB _ (RoundSplits.app A B) (Blocks.pointApp as b)) = max (max _ (dpB _ A as)) _
      rw [dpB_app A B as b]
      exact (max_assoc _ _ _).symm

end Shape

/-! ### local rounds in which only the slots speak -/

theorem RAnn.cardJ_allLocal (r : Round) (pt : r.IsPoint) :
    (RAnn.allLocal r).cardJ pt = @Fintype.card r.Pos pt.finPos := by
  letI := pt.finPos
  exact Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)

theorem RAnn.card0_allLocal (r : Round) (pt : r.IsPoint) : (RAnn.allLocal r).card0 pt = 0 := by
  letI := pt.finPos
  haveI : IsEmpty {p : r.Pos // (RAnn.allLocal r).own p = false} := ⟨fun x => Bool.noConfusion x.2⟩
  exact Fintype.card_eq_zero

namespace Shape

theorem lvJ_allLocal : ∀ (s : Shape) (pts : s.IsPoint), lvJ s (RoundSplits.allLocal s) pts = lvLoc s pts
  | [], _ => rfl
  | r :: s, (pt, pts) => by
      show lvOf ((RAnn.allLocal r).cardJ pt) + lvJ s (RoundSplits.allLocal s) pts = _
      rw [RAnn.cardJ_allLocal, lvJ_allLocal s pts]
      rfl

theorem lv0_allLocal : ∀ (s : Shape) (pts : s.IsPoint), lv0 s (RoundSplits.allLocal s) pts = s.length
  | [], _ => rfl
  | r :: s, (pt, pts) => by
      show lvOf ((RAnn.allLocal r).card0 pt) + lv0 s (RoundSplits.allLocal s) pts = s.length + 1
      rw [RAnn.card0_allLocal, lv0_allLocal s pts]
      show 2 ^ Nat.clog 2 0 + s.length = s.length + 1
      rw [Nat.clog_of_right_le_one (Nat.zero_le 1), pow_zero, Nat.add_comm]

theorem dpB_allLocal : ∀ (s : Shape) (pts : s.IsPoint), dpB s (RoundSplits.allLocal s) pts = dpLoc s pts
  | [], _ => rfl
  | r :: s, (pt, pts) => by
      show max
          (max (Nat.clog 2 ((RAnn.allLocal r).card0 pt)) (Nat.clog 2 ((RAnn.allLocal r).cardJ pt)))
          (dpB s (RoundSplits.allLocal s) pts) = _
      rw [RAnn.card0_allLocal, RAnn.cardJ_allLocal, dpB_allLocal s pts,
        Nat.clog_of_right_le_one (Nat.zero_le 1), Nat.zero_max]
      rfl

end Shape
end Iop

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw
open scoped ENNReal

/-! ## Part 2. The generic wires -/

section Wires
variable {lam K : ℕ}

theorem cTrees_ofLocalD (Ns : ℕ) :
    ∀ (s : Shape) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPos pts),
      cTrees _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps) Ns = Ns * s.lvLoc pts + s.length
  | [], _, _, _ => rfl
  | r :: s, (pt, pts), (_, ds), (_, nps) => by
      show Ns * lvOf (@Fintype.card r.Pos pt.finPos) + 2 ^ 0 +
          cTrees _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps) Ns =
        Ns * (lvOf (@Fintype.card r.Pos pt.finPos) + Shape.lvLoc s pts) + (s.length + 1)
      rw [cTrees_ofLocalD Ns s pts ds nps, Nat.mul_add]
      omega

theorem maxDepth_ofLocalD : ∀ (s : Shape) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPos pts),
    RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps) = s.dpLoc pts
  | [], _, _, _ => rfl
  | r :: s, (pt, pts), (_, ds), (_, nps) => by
      show max (max 0 (Nat.clog 2 (@Fintype.card r.Pos pt.finPos)))
          (RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofLocalD lam K s pts ds nps)) = _
      rw [maxDepth_ofLocalD s pts ds nps, Nat.zero_max]
      rfl

theorem cTrees_ofDraws (Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPosB A pts),
      cTrees _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps) Ns = Ns * s.lvJ A pts + s.lv0 A pts
  | [], _, _, _, _ => rfl
  | _ :: s, (a, A), (pt, pts), (_, ds), (_, _, nps) => by
      show Ns * lvOf (a.cardJ pt) + lvOf (a.card0 pt) +
          cTrees _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps) Ns =
        Ns * (lvOf (a.cardJ pt) + Shape.lvJ s A pts) + (lvOf (a.card0 pt) + Shape.lv0 s A pts)
      rw [cTrees_ofDraws Ns s A pts ds nps, Nat.mul_add]
      omega

theorem maxDepth_ofDraws :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint) (ds : s.Draws lam) (nps : s.NumPosB A pts),
      RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps) = s.dpB A pts
  | [], _, _, _, _ => rfl
  | _ :: s, (a, A), (pt, pts), (_, ds), (_, _, nps) => by
      show max (max (Nat.clog 2 (a.card0 pt)) (Nat.clog 2 (a.cardJ pt)))
          (RoundsQueryLayout.maxDepth _ _ (RoundsQueryLayout.ofDraws lam K s A pts ds nps)) = _
      rw [maxDepth_ofDraws s A pts ds nps]
      rfl

end Wires

/-! ## Part 3. The counts of the compiled scheme, exactly -/

section Data
variable {I X : Type} {L : BatchProtocol I X} {lam : ℕ} (D : DataK L lam)

/-- the depth of the tree over an encoded index -/
def DataK.dE (_ : DataK L lam) : ℕ := Nat.clog 2 L.wordLength

theorem lenT_data : D.L.offline.shape.length = L.offline.shape.length := Shape.length_pull _ _
theorem lenL_data : D.L.link.shape.length = L.link.shape.length := Shape.length_pull _ _
theorem lenB_data : D.L.onlineBatch.loc.shape.length = L.onlineBatch.loc.shape.length := Shape.length_pull _ _

/-- The verifier's queries on one proof: for each of the three protocols one Fiat-Shamir query a
round and one more, a leaf and a path for each opening, and a leaf and a path in the request
tree. -/
theorem tVB_data :
    tVB D.W = (L.offline.shape.length + 1 +
          (D.no.T * (max D.dE (L.offline.shape.dpLoc D.pT) + 1) + (D.ax.depthReq + 1))) +
        (L.link.shape.length + 1 +
          (D.no.L * (max D.dE (L.link.shape.dpLoc D.pL) + 1) + (D.ax.depthReq + 1))) +
        (L.onlineBatch.loc.shape.length + 1 +
          (D.no.O * (max D.dE (L.onlineBatch.loc.shape.dpB L.onlineBatch.ann D.pB) + 1) +
            (D.ax.depthReq + 1))) := by
  show (D.L.offline.shape.length + 1 +
        (D.no.T * (max (Nat.clog 2 L.wordLength)
                (RoundsQueryLayout.maxDepth _ _
                  (RoundsQueryLayout.ofLocalD lam D.dr.K L.offline.shape D.pT D.dr.T D.ax.posT)) + 1) +
          (D.ax.depthReq + 1))) +
      (D.L.link.shape.length + 1 +
        (D.no.L * (max (Nat.clog 2 L.wordLength)
                (RoundsQueryLayout.maxDepth _ _
                  (RoundsQueryLayout.ofLocalD lam D.dr.K L.link.shape D.pL D.dr.Lk D.ax.posL)) + 1) +
          (D.ax.depthReq + 1))) +
      (D.L.onlineBatch.loc.shape.length + 1 +
        (D.no.O * (max (Nat.clog 2 L.wordLength)
                (RoundsQueryLayout.maxDepth _ _
                  (RoundsQueryLayout.ofDraws lam D.dr.K L.onlineBatch.loc.shape L.onlineBatch.ann D.pB D.dr.B D.ax.posB)) +
              1) +
          (D.ax.depthReq + 1))) = _
  rw [lenT_data, lenL_data, lenB_data, maxDepth_ofLocalD, maxDepth_ofLocalD, maxDepth_ofDraws]
  rfl

/-- Evaluations of the leaf oracle (and, as a bound, of the node oracle) in setup and n batches. -/
theorem xTree_data (n : ℕ) :
    xTree D.W D.p n =
      (D.p.leaves + 1) * 2 ^ D.dE + (L.offline.shape.lvLoc D.pT + L.offline.shape.length) +
        D.p.leaves * (L.link.shape.lvLoc D.pL + L.link.shape.length) +
        n * (L.maxBatchSize * L.onlineBatch.loc.shape.lvJ L.onlineBatch.ann D.pB + L.onlineBatch.loc.shape.lv0 L.onlineBatch.ann D.pB) := by
  show (D.p.leaves + 1) * 2 ^ Nat.clog 2 L.wordLength +
      cTrees _ _ (RoundsQueryLayout.ofLocalD lam D.dr.K L.offline.shape D.pT D.dr.T D.ax.posT) 1 +
      D.p.leaves * cTrees _ _ (RoundsQueryLayout.ofLocalD lam D.dr.K L.link.shape D.pL D.dr.Lk D.ax.posL) 1 +
      n *
        cTrees _ _ (RoundsQueryLayout.ofDraws lam D.dr.K L.onlineBatch.loc.shape L.onlineBatch.ann D.pB D.dr.B D.ax.posB) L.maxBatchSize =
    _
  rw [cTrees_ofLocalD, cTrees_ofLocalD, cTrees_ofDraws, Nat.one_mul, Nat.one_mul]
  rfl

/-- Fiat-Shamir evaluations in setup and n batches. -/
theorem xFb_data (n : ℕ) :
    xFb (L := D.L) D.p n =
      2 * L.offline.shape.length + D.p.leaves * (2 * L.link.shape.length) +
        n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length) := by
  show 2 * D.L.offline.shape.length + D.p.leaves * (2 * D.L.link.shape.length) +
      n * ((L.maxBatchSize + 1) * D.L.onlineBatch.loc.shape.length) = _
  rw [lenT_data, lenL_data, lenB_data]

theorem xReq_data (n : ℕ) : xReq D.L n = n * L.maxBatchSize := rfl

end Data

/-! ## Part 4. Wires without tests -/

section Plain
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem cFail_of_ok {K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OK s A W → cFail s A W = 0
  | [], _, _, _ => rfl
  | _ :: s, (a, A), (w, W), h => by
      show (match a.kind with
        | .lo => failOf w.grJ
        | .sh => failOf w.gr0) + cFail s A W = 0
      rw [h.1.grJ_none, h.1.gr0_none, cFail_of_ok s A W h.2]
      cases a.kind <;> simp [failOf]

/-- α at a wire without tests (`W.OK`): the probabilities of the withheld sets, and nothing else. -/
theorem alphaBG_of_ok {W : QueryLayout lam L} (hW : W.OK) (M : LH.Nums) :
    alphaBG W M = M.pT + M.pL + L.maxBatchSize * M.pO := by
  unfold alphaBG
  rw [cFail_of_ok _ _ _ hW.T.sh, cFail_of_ok _ _ _ hW.Lk.sh, cFail_of_ok _ _ _ hW.B.sh]
  simp [alphaB]

theorem xGr_of_ok {W : QueryLayout lam L} (hW : W.OK) (p : Params) (n : ℕ) : xGr W p n = 0 := by
  unfold xGr
  rw [cTry_plain _ _ _ _ _ hW.T.sh, cTry_plain _ _ _ _ _ hW.Lk.sh, cTry_plain _ _ _ _ _ hW.B.sh]
  simp

theorem frac_le {a Y k e : ℕ} (ha : a ≤ Y) (he : e ≤ k) : (a : ℝ≥0∞) / 2 ^ k ≤ (Y : ℝ≥0∞) / 2 ^ e :=
  ENNReal.div_le_div (Nat.cast_le.2 ha) (pow_le_pow_right₀ one_le_two he)

theorem sq_frac_le {a c Y k e : ℕ} (ha : a ≤ Y) (hc : c ≤ Y) (he : e ≤ k) :
    (a : ℝ≥0∞) * ((0 + c : ℕ) : ℝ≥0∞) / 2 ^ k ≤ ((Y * Y : ℕ) : ℝ≥0∞) / 2 ^ e := by
  have h : a * (0 + c) ≤ Y * Y := by
    rw [Nat.zero_add]
    exact Nat.mul_le_mul ha hc
  have h' := frac_le h he
  rwa [Nat.cast_mul] at h'

/-- The hash terms of ζ, for one budget of q queries and n batches: for every number Y at least the
three counts and every e at most the two salt lengths and λ. (not all hypotheses are named here:
see the statement below) -/
theorem hashTerms_le_of {W : QueryLayout lam L} (hW : W.OK) (p : Params) (q n Y e : ℕ)
    (h1 : xTree W p n ≤ Y) (h2 : xFb (L := L) p n ≤ Y) (h3 : xReq L n ≤ Y) (e1 : e ≤ p.sMT)
    (e2 : e ≤ p.sFS) (e3 : e ≤ lam) :
    hashTermsBGTot W p q n ≤ ((q * Y + 6 * (Y * Y) : ℕ) : ℝ≥0∞) / 2 ^ e := by
  have e4 : e ≤ min p.sFS lam := le_min e2 e3
  have hmu : muB W p n ≤ (Y : ℝ≥0∞) / 2 ^ e :=
    max_le (frac_le h1 e1) (max_le (frac_le h1 e3) (max_le (frac_le h2 e4) (frac_le h3 e3)))
  have hsq : hashSqBG W p n ≤ 6 * (((Y * Y : ℕ) : ℝ≥0∞) / 2 ^ e) := by
    unfold hashSqBG
    rw [xGr_of_ok hW, Nat.cast_zero, zero_mul, ENNReal.zero_div, add_zero]
    calc
      _ ≤ ((Y * Y : ℕ) : ℝ≥0∞) / 2 ^ e + ((Y * Y : ℕ) : ℝ≥0∞) / 2 ^ e +
            ((Y * Y : ℕ) : ℝ≥0∞) / 2 ^ e + 3 * (((Y * Y : ℕ) : ℝ≥0∞) / 2 ^ e) :=
          add_le_add (add_le_add (add_le_add (sq_frac_le h1 h1 e1) (sq_frac_le h1 h1 e3))
              (sq_frac_le h2 h2 e4))
            (mul_le_mul_right (sq_frac_le h3 h3 e3) _)
      _ = 6 * (((Y * Y : ℕ) : ℝ≥0∞) / 2 ^ e) := by ring
  calc hashTermsBGTot W p q n = (q : ℝ≥0∞) * muB W p n + hashSqBG W p n := rfl
    _ ≤ (q : ℝ≥0∞) * ((Y : ℝ≥0∞) / 2 ^ e) + 6 * (((Y * Y : ℕ) : ℝ≥0∞) / 2 ^ e) :=
      add_le_add (mul_le_mul_right hmu _) hsq
    _ = ((q * Y + 6 * (Y * Y) : ℕ) : ℝ≥0∞) / 2 ^ e := by
      rw [← mul_div_assoc, ← mul_div_assoc, ENNReal.div_add_div_same]
      push_cast
      rfl

end Plain

/-! ## Part 5. The bounds of the compiler's theorem, with free numbers -/

section Free
variable {I X : Type} {L : BatchProtocol I X} {lam : ℕ} (D : DataK L lam)

/-- The verifier's queries: r bounds the rounds of the three protocols together, o the announced
openings together, d all depths. -/
theorem tVB_le_of (r o d : ℕ)
    (hr : L.offline.shape.length + L.link.shape.length + L.onlineBatch.loc.shape.length ≤ r)
    (ho : D.no.T + D.no.L + D.no.O ≤ o) (hE : D.dE ≤ d) (hT : L.offline.shape.dpLoc D.pT ≤ d)
    (hL : L.link.shape.dpLoc D.pL ≤ d) (hB : L.onlineBatch.loc.shape.dpB L.onlineBatch.ann D.pB ≤ d) :
    tVB D.W ≤ r + 3 + o * (d + 1) + 3 * (D.ax.depthReq + 1) := by
  rw [tVB_data]
  have a1 := Nat.mul_le_mul_left D.no.T (Nat.succ_le_succ (max_le hE hT))
  have a2 := Nat.mul_le_mul_left D.no.L (Nat.succ_le_succ (max_le hE hL))
  have a3 := Nat.mul_le_mul_left D.no.O (Nat.succ_le_succ (max_le hE hB))
  have a4 := Nat.mul_le_mul_right (d + 1) ho
  rw [Nat.add_mul, Nat.add_mul] at a4
  simp only [Nat.succ_eq_add_one] at a1 a2 a3
  omega

/-- the laws of the generic wires -/
theorem DataK.ok (ho : L.Opens D.no) (hN : L.maxBatchSize = 2 ^ D.ax.depthReq) : D.W.OK :=
  (wireBDOK _ _ lam L D.pT D.pL D.pB D.z D.no D.dr D.ax ho hN).1

/-- α, under the hypotheses below: κ₀^nb is the factor of the blocks of one protocol. -/
theorem alphaBG_data (ho : L.Opens D.no) (hN : L.maxBatchSize = 2 ^ D.ax.depthReq)
    (M : LH.Nums) (κ₀ : ℝ≥0∞) (nb : ℕ) :
    alphaBG D.W (D.nums M κ₀ nb) = κ₀ ^ nb * M.pT + κ₀ ^ nb * M.pL + L.maxBatchSize * (κ₀ ^ nb * M.pO) :=
  alphaBG_of_ok (D.ok ho hN) _

/-- ε, unfolded: the round-by-round error carries the factor κ₀^K of the blocks of one round (K is
`D.dr.K`). That error is a number that `M` lists (the data field `LH.Nums.εs`, Iop/InteractiveOracleProof.lean): that
the interface is sound at the number that is listed for it is no statement of this file; that tie is
`BatchProtocol.PropsK.soundK` (Hiop/Interface.lean). -/
theorem epsB_data (M : LH.Nums) (κ₀ : ℝ≥0∞) (nb tC tP : ℕ) :
    epsB D.W (D.nums M κ₀ nb) tC tP =
      ((tC + tP + tVB D.W + 1 : ℕ) : ℝ≥0∞) * (κ₀ ^ D.dr.K * M.εs) +
        2 * ((tC + tP + tVB D.W + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := rfl

/-- ζ, run by run. -/
theorem zetaBGen_le_of (ho : L.Opens D.no) (hN : L.maxBatchSize = 2 ^ D.ax.depthReq) (M : LH.Nums) (κ₀ : ℝ≥0∞)
    (nb q n Y e : ℕ) (h1 : xTree D.W D.p n ≤ Y) (h2 : xFb (L := D.L) D.p n ≤ Y) (h3 : n * L.maxBatchSize ≤ Y)
    (e1 : e ≤ D.p.sMT) (e2 : e ≤ D.p.sFS) (e3 : e ≤ lam) :
    zetaBGen D.L D.p (D.nums M κ₀ nb) (hashTermsBGTot D.W D.p) q n ≤
      D.p.leaves * binTail n D.p.leaves D.p.s1 + ((q * Y + 6 * (Y * Y) : ℕ) : ℝ≥0∞) / 2 ^ e +
        (κ₀ ^ nb * M.zT + D.p.leaves * (κ₀ ^ nb * M.zL) + n * (L.maxBatchSize * ((κ₀ ^ nb) ^ L.maxBatchSize * M.zO))) :=
  add_le_add_left (add_le_add_right
    (hashTerms_le_of (D.ok ho hN) D.p q n Y e h1 h2 h3 e1 e2 e3) _) _

theorem overrun_zero (p : Params) {n : ℕ} (h : n ≤ p.s1) :
    (p.leaves : ℝ≥0∞) * binTail n p.leaves p.s1 = 0 := by
  unfold binTail
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, mul_zero]

/-- The honest committer's extraction error. -/
theorem deltaB_data : deltaB D.W = 2 * ((2 * 2 ^ D.dE : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := rfl

end Free

end Compile.Batch
