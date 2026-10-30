-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngNums.lean: the bounds `pBad`, `pWin` of the lookup argument.

A stage (Blocks/Stage.lean) has bounds `pBad`, `pWin` for the probabilities of the public
part of its withheld set (`Hon.withheld`, Blocks/BlockHon.lean) and of the part that may depend on
the secret (`Stage.Props.prBad`, `prWin`). Here they are computed:

 * `LkPar.ndiv`: the number of dividing coordinates of a lookup argument (the verifier rejects the
   value 0 there): the coordinates of the points ϱ, ϱ3, ϱ5, ϱ' (Blocks/LookupBlock.lean) and the
   challenges of the layers of both sides; of the key side's last layer, whose challenges are the
   coordinates of the end point z, only those that `LkPar.zf` selects.
 * `Lk.stLookup_pBad`, `Lk.stLookup_pWin`: for the lookup argument `pBad` is ndiv / |E| and `pWin`
   is 0.
In the namespace `Lk`, 2 ≠ 0 in E is assumed.

Limits. The bound has the form of a union bound (number of dividing coordinates over |E|), not of
the exact value 1 - (1 - 1/|E|)^ndiv. `LkPar.ndiv` counts the dividing coordinates of one lookup
argument. The range reduction by calls (Blocks/RngCalls.lean) has one lookup argument for each call:
nothing is said here of its bounds.

Terms: lean/GLOSSARY.md.
-/
import Blocks.ClosingStage
import Blocks.LookupStage
import Blocks.RngForest
import Blocks.RngForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob Finset
open scoped ENNReal

/-- The bound for a point of n coordinates is n / |E|. -/
theorem pPt_eq (E : Type) [Field E] [Fintype E] (n : ℕ) :
    pPt E n = (n : ℝ≥0∞) / Fintype.card E := by
  unfold pPt Lk.ePt
  rw [Fintype.card_fun, Fintype.card_fin]
  cases n with
  | zero => simp
  | succ n =>
    have hq : (Fintype.card E : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [Nat.add_sub_cancel, pow_succ, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
      mul_comm ((Fintype.card E : ℝ≥0∞) ^ n) (Fintype.card E : ℝ≥0∞)]
    exact ENNReal.mul_div_mul_right
      _ _ (pow_ne_zero _ hq) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

/-- The number of the l + σ + 1 challenges of layer l of the key side that are rejected at 0: all,
but in the last layer, whose challenges are the coordinates of the end point z; there those that
`LkPar.zf` selects. -/
def LkPar.kDiv {E : Type} (P : LkPar E) (l : ℕ) : ℕ :=
  (List.range (l + P.σ + 1)).countP (P.kf (l + 1))

theorem LkPar.kDiv_of_lt {E : Type} (P : LkPar E) {l : ℕ} (h : l + 1 < P.D) :
    P.kDiv l = l + P.σ + 1 := by
  unfold LkPar.kDiv
  rw [List.countP_eq_length.mpr fun t _ => P.kf_of_lt h t, List.length_range]

/-- If every coordinate of z is checked, all challenges of all layers are rejected at 0. -/
theorem LkPar.kDiv_of_all {E : Type} (P : LkPar E) (h : ∀ t, P.zf t = true) (l : ℕ) :
    P.kDiv l = l + P.σ + 1 := by
  unfold LkPar.kDiv
  rw [List.countP_eq_length.mpr fun t _ => by simp [LkPar.kf, h t], List.length_range]

/-- The number of the coordinates of the end point z of the key side that are rejected at 0. -/
def LkPar.nZ {E : Type} (P : LkPar E) : ℕ := (List.range (P.D + P.σ)).countP P.zf

/-- The layers of the key side together: all challenges of all layers but the last, and the checked
coordinates of z (under `hD`). -/
theorem LkPar.sum_kDiv {E : Type} (P : LkPar E) (hD : 0 < P.D) :
    ∑ i ∈ range P.D, P.kDiv i = ∑ i ∈ range (P.D - 1), (i + P.σ + 1) + P.nZ := by
  obtain ⟨D', hD'⟩ : ∃ D', P.D = D' + 1 := ⟨P.D - 1, by omega⟩
  rw [hD', Nat.add_sub_cancel, sum_range_succ]
  congr 1
  · exact sum_congr rfl fun i hi => P.kDiv_of_lt (by rw [hD']; have := mem_range.mp hi; omega)
  · unfold LkPar.kDiv LkPar.nZ
    rw [hD', show D' + P.σ + 1 = D' + 1 + P.σ by omega]
    refine List.countP_congr fun t _ => ?_
    rw [← hD', P.kf_top]

/-- The number of dividing coordinates of a lookup argument. -/
def LkPar.ndiv {E : Type} (P : LkPar E) : ℕ :=
  P.σ + (∑ i ∈ range P.D, P.kDiv i) + (P.σ + P.lp) +
    (∑ i ∈ range P.r, (i + (P.σ + P.lp) + 1)) + P.gT + P.σ

/-- If every coordinate of z is checked: layer l of the key side counts its l + σ + 1 challenges. -/
theorem LkPar.ndiv_of_all {E : Type} (P : LkPar E) (h : ∀ t, P.zf t = true) :
    P.ndiv = P.σ + (∑ i ∈ range P.D, (i + P.σ + 1)) + (P.σ + P.lp) +
        (∑ i ∈ range P.r, (i + (P.σ + P.lp) + 1)) + P.gT + P.σ := by
  unfold LkPar.ndiv
  rw [sum_congr rfl fun i _ => P.kDiv_of_all h i]

namespace Lk

variable {E Y Pd N : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] [Fintype Pd] [DecidableEq Pd] (L : Lk E Y Pd N)

theorem stKey_pBad :
    ∀ n l : ℕ,
      (L.stKey n l).pBad = ((∑ i ∈ range n, L.par.kDiv (l + i) : ℕ) : ℝ≥0∞) / Fintype.card E
  | 0, _ => by
    show (0 : ℝ≥0∞) = _
    simp
  | n + 1, l => by
    show PL.Prover.pBad (L.plK l) + (L.stKey n (l + 1)).pBad = _
    rw [stKey_pBad n (l + 1), sum_range_succ']
    show ((L.par.kDiv l : ℕ) : ℝ≥0∞) / Fintype.card E + _ = _
    rw [ENNReal.div_add_div_same]
    congr 1
    have e : ∑ i ∈ range n, L.par.kDiv (l + 1 + i) = ∑ i ∈ range n, L.par.kDiv (l + (i + 1)) :=
      sum_congr rfl fun i _ => by rw [show l + 1 + i = l + (i + 1) by omega]
    rw [e, Nat.add_zero]
    push_cast
    ring

theorem stTab_pBad :
    ∀ n l : ℕ, (L.stTab n l).pBad =
      ((∑ i ∈ range n, (l + i + (L.par.σ + L.par.lp) + 1) : ℕ) : ℝ≥0∞) / Fintype.card E
  | 0, _ => by
    show (0 : ℝ≥0∞) = _
    simp
  | n + 1, l => by
    show PL.Prover.pBad (L.plT l) + (L.stTab n (l + 1)).pBad = _
    rw [stTab_pBad n (l + 1), sum_range_succ', PL.Prover.pBad_of_all fun _ => rfl]
    show (((l + (L.par.σ + L.par.lp) : ℕ) : ℝ≥0∞) + 1) / Fintype.card E + _ = _
    rw [ENNReal.div_add_div_same]
    congr 1
    have e : ∑ i ∈ range n, (l + 1 + i + (L.par.σ + L.par.lp) + 1) =
        ∑ i ∈ range n, (l + (i + 1) + (L.par.σ + L.par.lp) + 1) :=
      sum_congr rfl fun i _ => by omega
    rw [e]
    push_cast
    ring

theorem stKey_pWin : ∀ n l : ℕ, (L.stKey n l).pWin = 0
  | 0, _ => rfl
  | n + 1, l => by
    show (0 : ℝ≥0∞) + (L.stKey n (l + 1)).pWin = 0
    rw [stKey_pWin n (l + 1), add_zero]

theorem stTab_pWin : ∀ n l : ℕ, (L.stTab n l).pWin = 0
  | 0, _ => rfl
  | n + 1, l => by
    show (0 : ℝ≥0∞) + (L.stTab n (l + 1)).pWin = 0
    rw [stTab_pWin n (l + 1), add_zero]

/-- The bound `pBad` of the lookup argument, for the public part of its withheld set, is ndiv /
|E|. -/
theorem stLookup_pBad : L.stLookup.pBad = (L.par.ndiv : ℝ≥0∞) / Fintype.card E := by
  have e14 : L.st14.pBad =
      0 + (pPt E L.par.σ +
          ((L.stKey L.par.D 0).pBad +
            (0 + (pPt E (L.par.σ + L.par.lp) +
                ((L.stTab L.par.r 0).pBad + (0 + (pPt E L.par.gT + 0))))))) := rfl
  have e6 : L.st6.pBad = pPt E L.par.σ + (0 + (0 + 0)) := rfl
  have e : L.stLookup.pBad = L.st14.pBad + (0 + L.st6.pBad) := rfl
  rw [e, e14, e6, stKey_pBad, stTab_pBad, pPt_eq, pPt_eq, pPt_eq]
  simp only [zero_add, add_zero, ENNReal.div_add_div_same]
  congr 1
  unfold LkPar.ndiv
  push_cast
  ring

/-- The bound `pWin` of the lookup argument is 0. -/
theorem stLookup_pWin : L.stLookup.pWin = 0 := by
  have e14 : L.st14.pWin =
      0 +
        (0 + ((L.stKey L.par.D 0).pWin + (0 + (0 + ((L.stTab L.par.r 0).pWin + (0 + (0 + 0))))))) :=
    rfl
  have e6 : L.st6.pWin = 0 + (0 + (0 + 0)) := rfl
  have e : L.stLookup.pWin = L.st14.pWin + (0 + L.st6.pWin) := rfl
  rw [e, e14, e6, stKey_pWin, stTab_pWin]
  simp

end Lk

end Blocks
