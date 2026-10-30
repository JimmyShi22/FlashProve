-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicyHonTrace.lean: the honest cells of the head, those of the hidden numbers
included.

These are the honest cells of Inst/Model/Head/HonestBase.lean, with the cells that hold the policy's
numbers written by the honest prover's rule (Inst/Model/Head/PolicyHonest.lean,
Inst/Model/Head/PolicyCells.lean): the arrays d1, d2, ex from the digits of the margin with the
hidden number, the ledger's bytes 99 to 119 from the six hidden numbers.
  `honCellsP np X H pol x`        the cells: x, hd, the first 20,480 features of hf (nw, rn) and the
                                  ledger's bytes below 99 are those of `N.honBase`; the rest is new
  `lgv_abs'`, `fit_lgv`           the logits' bound from |H| ≤ 2^12 only; `Fit` at the reference
                                  sizes, if also C, θ < 2^40 and cap < 2^16

Notation:
  `cellW n a l` (Inst/Model/Widened.lean): an integer: the widened cell rule: cell l of the value a
    in an array of n cells: balanced low bytes, and the rest in the top cell.
Limits. That these cells meet a field relation of the head is not said here: `hon_rfz`,
Policy/Rel/LedgerHeadHonest.lean, says it of `RFz p` (Policy/Rel/LedgerHeadInt.lean), and rests on
this file. Nothing is said on the cells that are taken over (Inst/Model/Head/HonestBase.lean is
about them, under its own hypotheses), but for `honP_lg` (the array lg, read from hd) and
`honP_idle`. Nothing is said on the protocol.
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.Head.HonestBase
import Inst.Model.Head.PolicyHonCells

set_option autoImplicit false

namespace Inst.Model.Head.N

open Finset Inst.Model.Head.Policy

section
variable (np : NormPar) (X : ℕ → Vec) (H : Mat) (pol : AcceptancePolicy) (x : Instance ppref)

/-- The honest cells, those of the hidden numbers included. -/
def honCellsP : Cells ℤ where
  x := (honBase np X H (Req.of pol x)).x
  hd := (honBase np X H (Req.of pol x)).hd
  hr := fun n i =>
    if n < 99 then (honBase np X H (Req.of pol x)).hr n i else phr (lgv np X H) pol x n i
  hf := fun φ i =>
    if φ < 20480 then (honBase np X H (Req.of pol x)).hf φ i
    else if φ < 424576 then
      cellW 2 (pd1 (lgv np X H) pol x i ((φ - 20480) % 202048)) ((φ - 20480) / 202048)
    else if φ < 626624 then pd2 (lgv np X H) pol x i (φ - 424576)
    else if φ < 1232768 then
      cellW 3 (pex (lgv np X H) pol x i ((φ - 626624) % 202048) - 8421505) ((φ - 626624) / 202048)
    else 0

theorem honP_d1 {v : ℕ} (hv : v < nV) (i : ℕ) :
    d1 (honCellsP np X H pol x) v i = pd1 (lgv np X H) pol x i v := by
  refine rd_cellW (by norm_num) _ _ fun l hl => ?_
  show (honCellsP np X H pol x).hf (20480 + 202048 * l + v) i = _
  unfold nV at hv
  simp only [honCellsP]
  rw [if_neg (by omega), if_pos (by omega),
    show (20480 + 202048 * l + v - 20480) % 202048 = v by omega,
    show (20480 + 202048 * l + v - 20480) / 202048 = l by omega]

theorem honP_d2 {v : ℕ} (hv : v < nV) (i : ℕ) :
    d2 (honCellsP np X H pol x) v i = pd2 (lgv np X H) pol x i v := by
  show (honCellsP np X H pol x).hf (424576 + v) i = _
  unfold nV at hv
  simp only [honCellsP]
  rw [if_neg (by omega), if_neg (by omega),
    if_pos (by omega), show 424576 + v - 424576 = v by omega]

theorem honP_ex {v : ℕ} (hv : v < nV) (i : ℕ) :
    ex (honCellsP np X H pol x) v i = pex (lgv np X H) pol x i v := by
  have : rd 3 (fun l => (honCellsP np X H pol x).hf (fEx l v) i) =
      pex (lgv np X H) pol x i v - 8421505 := by
    refine rd_cellW (by norm_num) _ _ fun l hl => ?_
    show (honCellsP np X H pol x).hf (626624 + 202048 * l + v) i = _
    unfold nV at hv
    simp only [honCellsP]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show (626624 + 202048 * l + v - 626624) % 202048 = v by omega,
      show (626624 + 202048 * l + v - 626624) / 202048 = l by omega]
  unfold ex
  rw [this]
  ring

theorem honP_hr {n : ℕ} (hn : 99 ≤ n) (i : ℕ) :
    (honCellsP np X H pol x).hr n i = phr (lgv np X H) pol x n i :=
  if_neg (by omega)

/-- the cells hold the honest values of the policy -/
theorem honP_holds : HoldsPolicy (lgv np X H) pol x (honCellsP np X H pol x) where
  hr := fun _ i hn _ => honP_hr np X H pol x hn i
  d1 := fun i _ hv => honP_d1 np X H pol x hv i
  d2 := fun i _ hv => honP_d2 np X H pol x hv i
  ex := fun i _ hv => honP_ex np X H pol x hv i

/-- the array lg of these cells is the logits of the residual stream X -/
theorem honP_lg (i v : ℕ) : lg (honCellsP np X H pol x) H i v = lgv np X H i v :=
  sum_congr rfl fun j hj => by
    rw [show nrm (honCellsP np X H pol x) j i = nrm (honBase np X H (Req.of pol x)) j i from rfl,
      hon_nrm np X H (Req.of pol x) (mem_range.1 hj) i]

variable {np X H pol x}

theorem lgv_abs' (hH : ∀ j v, |H j v| ≤ 2 ^ 12) (i v : ℕ) : |lgv np X H i v| ≤ 42928701440 := by
  unfold lgv
  calc
    |∑ j ∈ range nD,
      outv np X i j * H j v| ≤ ∑ j ∈ range nD, |outv np X i j * H j v| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range nD, (2047 * 2 ^ 12 : ℤ) := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_le.2 (out_abs i j)) (hH j v) (abs_nonneg _) (by norm_num)
    _ = 42928701440 := by simp [nD]

theorem fit_lgv (hH : ∀ j v, |H j v| ≤ 2 ^ 12) (hC : pol.C < 2 ^ 40)
    (hθ : pol.theta < 2 ^ 40) (hcap : pol.cap < 2 ^ 16) : Fit ppref (lgv np X H) pol :=
  ⟨fun t _ v _ => le_trans (lgv_abs' hH t v) (by norm_num), hC, hθ, hcap, by norm_num [ppref]⟩

/-- under `PolOK` and `Fit`: every new cell has absolute value at most 128 -/
theorem honP_le (hp : PolOK (lgv np X H) pol x) (hf : Fit ppref (lgv np X H) pol) (i : ℕ) :
    (∀ φ, 20480 ≤ φ → |(honCellsP np X H pol x).hf φ i| ≤ 128) ∧
    ∀ n, 99 ≤ n → |(honCellsP np X H pol x).hr n i| ≤ 128 := by
  obtain ⟨u1, u2, u3⟩ := un_vals
  refine ⟨fun φ hφ => ?_, fun n hn => by rw [honP_hr np X H pol x hn i]; exact phr_le n i⟩
  simp only [honCellsP]
  rw [if_neg (by omega)]
  split_ifs with c3 c4 c5
  · refine (writable_iff (n := 2) (by norm_num) _).2 ?_ _ (by omega)
    have := pd1_range hp hf i ((φ - 20480) % 202048)
    simp only [u2, u1, Nat.reduceSub]
    constructor <;> omega
  · have := pd2_range hp hf i (φ - 424576)
    rw [abs_le]
    constructor <;> omega
  · refine (writable_iff (n := 3) (by norm_num) _).2 ?_ _ (by omega)
    have := pex_range (lg := lgv np X H) (pol := pol) (x := x) i ((φ - 626624) % 202048)
    simp only [u3, u2, Nat.reduceSub]
    constructor <;> omega
  · norm_num

end

/-! ## Sanity lemma: without a counted position these are the cells `honBase` -/

section Idle
variable (np : NormPar) (X : ℕ → Vec) (H : Mat) (pol : AcceptancePolicy) (x : Instance ppref)

theorem marg_idle (hc : x.cnt = ∅) (t v : ℕ) :
    marg (lgv np X H) x (Honest.pre (lgv np X H) pol x) t v = mgv np X H (Req.of pol x) t v := by
  simp [marg, rhoC, hc, mgv, Req.of]

theorem pd1_idle (hc : x.cnt = ∅) (i : ℕ) {v : ℕ} (hv : v < 202048) :
    pd1 (lgv np X H) pol x i v = d1v np X H (Req.of pol x) i v := by
  have hv' : v < ppref.V := hv
  simp only [pd1, d1v, Honest.honD, marg_idle np X H pol x hc, K1v, mhv, Honest.dK1,
    Honest.ix, Req.of, hv', and_true]
  split_ifs <;> rfl

theorem pd2_idle (hc : x.cnt = ∅) (i : ℕ) {v : ℕ} (hv : v < 202048) :
    pd2 (lgv np X H) pol x i v = d2v np X H (Req.of pol x) i v := by
  have hv' : v < ppref.V := hv
  simp only [pd2, d2v, Honest.honD, marg_idle np X H pol x hc, K2v,
    Honest.dK2, Req.of, hv', and_true]
  split_ifs <;> rfl

theorem pex_idle (hc : x.cnt = ∅) (i : ℕ) {v : ℕ} (hv : v < 202048) :
    pex (lgv np X H) pol x i v = exv np X H (Req.of pol x) i v := by
  have hv' : v < ppref.V := hv
  simp only [pex, exv, Honest.honD, marg_idle np X H pol x hc, K1v, mhv, Honest.dK1,
    Honest.ix, Req.of, hv', and_true]

/-- where no position is counted, the cells with the hidden numbers (`honCellsP`) are `honBase` -/
theorem honP_idle (hc : x.cnt = ∅) : honCellsP np X H pol x = honBase np X H (Req.of pol x) := by
  have e : ∀ (a b : Cells ℤ), a.hf = b.hf → a.hd = b.hd → a.hr = b.hr → a.x = b.x → a = b := by
    rintro ⟨⟩ ⟨⟩ h1 h2 h3 h4
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  refine e _ _ (funext fun φ => funext fun i => ?_) rfl (funext fun n => funext fun i => ?_) rfl
  · simp only [honCellsP, honBase]
    by_cases c1 : φ < 20480
    · simp only [if_pos c1]
    · have c0 : ¬ φ < 10240 := by omega
      simp only [if_neg c1, if_neg c0]
      by_cases c2 : φ < 424576
      · simp only [if_pos c2]
        rw [pd1_idle np X H pol x hc i (Nat.mod_lt _ (by norm_num))]
      · simp only [if_neg c2]
        by_cases c3 : φ < 626624
        · simp only [if_pos c3]
          rw [pd2_idle np X H pol x hc i (by omega)]
        · simp only [if_neg c3]
          by_cases c4 : φ < 1232768
          · simp only [if_pos c4]
            rw [pex_idle np X H pol x hc i (Nat.mod_lt _ (by norm_num))]
          · simp only [if_neg c4]
  · simp only [honCellsP, honBase]
    by_cases c1 : n < 99
    · rw [if_pos c1, if_pos c1]
    · rw [if_neg c1, if_neg c1]
      unfold phr
      rw [honByte_off (by rw [hc]; exact notMem_empty i)]
      norm_num

end Idle

end Inst.Model.Head.N
