-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicyCells.lean: the honest values of the cells that hold the policy's numbers, at
every pair (token v, position t), and the keys that they meet.

Integers only. This is what the honest trace of the head needs for the hidden numbers: the values to
be written into the arrays d1, d2, ex and into the ledger's bytes 99 to 119, their ranges, and the
keys (looked-up values) that they meet. All this is needed at every position and token,
not only at the covered ones, since the lookups cover every pair. (Real pair: t covered, v < V.)
  `mgP`                    the margin with both masks: ρ_t (lg_t[w_t] − lg_t[v] − [v < w_t]) + ρC_t
                           (c_t + 2^37 b_t); `mgP_cov`: at a covered position it is `marg`;
                           `mgP_off`: 0 at every other, whatever the numbers
  `pd1`, `pd2`, `pex`        the values of the arrays: d1 = K_1 − 32,896 and d2 = K_2 − 128 at a
                           real pair, 0 at every other; ex = EX[K_1] at a real pair, 2^24 at every
                           other
  `pd1_range`, `pd2_range`, `pex_range`
                           −32,896 ≤ d1 ≤ 32,639; −128 ≤ d2 ≤ 127 (these two under `PolOK`, `Fit`);
                           1 ≤ ex ≤ 2^24 (always): within what two cells, one cell, three cells with
                           the offset 8,421,505 can hold
  `key_top`, `key_mid`, `key_low`, `key_ex`
                           under `PolOK`, `Fit`, at every position: margin − 2^8 K_1 − K_2 = 2^23
                           K_0 (for v < V) with K_0, K_1 in [0, 2^16), K_2 in [0, 2^8), and K_1 +
                           2^16 ex is row K_1 of the table FE (the last three at every v)
Outside the policy the middle digit can be negative, so d1 can be below −32,896 and two cells do not
hold it: whoever builds a trace from these values needs `PolOK`. `pd1_K1`, `pd2_K2` (for v < V),
`pex_range`, `phr_le`, `phr_byte`, `mgP_cov`, `mgP_off` need neither `PolOK` nor `Fit`.
The masks are on positions, where the implementation's are on pairs ([real]; [v < V] ρC_t): at a
covered position and a token v ≥ V the implementation's key is 0 and `mgP` is not. At the reference
sizes there is no such pair (JV = V); sizes with JV > V would need the mask on v. The size bounds
assumed here are `Fit` (Inst/Model/Head/PolicyDefs.lean), as in `HRel_of_HCong` of
Policy/Rel/LedgerHeadNoWrap.lean, which assumes T ≤ 2^10 besides.

Limits. No trace, no field relation, no affine form of the protocol is defined or met here: the file
gives the numbers and their arithmetic, for a trace whose margin contains the hidden number. Tokens
v ≥ V have no cell in this folder's head (its arrays have exactly V features); `pd1`, `pd2` are 0
and `pex` is 2^24 there.
(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.PolicyNoWrap
import Inst.Model.Head.PolicyBytes

set_option autoImplicit false

namespace Inst.Model.Head.Policy

open Inst.Model Finset

/-! ## The values at every pair -/

section
variable {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P)

/-- the margin with both masks -/
def mgP (h : Hid) (t v : ℕ) : ℤ :=
  rhoR x t * (lg t (x.w t) - lg t v - if v < x.w t then 1 else 0) +
    rhoC x t * (h.c t + 2 ^ 37 * h.b t)

/-- the values of the arrays d1, d2, ex -/
def pd1 (t v : ℕ) : ℤ :=
  if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then (Honest.honD lg pol x).K1 v t - 32896 else 0
def pd2 (t v : ℕ) : ℤ :=
  if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then (Honest.honD lg pol x).K2 v t - 128 else 0
def pex (t v : ℕ) : ℤ := (Honest.honD lg pol x).ex v t
/-- the cell of ledger byte n, for n ≥ 99 -/
def phr (n t : ℕ) : ℤ := hidByte (Honest.honH lg pol x) n t - 128

variable {lg pol x}

theorem mgP_cov (h : Hid) {t : ℕ} (hr : x.r ≤ t) (he : t < x.e) (v : ℕ) :
    mgP lg x h t v = marg lg x h t v := by
  unfold mgP marg rhoR
  rw [if_pos ⟨hr, he⟩]
  ring

theorem mgP_off {t : ℕ} (h : ¬ (x.r ≤ t ∧ t < x.e)) (g : Hid) (v : ℕ) : mgP lg x g t v = 0 := by
  have hc : t ∉ x.cnt := fun h' => h (cnt_covered h')
  unfold mgP rhoR rhoC
  rw [if_neg h, if_neg hc]
  ring

theorem pd1_K1 (t : ℕ) {v : ℕ} (hv : v < P.V) :
    pd1 lg pol x t v + 32896 * rhoR x t = (Honest.honD lg pol x).K1 v t := by
  unfold pd1 rhoR
  by_cases h : x.r ≤ t ∧ t < x.e
  · rw [if_pos ⟨h, hv⟩, if_pos h]; ring
  · rw [if_neg fun h' => h h'.1, if_neg h, (Honest.honest_offD fun h' => h h'.1).2.1]; ring

theorem pd2_K2 (t : ℕ) {v : ℕ} (hv : v < P.V) :
    pd2 lg pol x t v + 128 * rhoR x t = (Honest.honD lg pol x).K2 v t := by
  unfold pd2 rhoR
  by_cases h : x.r ≤ t ∧ t < x.e
  · rw [if_pos ⟨h, hv⟩, if_pos h]; ring
  · rw [if_neg fun h' => h h'.1, if_neg h, (Honest.honest_offD fun h' => h h'.1).2.2.1]; ring

theorem phr_byte (n t : ℕ) : 128 + phr lg pol x n t = hidByte (Honest.honH lg pol x) n t := by
  unfold phr; ring

theorem phr_le (n t : ℕ) : |phr lg pol x n t| ≤ 128 := by
  have := hidByte_bounds (Honest.honH lg pol x) n t
  unfold phr
  rw [abs_le]
  constructor <;> omega

theorem pex_range (t v : ℕ) : 1 ≤ pex lg pol x t v ∧ pex lg pol x t v ≤ 2 ^ 24 := by
  show 1 ≤ (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then
          EX (Honest.dK1 (marg lg x (Honest.pre lg pol x) t v)).toNat
        else 2 ^ 24) ∧
    (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then
          EX (Honest.dK1 (marg lg x (Honest.pre lg pol x) t v)).toNat
        else 2 ^ 24) ≤ 2 ^ 24
  split_ifs
  · exact TablesSanity.tab9.2 _
  · norm_num

section Keys
variable (hp : PolOK lg pol x) (hf : Fit P lg pol)
include hp hf

/-- under `PolOK` and `Fit`, at every pair (v, t): K_0 and K_1 are in [0, 2^16), K_2 is in [0, 2^8)
-/
theorem dig_all (t v : ℕ) :
    (0 ≤ (Honest.honD lg pol x).K0 v t ∧ (Honest.honD lg pol x).K0 v t < 2 ^ 16) ∧
    (0 ≤ (Honest.honD lg pol x).K1 v t ∧ (Honest.honD lg pol x).K1 v t < 2 ^ 16) ∧
    (0 ≤ (Honest.honD lg pol x).K2 v t ∧ (Honest.honD lg pol x).K2 v t < 2 ^ 8) := by
  by_cases h : (x.r ≤ t ∧ t < x.e) ∧ v < P.V
  · exact ((Honest.honest_rel hp hf).B1 t h.1.1 h.1.2 v h.2).2
  · obtain ⟨e0, e1, e2, -⟩ := Honest.honest_offD (lg := lg) (pol := pol) h
    rw [e0, e1, e2]
    norm_num

theorem key_mid (t v : ℕ) :
    0 ≤ (Honest.honD lg pol x).K1 v t ∧ (Honest.honD lg pol x).K1 v t < 2 ^ 16 :=
  (dig_all hp hf t v).2.1
theorem key_low (t v : ℕ) :
    0 ≤ (Honest.honD lg pol x).K2 v t ∧ (Honest.honD lg pol x).K2 v t < 2 ^ 8 :=
  (dig_all hp hf t v).2.2

/-- the key of the top digit, under `PolOK`, `Fit`, at every position, for v < V: margin − 2^8 K_1 −
K_2 = 2^23 K_0, with K_0 in [0, 2^16) -/
theorem key_top (t : ℕ) {v : ℕ} (hv : v < P.V) :
    mgP lg x (Honest.honH lg pol x) t v -
        2 ^ 8 * (Honest.honD lg pol x).K1 v t - (Honest.honD lg pol x).K2 v t =
      2 ^ 23 * (Honest.honD lg pol x).K0 v t ∧
    0 ≤ (Honest.honD lg pol x).K0 v t ∧
    (Honest.honD lg pol x).K0 v t < 2 ^ 16 := by
  refine ⟨?_, (dig_all hp hf t v).1⟩
  by_cases h : x.r ≤ t ∧ t < x.e
  · rw [mgP_cov _ h.1 h.2]
    have := ((Honest.honest_rel hp hf).B1 t h.1 h.2 v hv).1
    omega
  · obtain ⟨e0, e1, e2, -⟩ :=
      Honest.honest_offD (lg := lg) (pol := pol) (x := x) (t := t) (v := v) fun h' => h h'.1
    rw [mgP_off h, e0, e1, e2]
    norm_num

/-- under `PolOK`, `Fit`: the key of EX, at every pair: K_1 + 2^16 ex is row K_1 of FE -/
theorem key_ex (t v : ℕ) :
    ((Honest.honD lg pol x).K1 v t).toNat < 2 ^ 16 ∧
    (Honest.honD lg pol x).K1 v t + 2 ^ 16 * pex lg pol x t v =
      FE.row ((Honest.honD lg pol x).K1 v t).toNat := by
  obtain ⟨k0, k1⟩ := key_mid hp hf t v
  refine ⟨by omega, ?_⟩
  show _ = ((((Honest.honD lg pol x).K1 v t).toNat : ℕ) : ℤ) +
      2 ^ 16 * EX ((Honest.honD lg pol x).K1 v t).toNat
  rw [Int.toNat_of_nonneg k0]
  by_cases h : (x.r ≤ t ∧ t < x.e) ∧ v < P.V
  · unfold pex
    rw [(Honest.honest_rel hp hf).HE t h.1.1 h.1.2 v h.2]
  · obtain ⟨-, e1, -, e3⟩ := Honest.honest_offD (lg := lg) (pol := pol) h
    unfold pex
    rw [e3, e1, Int.toNat_zero, TablesSanity.tab9.1]

theorem pd1_range (t v : ℕ) : -32896 ≤ pd1 lg pol x t v ∧ pd1 lg pol x t v ≤ 32639 := by
  have := key_mid hp hf t v
  unfold pd1
  split_ifs <;> omega

theorem pd2_range (t v : ℕ) : -128 ≤ pd2 lg pol x t v ∧ pd2 lg pol x t v ≤ 127 := by
  have := key_low hp hf t v
  unfold pd2
  split_ifs <;> omega

end Keys

end

end Inst.Model.Head.Policy
