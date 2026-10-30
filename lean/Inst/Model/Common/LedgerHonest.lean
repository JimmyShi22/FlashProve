-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/LedgerHonest.lean: the honest ledger of a normalisation.

The definitions (row values, multipliers, W_s, the 17 identities) are those of
Inst/Model/Common/Ledger.lean. Everything here is integer arithmetic for one normalisation at one
position, generic in d, M, ϵ.
  `rowDigits`          the 99 bytes from the numbers that they encode; `rowDigits_spec`: for numbers
                       within their ranges they are in range and encode these numbers
  `carry`              the honest carries, by an explicit formula; `carry_ok`
  `root_ok`, `recip_ok`  under the hypotheses of their statements the numbers of the square root and
                       of the reciprocal are in the ranges of their bytes and satisfy the identities
                       that do not hold by definition
  `hon np d b`         the honest ledger: the bytes as values, in [0, 255] under `HonHyp` (the cell
                       of byte n is the value − 128), from the cells b of the input and V, ς, R of
                       the model's `NORM`
  `HonHyp`             the hypotheses: 1 ≤ ϵ < 2^48, M ≤ 47, d ≤ 2^16, every cell of the input at
                       most 128 in absolute value, and the model's range condition V + ϵ < 2^78
  `hon_typed`, .., `hon_R`
      under `HonHyp`: every key (looked-up value) µ_n D_n of the family ROW is a byte (`Typed`,
      Inst/Model/Common/LedgerSound.lean); every cell is a signed byte; the 17 identities hold over
      the integers; ς, R, V are the model's
`hon` is written as a term, from /, %, sums and the model's `NORM.V`, `NORM.sig`, `NORM.R`; no
existence statement is unpacked in it. (That its value uses no Classical.choice is not checked in
this library.)
Notation (Inst/Model/Common/Ledger.lean, unless another file is named):
  `D`: a map from the number of a byte to its value: "A ledger is here the function D from the
    number of a byte to its value".
  `Vlo`, `Vhi`, `cs`, `sa`, `s0`, `sb`, `sig`, `l1`, `h1`, `Blo`, `Bhi`, `kc`, `Rlo`, `Rhi`, `R`,
    `q1`, `rr`, `rq` (the row values): numbers read from bytes of D; the doc comments there tell the
    bytes.
  `Wsum d b s` (W_s): "W_s = Σ_j Σ_{l + l' = s} b_l[j] b_l'[j], for the five cells b_0..b_4 of the d
    values x[j]"; so b: first the cell l < 5, then j < d; `xOf b j`: "the value that the five cells
    b_0[j], .., b_4[j] represent" (Inst/Model/Common/LedgerSound.lean).
  `mu n` (µ_n): "The multiplier µ_n of byte n in the keys (looked-up values) µ_n D_n of the family
    ROW".
  (J1) to (J9): `idn`: "The 17 identities, each as "left side minus right side": number k < 9 is
    (J1) for s = k; 9..16 are (J2) to (J9)."
  `np`: a `NormPar`, "exponent of the reciprocal; shift; constant" of a normalisation: its fields M,
    K, eps; ϵ is eps; (N1): "(N1) V = Σ_j x[j]²" (`NORM.V`, Inst/Model/Program.lean).
-/
import Inst.Model.Common.LedgerSound
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace Inst.Model.Ledger

open Finset

/-! ## 1. Bytes from numbers -/

/-- Byte j of N, low byte first. -/
def byteAt (N : ℤ) (j : ℕ) : ℤ := N / 256 ^ j % 256

theorem byteAt_bounds (N : ℤ) (j : ℕ) : 0 ≤ byteAt N j ∧ byteAt N j ≤ 255 := by
  unfold byteAt
  constructor
  · exact Int.emod_nonneg _ (by norm_num)
  · have := Int.emod_lt_of_pos (N / 256 ^ j) (show (0 : ℤ) < 256 by norm_num)
    omega

/-- The 99 bytes of a ledger from its numbers. Bytes 0 to 9 hold V. Bytes 10 to 57 hold the carries
c_1 to c_8, six bytes each, after 2^47 has been added. Bytes 58 to 63 hold ς, whose low byte is
split into its upper seven bits (byte 58) and its parity (byte 59). Then l1 from 64, h1 from 69, Blo
from 74, Bhi from 77, kc + 4 at 79, Rlo from 80, Rhi from 83, q1 from 86, rr from 89, rq from 94. -/
def rowDigits (Vn : ℤ) (cr : ℕ → ℤ) (sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn : ℤ) (idx : ℕ) :
    ℤ :=
  if idx < 10 then byteAt Vn idx
  else if idx < 58 then byteAt (cr ((idx - 10) / 6 + 1) + 2 ^ 47) ((idx - 10) % 6)
  else if idx = 58 then sg % 256 / 2
  else if idx = 59 then sg % 2
  else if idx < 64 then byteAt sg (idx - 59)
  else if idx < 69 then byteAt l1n (idx - 64)
  else if idx < 74 then byteAt h1n (idx - 69)
  else if idx < 77 then byteAt Blon (idx - 74)
  else if idx < 79 then byteAt Bhin (idx - 77)
  else if idx = 79 then kap + 4
  else if idx < 83 then byteAt Rlon (idx - 80)
  else if idx < 86 then byteAt Rhin (idx - 83)
  else if idx < 89 then byteAt q1n (idx - 86)
  else if idx < 94 then byteAt rrn (idx - 89)
  else byteAt rqn (idx - 94)

section Eval
variable (Vn : ℤ) (cr : ℕ → ℤ) (sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn : ℤ)

local notation "DD" => rowDigits Vn cr sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn

theorem rd_V {j : ℕ} (h : j < 10) : DD j = byteAt Vn j := by
  unfold rowDigits; rw [if_pos h]
theorem rd_c {s j : ℕ} (h1 : 1 ≤ s) (h8 : s ≤ 8) (h : j < 6) :
    DD (10 + 6 * (s - 1) + j) = byteAt (cr s + 2 ^ 47) j := by
  unfold rowDigits
  rw [if_neg (by omega), if_pos (by omega)]
  have e1 : (10 + 6 * (s - 1) + j - 10) / 6 + 1 = s := by omega
  have e2 : (10 + 6 * (s - 1) + j - 10) % 6 = j := by omega
  rw [e1, e2]
theorem rd_58 : DD 58 = sg % 256 / 2 := by unfold rowDigits; rfl
theorem rd_59 : DD 59 = sg % 2 := by unfold rowDigits; rfl
theorem rd_s {j : ℕ} (h1 : 1 ≤ j) (h : j < 5) : DD (59 + j) = byteAt sg j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_l1 {j : ℕ} (h : j < 5) : DD (64 + j) = byteAt l1n j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_h1 {j : ℕ} (h : j < 5) : DD (69 + j) = byteAt h1n j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_Blo {j : ℕ} (h : j < 3) : DD (74 + j) = byteAt Blon j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_Bhi {j : ℕ} (h : j < 2) : DD (77 + j) = byteAt Bhin j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_79 : DD 79 = kap + 4 := by unfold rowDigits; rfl
theorem rd_Rlo {j : ℕ} (h : j < 3) : DD (80 + j) = byteAt Rlon j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_Rhi {j : ℕ} (h : j < 3) : DD (83 + j) = byteAt Rhin j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_q1 {j : ℕ} (h : j < 3) : DD (86 + j) = byteAt q1n j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_rr {j : ℕ} (h : j < 5) : DD (89 + j) = byteAt rrn j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
theorem rd_rq (j : ℕ) : DD (94 + j) = byteAt rqn j := by
  unfold rowDigits
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

end Eval

/-- The n low bytes of N hold N modulo 256^n. -/
theorem sum_byteAt (N : ℤ) (n : ℕ) : ∑ j ∈ range n, 256 ^ j * byteAt N j = N % 256 ^ n := by
  induction n with
  | zero => simp [Int.emod_one]
  | succ n ih =>
    rw [sum_range_succ, ih]
    unfold byteAt
    rw [pow_succ]
    have ha : (0 : ℤ) < 256 ^ n := by positivity
    generalize (256 : ℤ) ^ n = a at ha
    have h1 := Int.emod_add_mul_ediv N a
    have h2 := Int.emod_add_mul_ediv (N / a) 256
    have hr0 := Int.emod_nonneg N ha.ne'
    have hr1 := Int.emod_lt_of_pos N ha
    have hq0 := Int.emod_nonneg (N / a) (show (256 : ℤ) ≠ 0 by norm_num)
    have hq1 := Int.emod_lt_of_pos (N / a) (show (0 : ℤ) < 256 by norm_num)
    have key : N = (N % a + a * (N / a % 256)) + (a * 256) * (N / a / 256) := by
      linear_combination (-1 : ℤ) * h1 - a * h2
    symm
    conv_lhs => rw [key]
    rw [Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by positivity) (by nlinarith)

/-- n bytes that are the bytes of N hold N modulo 256^n. -/
theorem b256_of_bytes {D : ℕ → ℤ} {a n : ℕ} {N : ℤ} (h : ∀ j < n, D (a + j) = byteAt N j) :
    b256 D a n = N % 256 ^ n := by
  unfold b256
  rw [sum_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]]
  exact sum_byteAt N n

theorem b256_of_bytes_lt {D : ℕ → ℤ} {a n : ℕ} {N : ℤ} (h : ∀ j < n, D (a + j) = byteAt N j)
    (h0 : 0 ≤ N) (h1 : N < 256 ^ n) : b256 D a n = N := by
  rw [b256_of_bytes h, Int.emod_eq_of_lt h0 h1]

/-- The bytes of N from index a on are the bytes of the quotient of N by 256^a. -/
theorem byteAt_shift (N : ℤ) (a j : ℕ) : byteAt N (a + j) = byteAt (N / 256 ^ a) j := by
  unfold byteAt
  rw [pow_add, ← Int.ediv_ediv_of_nonneg (by positivity)]

section Main
variable (Vn : ℤ) (cr : ℕ → ℤ) (sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn : ℤ)

local notation "DD" => rowDigits Vn cr sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn

/-- These bytes are in the ranges that the multipliers prescribe, if V, ς, Blo and kc are in
theirs. -/
theorem rowDigits_typed (hV : 0 ≤ Vn ∧ Vn < 2 ^ 78) (hs : 0 ≤ sg ∧ sg < 2 ^ 39)
    (hBl : 0 ≤ Blon ∧ Blon < 2 ^ 23) (hk : -4 ≤ kap ∧ kap < 4) : Typed DD := by
  intro idx hidx
  unfold mu
  split_ifs with h9 h58 h59 h63 h76 h79
  · subst h9
    rw [rd_V _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num)]
    unfold byteAt
    norm_num at hV ⊢
    omega
  · subst h58
    rw [rd_58]
    omega
  · subst h59
    rw [rd_59]
    omega
  · subst h63
    rw [show (63 : ℕ) = 59 + 4 from rfl, rd_s _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)]
    unfold byteAt
    norm_num at hs ⊢
    omega
  · subst h76
    rw [show (76 : ℕ) = 74 + 2 from rfl, rd_Blo _ _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num)]
    unfold byteAt
    norm_num at hBl ⊢
    omega
  · subst h79
    rw [rd_79]
    omega
  · rw [one_mul]
    have key : ∃ N j, DD idx = byteAt N j := by
      by_cases c1 : idx < 10
      · exact ⟨_, _, rd_V _ _ _ _ _ _ _ _ _ _ _ _ _ c1⟩
      by_cases c2 : idx < 58
      · obtain ⟨s, j, hs1, hs8, hj, rfl⟩ :
            ∃ s j, 1 ≤ s ∧ s ≤ 8 ∧ j < 6 ∧ idx = 10 + 6 * (s - 1) + j :=
          ⟨(idx - 10) / 6 + 1, (idx - 10) % 6, by omega, by omega, by omega, by omega⟩
        exact ⟨_, _, rd_c _ _ _ _ _ _ _ _ _ _ _ _ _ hs1 hs8 hj⟩
      by_cases c3 : idx < 64
      · obtain ⟨j, h1, hj, rfl⟩ : ∃ j, 1 ≤ j ∧ j < 5 ∧ idx = 59 + j :=
          ⟨idx - 59, by omega, by omega, by omega⟩
        exact ⟨_, _, rd_s _ _ _ _ _ _ _ _ _ _ _ _ _ h1 hj⟩
      by_cases c4 : idx < 69
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 5 ∧ idx = 64 + j := ⟨idx - 64, by omega, by omega⟩
        exact ⟨_, _, rd_l1 _ _ _ _ _ _ _ _ _ _ _ _ _ hj⟩
      by_cases c5 : idx < 74
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 5 ∧ idx = 69 + j := ⟨idx - 69, by omega, by omega⟩
        exact ⟨_, _, rd_h1 _ _ _ _ _ _ _ _ _ _ _ _ _ hj⟩
      by_cases c6 : idx < 77
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 3 ∧ idx = 74 + j := ⟨idx - 74, by omega, by omega⟩
        exact ⟨_, _, rd_Blo _ _ _ _ _ _ _ _ _ _ _ _ _ hj⟩
      by_cases c7 : idx < 79
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 2 ∧ idx = 77 + j := ⟨idx - 77, by omega, by omega⟩
        exact ⟨_, _, rd_Bhi _ _ _ _ _ _ _ _ _ _ _ _ _ hj⟩
      by_cases c8 : idx < 83
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 3 ∧ idx = 80 + j := ⟨idx - 80, by omega, by omega⟩
        exact ⟨_, _, rd_Rlo _ _ _ _ _ _ _ _ _ _ _ _ _ hj⟩
      by_cases c9 : idx < 86
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 3 ∧ idx = 83 + j := ⟨idx - 83, by omega, by omega⟩
        exact ⟨_, _, rd_Rhi _ _ _ _ _ _ _ _ _ _ _ _ _ hj⟩
      by_cases c10 : idx < 89
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 3 ∧ idx = 86 + j := ⟨idx - 86, by omega, by omega⟩
        exact ⟨_, _, rd_q1 _ _ _ _ _ _ _ _ _ _ _ _ _ hj⟩
      by_cases c11 : idx < 94
      · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 5 ∧ idx = 89 + j := ⟨idx - 89, by omega, by omega⟩
        exact ⟨_, _, rd_rr _ _ _ _ _ _ _ _ _ _ _ _ _ hj⟩
      · obtain ⟨j, rfl⟩ : ∃ j, idx = 94 + j := ⟨idx - 94, by omega⟩
        exact ⟨_, _, rd_rq _ _ _ _ _ _ _ _ _ _ _ _ _ j⟩
    obtain ⟨N, j, e⟩ := key
    rw [e]
    exact byteAt_bounds N j

theorem rowDigits_V (hV : 0 ≤ Vn ∧ Vn < 2 ^ 78) :
    b256 DD 0 10 = Vn ∧ Vlo DD = Vn % 2 ^ 48 ∧ Vhi DD = Vn / 2 ^ 48 := by
  refine ⟨?_, ?_, ?_⟩
  · exact b256_of_bytes_lt (fun j hj => by rw [zero_add]; exact rd_V _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hV.1 (lt_trans hV.2 (by norm_num))
  · have h := b256_of_bytes (D := DD) (a := 0) (n := 6) (N := Vn) fun j hj => by
      rw [zero_add]; exact rd_V _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)
    rw [show (256 : ℤ) ^ 6 = 2 ^ 48 by norm_num] at h
    exact h
  · have h := b256_of_bytes_lt (D := DD) (a := 6) (n := 4) (N := Vn / 256 ^ 6)
      (fun j hj => by rw [rd_V _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega), byteAt_shift])
      (Int.ediv_nonneg hV.1 (by norm_num)) (by
        have := hV.2
        norm_num at this ⊢
        omega)
    rw [show (256 : ℤ) ^ 6 = 2 ^ 48 by norm_num] at h
    exact h

theorem rowDigits_cs (hc : ∀ s, 1 ≤ s → s ≤ 8 → -2 ^ 47 ≤ cr s ∧ cr s < 2 ^ 47) (s : ℕ)
    (h1 : 1 ≤ s) (h8 : s ≤ 8) : cs DD s = cr s := by
  unfold cs
  rw [if_neg (by omega), if_neg (by omega),
    b256_of_bytes_lt (N := cr s + 2 ^ 47) (fun j hj => rd_c _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h8 hj)]
  · ring
  · have := (hc s h1 h8).1
    linarith
  · have := (hc s h1 h8).2
    norm_num at this ⊢
    linarith

theorem rowDigits_sig (hs : 0 ≤ sg ∧ sg < 2 ^ 39) :
    sig DD = sg ∧ s0 DD = sg % 2 ∧ sa DD = sg % 2 ^ 24 ∧ sb DD = sg / 2 ^ 24 := by
  have e60 : DD 60 = byteAt sg 1 :=
    rd_s _ _ _ _ _ _ _ _ _ _ _ _ _ (j := 1) (by norm_num) (by norm_num)
  have e61 : DD 61 = byteAt sg 2 :=
    rd_s _ _ _ _ _ _ _ _ _ _ _ _ _ (j := 2) (by norm_num) (by norm_num)
  have e62 : DD 62 = byteAt sg 3 :=
    rd_s _ _ _ _ _ _ _ _ _ _ _ _ _ (j := 3) (by norm_num) (by norm_num)
  have e63 : DD 63 = byteAt sg 4 :=
    rd_s _ _ _ _ _ _ _ _ _ _ _ _ _ (j := 4) (by norm_num) (by norm_num)
  have ha : sa DD = sg % 2 ^ 24 := by
    unfold sa
    rw [rd_58, rd_59, e60, e61]
    unfold byteAt
    norm_num
    omega
  have hb : sb DD = sg / 2 ^ 24 := by
    unfold sb
    rw [e62, e63]
    unfold byteAt
    have := hs.1
    have := hs.2
    norm_num at *
    omega
  refine ⟨?_, rd_59 _ _ _ _ _ _ _ _ _ _ _ _ _, ha, hb⟩
  unfold sig
  rw [ha, hb]
  norm_num
  omega

end Main


section Spec
variable (Vn : ℤ) (cr : ℕ → ℤ) (sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn : ℤ)

local notation "DD" => rowDigits Vn cr sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn

/-- The bytes hold their numbers: for all numbers within their ranges (the hypotheses) the 99 bytes
are in range and every row value is the number, or (Vlo, Vhi; s0, sa, sb) the part of the number,
from which its bytes were made (the carries: c_1 to c_8). -/
theorem rowDigits_spec (hV : 0 ≤ Vn ∧ Vn < 2 ^ 78)
    (hc : ∀ s, 1 ≤ s → s ≤ 8 → -2 ^ 47 ≤ cr s ∧ cr s < 2 ^ 47) (hs : 0 ≤ sg ∧ sg < 2 ^ 39)
    (hl : 0 ≤ l1n ∧ l1n < 2 ^ 40) (hh : 0 ≤ h1n ∧ h1n < 2 ^ 40) (hBl : 0 ≤ Blon ∧ Blon < 2 ^ 23)
    (hBh : 0 ≤ Bhin ∧ Bhin < 2 ^ 16) (hk : -4 ≤ kap ∧ kap < 4) (hRl : 0 ≤ Rlon ∧ Rlon < 2 ^ 24)
    (hRh : 0 ≤ Rhin ∧ Rhin < 2 ^ 24) (hq : 0 ≤ q1n ∧ q1n < 2 ^ 24)
    (hrr : 0 ≤ rrn ∧ rrn < 2 ^ 40) (hrq : 0 ≤ rqn ∧ rqn < 2 ^ 40) :
    Typed DD ∧ (∀ s < 10, DD s = Vn / 256 ^ s % 256) ∧ b256 DD 0 10 = Vn ∧
    Vlo DD = Vn % 2 ^ 48 ∧ Vhi DD = Vn / 2 ^ 48 ∧ (∀ s, 1 ≤ s → s ≤ 8 → cs DD s = cr s) ∧
    sig DD = sg ∧ s0 DD = sg % 2 ∧ sa DD = sg % 2 ^ 24 ∧ sb DD = sg / 2 ^ 24 ∧ l1 DD = l1n ∧
    h1 DD = h1n ∧ Blo DD = Blon ∧ Bhi DD = Bhin ∧ kc DD = kap ∧ Rlo DD = Rlon ∧ Rhi DD = Rhin ∧
    q1 DD = q1n ∧ rr DD = rrn ∧ rq DD = rqn := by
  have hT := rowDigits_typed Vn cr sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn hV hs hBl hk
  obtain ⟨v1, v2, v3⟩ := rowDigits_V Vn cr sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn hV
  obtain ⟨g1, g2, g3, g4⟩ := rowDigits_sig Vn cr sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn hs
  refine ⟨hT,
    fun s hs => rd_V _ _ _ _ _ _ _ _ _ _ _ _ _ hs,
    v1, v2, v3,
    rowDigits_cs Vn cr sg l1n h1n Blon Bhin kap Rlon Rhin q1n rrn rqn hc,
    g1, g2, g3, g4,
    b256_of_bytes_lt (fun j hj => rd_l1 _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hl.1 (lt_of_lt_of_le hl.2 (by norm_num)),
    b256_of_bytes_lt (fun j hj => rd_h1 _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hh.1 (lt_of_lt_of_le hh.2 (by norm_num)),
    b256_of_bytes_lt (fun j hj => rd_Blo _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hBl.1 (lt_of_lt_of_le hBl.2 (by norm_num)),
    b256_of_bytes_lt (fun j hj => rd_Bhi _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hBh.1 (lt_of_lt_of_le hBh.2 (by norm_num)),
    ?_,
    b256_of_bytes_lt (fun j hj => rd_Rlo _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hRl.1 (lt_of_lt_of_le hRl.2 (by norm_num)),
    b256_of_bytes_lt (fun j hj => rd_Rhi _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hRh.1 (lt_of_lt_of_le hRh.2 (by norm_num)),
    b256_of_bytes_lt (fun j hj => rd_q1 _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hq.1 (lt_of_lt_of_le hq.2 (by norm_num)),
    b256_of_bytes_lt (fun j hj => rd_rr _ _ _ _ _ _ _ _ _ _ _ _ _ hj)
      hrr.1 (lt_of_lt_of_le hrr.2 (by norm_num)),
    b256_of_bytes_lt (fun j _ => rd_rq _ _ _ _ _ _ _ _ _ _ _ _ _ j)
      hrq.1 (lt_of_lt_of_le hrq.2 (by norm_num))⟩
  unfold kc
  rw [rd_79]
  ring

end Spec

/-! ## 2. The honest numbers -/

/-- The honest carry into byte s: ⌊V / 256^s⌋ − Σ_{i < 9 − s} 256^i W_(s+i). That it obeys the
recursion of the carries, as (J1), is part of `carry_ok`. -/
def carry (W : ℕ → ℤ) (Vn : ℤ) (s : ℕ) : ℤ :=
  Vn / 256 ^ s - ∑ i ∈ range (9 - s), 256 ^ i * W (s + i)

/-- The carries. Let V = Σ_{s < 9} 256^s W_s with |W_s| ≤ 2^35. Then c_0 = 0, c_9 = ⌊V / 256^9⌋, the
nine equations (J1) hold over the integers, and c_1, .., c_8 lie in [−2^47, 2^47), so that each fits
six bytes after 2^47 is added. -/
theorem carry_ok (W : ℕ → ℤ) (Vn : ℤ)
    (hV : Vn = ∑ s ∈ range 9, 256 ^ s * W s) (hW : ∀ s < 9, |W s| ≤ 2 ^ 35) :
    carry W Vn 0 = 0 ∧
    carry W Vn 9 = Vn / 256 ^ 9 ∧
    (∀ s < 9, W s + carry W Vn s - Vn / 256 ^ s % 256 - 256 * carry W Vn (s + 1) = 0) ∧
    ∀ s, 1 ≤ s → s ≤ 8 → -2 ^ 47 ≤ carry W Vn s ∧ carry W Vn s < 2 ^ 47 := by
  have b0 := abs_le.mp (hW 0 (by norm_num))
  have b1 := abs_le.mp (hW 1 (by norm_num))
  have b2 := abs_le.mp (hW 2 (by norm_num))
  have b3 := abs_le.mp (hW 3 (by norm_num))
  have b4 := abs_le.mp (hW 4 (by norm_num))
  have b5 := abs_le.mp (hW 5 (by norm_num))
  have b6 := abs_le.mp (hW 6 (by norm_num))
  have b7 := abs_le.mp (hW 7 (by norm_num))
  have b8 := abs_le.mp (hW 8 (by norm_num))
  simp only [sum_range_succ, sum_range_zero, zero_add] at hV
  norm_num at hV b0 b1 b2 b3 b4 b5 b6 b7 b8
  refine ⟨?_, ?_, fun s hs => ?_, fun s h1 h8 => ?_⟩
  · simp only [carry, sum_range_succ, sum_range_zero]
    norm_num
    omega
  · simp [carry]
  · interval_cases s <;> simp only [carry, sum_range_succ, sum_range_zero] <;> norm_num <;> omega
  · interval_cases s <;> simp only [carry, sum_range_succ, sum_range_zero] <;> norm_num <;> omega

/-- The numbers of the square root. s is the integer square root of V + ϵ; its low 24 and high 15
bits are s % 2^24 and s / 2^24. For V ≥ 0, 1 ≤ ϵ < 2^48 and V + ϵ < 2^78 every number of (J2) to
(J5) is in the range of its bytes, and (J3) holds over the integers. The other three hold by the
definitions of the numbers. -/
theorem root_ok (Vn eps s : ℤ) (hV0 : 0 ≤ Vn) (he : 1 ≤ eps) (he2 : eps < 2 ^ 48)
    (hN : Vn + eps < 2 ^ 78) (h1 : s ^ 2 ≤ Vn + eps) (h2 : Vn + eps < (s + 1) ^ 2) (hs : 0 ≤ s) :
    1 ≤ s ∧ s < 2 ^ 39 ∧
    (0 ≤ Vn + eps - s ^ 2 ∧ Vn + eps - s ^ 2 < 2 ^ 40) ∧
    (0 ≤ 2 * s - (Vn + eps - s ^ 2) ∧ 2 * s - (Vn + eps - s ^ 2) < 2 ^ 40) ∧
    (0 ≤ (s % 2 ^ 24) * (s / 2 ^ 24) % 2 ^ 23 ∧ (s % 2 ^ 24) * (s / 2 ^ 24) % 2 ^ 23 < 2 ^ 23) ∧
    (0 ≤ (s % 2 ^ 24) * (s / 2 ^ 24) / 2 ^ 23 ∧ (s % 2 ^ 24) * (s / 2 ^ 24) / 2 ^ 23 < 2 ^ 16) ∧
    (-4 ≤ Vn / 2 ^ 48 - (s % 2 ^ 24) * (s / 2 ^ 24) / 2 ^ 23 - (s / 2 ^ 24) * (s / 2 ^ 24) ∧
      Vn / 2 ^ 48 - (s % 2 ^ 24) * (s / 2 ^ 24) / 2 ^ 23 - (s / 2 ^ 24) * (s / 2 ^ 24) < 4) ∧
    Vn % 2 ^ 48 + eps - (s % 2 ^ 24) * (s % 2 ^ 24) -
        2 ^ 25 * ((s % 2 ^ 24) * (s / 2 ^ 24) % 2 ^ 23) - (Vn + eps - s ^ 2) +
        2 ^ 48 *
          (Vn / 2 ^ 48 - (s % 2 ^ 24) * (s / 2 ^ 24) / 2 ^ 23 - (s / 2 ^ 24) * (s / 2 ^ 24)) =
      0 := by
  have hs1 : 1 ≤ s := by
    by_contra h
    have : s = 0 := by omega
    subst this
    norm_num at h2
    omega
  have hs39 : s < 2 ^ 39 := by
    by_contra h
    have h39 : (2 : ℤ) ^ 39 ≤ s := by omega
    have h78 := mul_le_mul h39 h39 (by norm_num) hs
    rw [← pow_two] at h78
    norm_num at h78 hN
    linarith
  have ha := Int.emod_nonneg s (show (2 : ℤ) ^ 24 ≠ 0 by norm_num)
  have ha2 := Int.emod_lt_of_pos s (show (0 : ℤ) < 2 ^ 24 by norm_num)
  have hsab := Int.emod_add_mul_ediv s (2 ^ 24)
  have hb0 : 0 ≤ s / 2 ^ 24 := Int.ediv_nonneg hs (by norm_num)
  have hb2 : s / 2 ^ 24 < 2 ^ 15 := by omega
  generalize s % 2 ^ 24 = a at *
  generalize s / 2 ^ 24 = b at *
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb0
  have hab2 : a * b < 2 ^ 39 := by
    have := mul_lt_mul'' ha2 hb2 ha hb0
    norm_num at this ⊢
    exact this
  have hB := Int.emod_add_mul_ediv (a * b) (2 ^ 23)
  have hBl := Int.emod_nonneg (a * b) (show (2 : ℤ) ^ 23 ≠ 0 by norm_num)
  have hBl2 := Int.emod_lt_of_pos (a * b) (show (0 : ℤ) < 2 ^ 23 by norm_num)
  have hBh0 : 0 ≤ a * b / 2 ^ 23 := Int.ediv_nonneg hab0 (by norm_num)
  have hBh2 : a * b / 2 ^ 23 < 2 ^ 16 := by omega
  have hVs := Int.emod_add_mul_ediv Vn (2 ^ 48)
  have hVl := Int.emod_nonneg Vn (show (2 : ℤ) ^ 48 ≠ 0 by norm_num)
  have hVl2 := Int.emod_lt_of_pos Vn (show (0 : ℤ) < 2 ^ 48 by norm_num)
  generalize a * b % 2 ^ 23 = Bl at *
  generalize a * b / 2 ^ 23 = Bh at *
  generalize Vn % 2 ^ 48 = Vl at *
  generalize Vn / 2 ^ 48 = Vh at *
  have hE1 : Vl + eps - a * a - 2 ^ 25 * Bl - (Vn + eps - s ^ 2) + 2 ^ 48 * (Vh - Bh - b * b) =
      0 := by
    rw [← hsab, ← hVs]
    linear_combination (-(2 ^ 25 : ℤ)) * hB
  have haa : a * a < 2 ^ 48 := by
    have := mul_lt_mul'' ha2 ha2 ha ha
    norm_num at this ⊢
    exact this
  have haa0 : 0 ≤ a * a := mul_nonneg ha ha
  have hl0 : 0 ≤ Vn + eps - s ^ 2 := by linarith
  have hl2 : Vn + eps - s ^ 2 ≤ 2 * s := by
    have e : (s + 1) ^ 2 = s ^ 2 + 2 * s + 1 := by ring
    rw [e] at h2
    linarith
  refine ⟨hs1, hs39, ⟨hl0, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨hBl, hBl2⟩, ⟨hBh0, hBh2⟩, ?_, hE1⟩
  generalize Vh - Bh - b * b = k at *
  generalize a * a = aa at *
  generalize Vn + eps - s ^ 2 = l at *
  constructor <;> omega

/-- The numbers of the reciprocal R = ⌊(2^M + ⌊s/2⌋) / s⌋, for M ≤ 47 and 1 ≤ s < 2^39. Every number
of (J6) to (J9) is in the range of its bytes, and (J7) and (J8) hold over the integers. (J6) and
(J9) hold by the definitions of q1 and rq. -/
theorem recip_ok (M : ℕ) (hM : M ≤ 47) (s R : ℤ) (hs1 : 1 ≤ s)
    (hs39 : s < 2 ^ 39) (hR : R = (2 ^ M + s / 2) / s) :
    (0 ≤ R % 2 ^ 24 ∧ R % 2 ^ 24 < 2 ^ 24) ∧
    (0 ≤ R / 2 ^ 24 ∧ R / 2 ^ 24 < 2 ^ 24) ∧
    (0 ≤ R % 2 ^ 24 * (s / 2 ^ 24) + R / 2 ^ 24 * (s % 2 ^ 24) ∧
      R % 2 ^ 24 * (s / 2 ^ 24) + R / 2 ^ 24 * (s % 2 ^ 24) < 2 ^ 24) ∧
    (0 ≤ 2 ^ M + s / 2 - R * s ∧ 2 ^ M + s / 2 - R * s < 2 ^ 40) ∧
    (0 ≤ s - 1 - (2 ^ M + s / 2 - R * s) ∧ s - 1 - (2 ^ M + s / 2 - R * s) < 2 ^ 40) ∧
    R / 2 ^ 24 * (s / 2 ^ 24) = 0 ∧
    2 ^ (M + 1) + s - s % 2 - 2 * (R % 2 ^ 24 * (s % 2 ^ 24)) -
        2 ^ 25 * (R % 2 ^ 24 * (s / 2 ^ 24) + R / 2 ^ 24 * (s % 2 ^ 24)) -
        2 * (2 ^ M + s / 2 - R * s) = 0 := by
  have hp1 : (1 : ℤ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
  have hp2 : (2 : ℤ) ^ M ≤ 2 ^ 47 := pow_le_pow_right₀ (by norm_num) hM
  have hpp : (2 : ℤ) ^ (M + 1) = 2 * 2 ^ M := by ring
  rw [hpp]
  generalize (2 : ℤ) ^ M = p at *
  have hh0 : 0 ≤ s / 2 := by omega
  have hh2 : 2 * (s / 2) = s - s % 2 := by omega
  have hs0a : 0 ≤ s % 2 := by omega
  have hs0b : s % 2 < 2 := by omega
  have hdiv := Int.emod_add_mul_ediv (p + s / 2) s
  have hm0 := Int.emod_nonneg (p + s / 2) (show s ≠ 0 by omega)
  have hm2 := Int.emod_lt_of_pos (p + s / 2) (show 0 < s by omega)
  rw [← hR] at hdiv
  have hR0 : 0 ≤ R := by rw [hR]; exact Int.ediv_nonneg (by omega) (by omega)
  have hrr : p + s / 2 - R * s = (p + s / 2) % s := by linarith
  rw [hrr]
  generalize (p + s / 2) % s = rr at *
  -- R s = p + s / 2 - rr
  have hRs : R * s = p + s / 2 - rr := by linarith
  have ha := Int.emod_nonneg s (show (2 : ℤ) ^ 24 ≠ 0 by norm_num)
  have ha2 := Int.emod_lt_of_pos s (show (0 : ℤ) < 2 ^ 24 by norm_num)
  have hsab := Int.emod_add_mul_ediv s (2 ^ 24)
  have hb0 : 0 ≤ s / 2 ^ 24 := Int.ediv_nonneg (by omega) (by norm_num)
  have hl := Int.emod_nonneg R (show (2 : ℤ) ^ 24 ≠ 0 by norm_num)
  have hl2 := Int.emod_lt_of_pos R (show (0 : ℤ) < 2 ^ 24 by norm_num)
  have hRab := Int.emod_add_mul_ediv R (2 ^ 24)
  have hH0 : 0 ≤ R / 2 ^ 24 := Int.ediv_nonneg hR0 (by norm_num)
  have hRle : R ≤ R * s := le_mul_of_one_le_right hR0 hs1
  have hR48 : R < 2 ^ 48 := by omega
  have hH2 : R / 2 ^ 24 < 2 ^ 24 := by omega
  generalize s % 2 = s0 at *
  generalize s / 2 = sh at *
  generalize s % 2 ^ 24 = a at *
  generalize s / 2 ^ 24 = b at *
  generalize R % 2 ^ 24 = Rl at *
  generalize R / 2 ^ 24 = Rh at *
  -- The product of the two high parts is 0.
  have hz : Rh * b = 0 := by
    rcases eq_or_lt_of_le hb0 with h | h
    · rw [← h, mul_zero]
    · rcases eq_or_lt_of_le hH0 with h' | h'
      · rw [← h', zero_mul]
      · exfalso
        have h1 : 1 ≤ b := h
        have h2 : 1 ≤ Rh := h'
        have h3 : 1 ≤ Rh * b := one_le_mul_of_one_le_of_one_le h2 h1
        have h4 : 0 ≤ Rl * a := mul_nonneg hl ha
        have h5 : 0 ≤ Rl * b := mul_nonneg hl hb0
        have h6 : 0 ≤ Rh * a := mul_nonneg hH0 ha
        have e : R * s = Rl * a + 2 ^ 24 * (Rl * b + Rh * a) + 2 ^ 48 * (Rh * b) := by
          rw [← hRab, ← hsab]; ring
        omega
  have e : R * s = Rl * a + 2 ^ 24 * (Rl * b + Rh * a) := by
    have : R * s = Rl * a + 2 ^ 24 * (Rl * b + Rh * a) + 2 ^ 48 * (Rh * b) := by
      rw [← hRab, ← hsab]; ring
    rw [this, hz]; ring
  have h4 : 0 ≤ Rl * a := mul_nonneg hl ha
  have h5 : 0 ≤ Rl * b := mul_nonneg hl hb0
  have h6 : 0 ≤ Rh * a := mul_nonneg hH0 ha
  generalize Rl * a = x1 at *
  generalize Rl * b = x2 at *
  generalize Rh * a = x3 at *
  generalize R * s = Rs at *
  refine ⟨⟨hl, hl2⟩, ⟨hH0, hH2⟩, ⟨by omega, by omega⟩, ⟨hm0, by omega⟩,
    ⟨by omega, by omega⟩, hz, by omega⟩

/-! ## 3. The honest ledger -/

/-- The honest ledger of a normalisation with parameters np on the d values whose cells are b: its
99 bytes, as values. -/
def hon (np : NormPar) (d : ℕ) (b : ℕ → ℕ → ℤ) : ℕ → ℤ :=
  let Vn := NORM.V d (xOf b)
  let s := NORM.sig np d (xOf b)
  let Rn := NORM.R np d (xOf b)
  rowDigits Vn (carry (Wsum d b) Vn) s (Vn + np.eps - s ^ 2) (2 * s - (Vn + np.eps - s ^ 2))
    ((s % 2 ^ 24) * (s / 2 ^ 24) % 2 ^ 23) ((s % 2 ^ 24) * (s / 2 ^ 24) / 2 ^ 23)
    (Vn / 2 ^ 48 - (s % 2 ^ 24) * (s / 2 ^ 24) / 2 ^ 23 - (s / 2 ^ 24) * (s / 2 ^ 24)) (Rn % 2 ^ 24)
    (Rn / 2 ^ 24) (Rn % 2 ^ 24 * (s / 2 ^ 24) + Rn / 2 ^ 24 * (s % 2 ^ 24))
    (2 ^ np.M + s / 2 - Rn * s) (s - 1 - (2 ^ np.M + s / 2 - Rn * s))

/-- The hypotheses on the parameters, on the cells of the input and on the integer model. -/
structure HonHyp (np : NormPar) (d : ℕ) (b : ℕ → ℕ → ℤ) : Prop where
  eps_pos : 1 ≤ np.eps
  eps_lt : np.eps < 2 ^ 48
  M_le : np.M ≤ 47
  d_le : d ≤ 2 ^ 16
  /-- the cells of the input are signed bytes, or 128 -/
  cell : ∀ l < 5, ∀ j < d, |b l j| ≤ 128
  /-- the range condition of (N1) -/
  fits : NORM.V d (xOf b) + np.eps < 2 ^ 78

/-- For cells of absolute value at most 128 and d ≤ 2^16, every W_s is at most 2^35 in absolute
value. -/
theorem abs_Wsum_le_pow {d : ℕ} {b : ℕ → ℕ → ℤ} (hd : d ≤ 2 ^ 16)
    (hb : ∀ l < 5, ∀ j < d, |b l j| ≤ 128) (s : ℕ) : |Wsum d b s| ≤ 2 ^ 35 := by
  refine (abs_Wsum_le hb s).trans ?_
  have : (d : ℤ) ≤ 2 ^ 16 := by exact_mod_cast hd
  nlinarith

/-- Under `HonHyp`, the honest ledger is in range (`Typed`), the 17 identities hold for it over the
integers, and its carries are the honest carries. -/
theorem hon_spec {np : NormPar} {d : ℕ} {b : ℕ → ℕ → ℤ} (H : HonHyp np d b) :
    Typed (hon np d b) ∧
    (∀ k < 17, idn np (Wsum d b) (hon np d b) k = 0) ∧
    (∀ s ≤ 9, cs (hon np d b) s = carry (Wsum d b) (NORM.V d (xOf b)) s) := by
  set x : ℕ → ℤ := xOf b with hx
  set Vn := NORM.V d x with hVn
  have hV0 : 0 ≤ Vn := sum_nonneg fun j _ => sq_nonneg _
  have he := H.eps_pos
  have hfit : Vn + np.eps < 2 ^ 78 := H.fits
  set s := NORM.sig np d x with hs
  have hspec : 0 ≤ s ∧ s ^ 2 ≤ Vn + np.eps ∧ Vn + np.eps < (s + 1) ^ 2 := by
    have ha : 0 ≤ Vn + np.eps := by linarith
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le ha
    have e : s = (Nat.sqrt n : ℤ) := by
      show isqrt (Vn + np.eps) = _
      rw [hn]
      simp [isqrt]
    rw [e, hn]
    exact ⟨by positivity, by exact_mod_cast Nat.sqrt_le' n, by exact_mod_cast Nat.lt_succ_sqrt' n⟩
  obtain ⟨hs1, hs39, hl1, hh1, hBl, hBh, hk, hE1⟩ :=
    root_ok Vn np.eps s hV0 he H.eps_lt hfit hspec.2.1 hspec.2.2 hspec.1
  set Rn := NORM.R np d x with hRn
  obtain ⟨hRl, hRh, hq, hrr, hrq, hR2, hR3⟩ := recip_ok np.M H.M_le s Rn hs1 hs39 rfl
  have hsum : Vn = ∑ s ∈ range 9, 256 ^ s * Wsum d b s := by
    rw [sum_pow_Wsum]
    rfl
  obtain ⟨hc0, hc9, hcL, hcB⟩ :=
    carry_ok (Wsum d b) Vn hsum fun s _ => abs_Wsum_le_pow H.d_le H.cell s
  obtain ⟨hty, hDv, hDV, hDlo, hDhi, hDc, hDsig, hDs0, hDsa, hDsb, hDl1, hDh1, hDBlo, hDBhi, hDkc, hDRlo, hDRhi, hDq1, hDrr, hDrq⟩ :=
    rowDigits_spec Vn (carry (Wsum d b) Vn) s _ _ _ _ _ _ _ _ _ _ ⟨hV0, by linarith⟩ hcB
      ⟨hspec.1, hs39⟩ hl1 hh1 hBl hBh hk hRl hRh hq hrr hrq
  set D := hon np d b with hD
  have hcD : ∀ s ≤ 9, cs D s = carry (Wsum d b) Vn s := by
    intro s hs9
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · rw [hc0]; rfl
    · rcases Nat.lt_or_ge s 9 with h | h
      · exact hDc s hpos (by omega)
      · obtain rfl : s = 9 := by omega
        rw [hc9]
        show D 9 = _
        rw [show D 9 = Vn / 256 ^ 9 % 256 from hDv 9 (by norm_num)]
        have : Vn / 256 ^ 9 < 256 := by
          have : Vn < 2 ^ 78 := by linarith
          omega
        have h0 : 0 ≤ Vn / 256 ^ 9 := Int.ediv_nonneg hV0 (by norm_num)
        exact Int.emod_eq_of_lt h0 this
  refine ⟨hty, fun k hk17 => ?_, hcD⟩
  by_cases hk9 : k < 9
  · rw [idn_j1 np _ _ hk9, hcD k (by omega), hcD (k + 1) (by omega),
      show D k = Vn / 256 ^ k % 256 from hDv k (by omega)]
    exact hcL k hk9
  · have hcases : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [idn_j2, show sa D = _ from hDsa, show sb D = _ from hDsb,
        show Blo D = _ from hDBlo, show Bhi D = _ from hDBhi]
      have := Int.emod_add_mul_ediv (s % 2 ^ 24 * (s / 2 ^ 24)) (2 ^ 23)
      linarith
    · rw [idn_j3, sq, show Vlo D = _ from hDlo, show sa D = _ from hDsa, show Blo D = _ from hDBlo,
        show l1 D = _ from hDl1, show kc D = _ from hDkc]
      simp only [Int.cast_id]
      exact hE1
    · rw [idn_j4, sq, show Vhi D = _ from hDhi, show Bhi D = _ from hDBhi,
        show sb D = _ from hDsb, show kc D = _ from hDkc]
      ring
    · rw [idn_j5, show l1 D = _ from hDl1, show h1 D = _ from hDh1, show sig D = _ from hDsig]
      ring
    · rw [idn_j6, show Rlo D = _ from hDRlo, show Rhi D = _ from hDRhi, show sa D = _ from hDsa,
        show sb D = _ from hDsb, show q1 D = _ from hDq1]
      ring
    · rw [idn_j7, show Rhi D = _ from hDRhi, show sb D = _ from hDsb]
      exact hR2
    · rw [idn_j8, show sig D = _ from hDsig, show s0 D = _ from hDs0, show Rlo D = _ from hDRlo,
        show sa D = _ from hDsa, show q1 D = _ from hDq1, show rr D = _ from hDrr]
      exact hR3
    · rw [idn_j9, show rr D = _ from hDrr, show rq D = _ from hDrq, show sig D = _ from hDsig]
      ring

section Corollaries
variable {np : NormPar} {d : ℕ} {b : ℕ → ℕ → ℤ} (H : HonHyp np d b)
include H

/-- Under `HonHyp`, every key of ROW is an entry of its table. -/
theorem hon_typed : Typed (hon np d b) := (hon_spec H).1

/-- Under `HonHyp`, every honest byte is in [0, 255]. -/
theorem hon_byte {n : ℕ} (hn : n < 99) : 0 ≤ hon np d b n ∧ hon np d b n ≤ 255 :=
  (hon_typed H).byte hn

/-- Under `HonHyp`, every honest cell of the ledger is a signed byte. -/
theorem hon_cell {n : ℕ} (hn : n < 99) : -128 ≤ hon np d b n - 128 ∧ hon np d b n - 128 ≤ 127 := by
  have := hon_byte H hn
  omega

/-- Under `HonHyp`, the 17 identities hold for the honest ledger, over the integers. -/
theorem hon_idn : ∀ k < 17, idn np (Wsum d b) (hon np d b) k = 0 := (hon_spec H).2.1

/-- Under `HonHyp`, the honest ledger's V, ς, R (`hon_V`, `hon_sig`, `hon_R`) are those of the
integer model. -/
theorem hon_V : Vlo (hon np d b) + 2 ^ 48 * Vhi (hon np d b) = NORM.V d (xOf b) :=
  (sound_int (le_trans (by norm_num) H.eps_pos) (hon_typed H) (hon_idn H)).1
theorem hon_sig : sig (hon np d b) = NORM.sig np d (xOf b) :=
  (sound_int (le_trans (by norm_num) H.eps_pos) (hon_typed H) (hon_idn H)).2.1
theorem hon_R : R (hon np d b) = NORM.R np d (xOf b) :=
  (sound_int (le_trans (by norm_num) H.eps_pos) (hon_typed H) (hon_idn H)).2.2.1

omit H in
/-- The recursion of the honest carries: c_0 = 0 and, under `HonHyp`, c_(s+1) = ⌊(W_s + c_s) / 256⌋
for s < 9. -/
theorem hon_carry_zero : cs (hon np d b) 0 = 0 := rfl
theorem hon_carry_succ {s : ℕ} (hs : s < 9) :
    cs (hon np d b) (s + 1) = (Wsum d b s + cs (hon np d b) s) / 256 := by
  have h := hon_idn H s (by omega)
  rw [idn_j1 np _ _ hs] at h
  have hb := hon_byte H (n := s) (by omega)
  omega

end Corollaries

end Inst.Model.Ledger
