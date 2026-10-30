-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicyNoWrap.lean: for the head's acceptance policy: the top digit of the margin
(`K0of`) and sums over the counted positions. From congruences modulo p to the relations (B1) to
(B4), (HE), (Z) over ℤ: `HRel_of_HCong`, Policy/Rel/LedgerHeadNoWrap.lean.

Integers only: no cell (a cell is one committed integer of a proof), no protocol. (The relation on
a request: Inst/Model/ProgramR.lean.)
`HRel_of_HCong` is at sh = 8, F = 24, BIG = 2^37, T ≤ 2^10, and under the same bounds as the honest
prover's rule assumes (`Fit`, Inst/Model/Head/PolicyDefs.lean: |lg| ≤ 68,715,282,431 at t < T, v <
V; C, θ < 2^40; cap < 2^16; 2 V ≤ 2^24). `NB_le` and `sum_cnt_bounds` ask T ≤ 2^10.

The implementation. Policy/Rel/LedgerHeadNoWrap.lean serves the same end as the implementation's
no-overflow checks on the output head, for the margin with the hidden number, the table EX and the
four claims on the hidden numbers, by other inequalities in another order. The implementation's
protocol text (not its latest text; not in this repository) gives the family only; the single
inequalities are in
verifier/src/cp_verify.cpp, error names no-wrap-H-..; they bound the digits' cells before their
lookups and keep all parts below 2^60. In Policy/Rel/LedgerHeadNoWrap.lean the middle and the low
digit come with their ranges (`HCong.K1r`, `HCong.K2r`; proved under `RFz p`: `K1_range`,
`K2_range`), and each difference is kept below p. What is said of the implementation is a
reading of programs which are not in this library: nothing here checks it, and no Lean statement of
this file is about the implementation or its texts. `AcceptancePolicy.OK` with T = 2^10 implies the
implementation's conditions E2, E3, E4 (`PolTests`, Inst/Model/ProgTests.lean): by hand, no theorem.

(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.PolicySound
import Inst.Model.Common.LedgerSound

set_option autoImplicit false

namespace Inst.Model.Head.Policy

open Inst.Model

section
variable {P : Params} (lg : ℕ → ℕ → ℤ) (x : Instance P) (h : Hid) (K1 K2 : ℕ → ℕ → ℤ)

/-- the top digit of the margin -/
def K0of (v t : ℕ) : ℤ := (marg lg x h t v - 2 ^ 8 * K1 v t - K2 v t) / 2 ^ 23

end

section
variable {P : Params} {x : Instance P}

theorem NB_le (hT : P.T ≤ 2 ^ 10) : (x.NB : ℤ) ≤ 2 ^ 10 := by
  have : x.NB ≤ 2 ^ 10 := by unfold Instance.NB; omega
  exact_mod_cast this

/-- if T ≤ 2^10 and B ≥ 0, a sum over the counted positions of terms in [0, B] is in [0, 2^10 B] -/
theorem sum_cnt_bounds (hT : P.T ≤ 2 ^ 10) (f : ℕ → ℤ) {B : ℤ}
    (hB : 0 ≤ B) (hf : ∀ t ∈ x.cnt, 0 ≤ f t ∧ f t ≤ B) :
    0 ≤ ∑ t ∈ x.cnt, f t ∧ ∑ t ∈ x.cnt, f t ≤ 2 ^ 10 * B := by
  refine ⟨Finset.sum_nonneg fun t ht => (hf t ht).1, ?_⟩
  have h1 := Finset.sum_le_card_nsmul x.cnt f B fun t ht => (hf t ht).2
  rw [x.card_cnt, nsmul_eq_mul] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_right (NB_le hT) hB)

end

end Inst.Model.Head.Policy
