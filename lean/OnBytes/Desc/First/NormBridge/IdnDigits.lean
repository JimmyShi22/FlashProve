-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/NormBridge/IdnDigits.lean: THE LEDGER's IDENTITIES READ THE DIGITS BELOW 99 ALONE.
Algebra over
a commutative ring, on the library's definitions (Inst/Model/Common/Ledger.lean, LedgerForms.lean).
Statements and proofs. So a premise "the digits' forms are worth the cells' extensions" need be
asked of the
99 digits of a row only.

  b256_congr, cs_congr, sa_congr, sb_congr, Rlo_congr, Rhi_congr, prods_congr, idnP_congr_D.

-/
import Inst.Model.Common.LedgerForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D6.Bridge
open Finset
open Inst.Model (NormPar)
open Inst.Model.Ledger

variable {K : Type} [CommRing K] {D D' : ℕ → K}

theorem b256_congr (h : ∀ n < 99, D n = D' n) (a n : ℕ) (han : a + n ≤ 99) :
    b256 D a n = b256 D' a n := by
  unfold b256
  exact sum_congr rfl fun l hl => by
    rw [h (a + l) (by
      have := mem_range.mp hl
      omega)]

theorem cs_congr (h : ∀ n < 99, D n = D' n) (s : ℕ) (hs : s ≤ 9) : cs D s = cs D' s := by
  unfold cs
  by_cases h0 : s = 0
  · rw [if_pos h0, if_pos h0]
  · by_cases h9 : s = 9
    · rw [if_neg h0, if_neg h0, if_pos h9, if_pos h9, h 9 (by omega)]
    · rw [if_neg h0, if_neg h0, if_neg h9, if_neg h9, b256_congr h _ 6 (by omega)]

theorem sa_congr (h : ∀ n < 99, D n = D' n) : sa D = sa D' := by
  unfold sa
  rw [h 58 (by omega), h 59 (by omega), h 60 (by omega), h 61 (by omega)]

theorem sb_congr (h : ∀ n < 99, D n = D' n) : sb D = sb D' := by
  unfold sb
  rw [h 62 (by omega), h 63 (by omega)]

theorem Rlo_congr (h : ∀ n < 99, D n = D' n) : Rlo D = Rlo D' := b256_congr h 80 3 (by omega)

theorem Rhi_congr (h : ∀ n < 99, D n = D' n) : Rhi D = Rhi D' := b256_congr h 83 3 (by omega)

theorem prods_congr (h : ∀ n < 99, D n = D' n) : prods D = prods D' := by
  unfold prods
  rw [sa_congr h, sb_congr h, Rlo_congr h, Rhi_congr h]

/-- **An identity reads the digits below 99 alone.** -/
theorem idnP_congr_D (np : NormPar) (Ws pv : ℕ → K) (h : ∀ n < 99, D n = D' n) (k : ℕ) :
    idnP np Ws D pv k = idnP np Ws D' pv k := by
  have eVlo : Vlo D = Vlo D' := b256_congr h 0 6 (by omega)
  have eVhi : Vhi D = Vhi D' := b256_congr h 6 4 (by omega)
  have el1 : l1 D = l1 D' := b256_congr h 64 5 (by omega)
  have eh1 : h1 D = h1 D' := b256_congr h 69 5 (by omega)
  have eBlo : Blo D = Blo D' := b256_congr h 74 3 (by omega)
  have eBhi : Bhi D = Bhi D' := b256_congr h 77 2 (by omega)
  have eq1 : q1 D = q1 D' := b256_congr h 86 3 (by omega)
  have err : rr D = rr D' := b256_congr h 89 5 (by omega)
  have erq : rq D = rq D' := b256_congr h 94 5 (by omega)
  have es0 : s0 D = s0 D' := h 59 (by omega)
  have ekc : kc D = kc D' := by
    unfold kc
    rw [h 79 (by omega)]
  have esig : sig D = sig D' := by
    unfold sig
    rw [sa_congr h, sb_congr h]
  by_cases hk9 : k < 9
  · rw [idnP_j1 np _ _ _ hk9, idnP_j1 np _ _ _ hk9, cs_congr h k (by omega),
      cs_congr h (k + 1) (by omega), h k (by omega)]
  · by_cases hk17 : 17 ≤ k
    · rw [idnP_of_le np _ _ _ hk17, idnP_of_le np _ _ _ hk17]
    · have hc : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show pv 1 - Blo D - 2 ^ 23 * Bhi D = pv 1 - Blo D' - 2 ^ 23 * Bhi D'
        rw [eBlo, eBhi]
      · show Vlo D + (np.eps : K) - pv 0 - 2 ^ 25 * Blo D - l1 D + 2 ^ 48 * kc D =
          Vlo D' + (np.eps : K) - pv 0 - 2 ^ 25 * Blo D' - l1 D' + 2 ^ 48 * kc D'
        rw [eVlo, eBlo, el1, ekc]
      · show Vhi D - Bhi D - pv 2 - kc D = Vhi D' - Bhi D' - pv 2 - kc D'
        rw [eVhi, eBhi, ekc]
      · show l1 D + h1 D - 2 * sig D = l1 D' + h1 D' - 2 * sig D'
        rw [el1, eh1, esig]
      · show pv 4 + pv 5 - q1 D = pv 4 + pv 5 - q1 D'
        rw [eq1]
      · rfl
      · show 2 ^ (np.M + 1) + sig D - s0 D - 2 * pv 3 - 2 ^ 25 * q1 D - 2 * rr D =
          2 ^ (np.M + 1) + sig D' - s0 D' - 2 * pv 3 - 2 ^ 25 * q1 D' - 2 * rr D'
        rw [esig, es0, eq1, err]
      · show rr D + rq D - sig D + 1 = rr D' + rq D' - sig D' + 1
        rw [err, erq, esig]

end D6.Bridge

#print axioms D6.Bridge.idnP_congr_D
