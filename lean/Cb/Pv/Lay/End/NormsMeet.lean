-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsMeet.lean: hidden sums and products that make the seventeen lines of a norm true,
if the two lines that hold no hidden value are.

The lines (J1) to (J9) of a norm, with letters in the places of the sums W_s and of the row products
(idnP, Inst/Model/Common/LedgerForms.lean), are affine in these letters. Fifteen of the seventeen
lines hold a letter; two (numbers 12 and 16) read the bytes alone. This file names values of the
letters at which the fifteen hold, whatever the bytes are.

Main definitions: hidW (the nine sums), hidP (the seven products; dl: what product 4 holds more and
product 5 less, as the two stand in one line together).
Main theorem: idnP_hid: at these values every line holds, if lines 12 and 16 do.

Limits. Nothing says that these values are the true sums and products. 2 is asked not to be 0.


-/
import Cb.Pv.Lay.End.NormsCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End

open Inst.Model (NormPar)
open Inst.Model.Ledger (idnP cs Vlo Vhi l1 h1 Blo Bhi kc sig s0 q1 rr rq)

variable {E : Type} [Field E]

/-- The value of the letter for W_x at which line x holds. -/
def hidW (Dg : ℕ → E) (x : ℕ) : E := Dg x + 256 * cs Dg (x + 1) - cs Dg x

/-- Values of the letters for the seven products at which lines 9, 10, 11, 13, 14, 15 hold. -/
def hidP (np : NormPar) (Dg : ℕ → E) (dl : E) (j : ℕ) : E :=
  match j with
  | 0 => Vlo Dg + (np.eps : E) - 2 ^ 25 * Blo Dg - l1 Dg + 2 ^ 48 * kc Dg
  | 1 => Blo Dg + 2 ^ 23 * Bhi Dg
  | 2 => Vhi Dg - Bhi Dg - kc Dg
  | 3 => (2 ^ (np.M + 1) + sig Dg - s0 Dg - 2 ^ 25 * q1 Dg - 2 * rr Dg) / 2
  | 4 => q1 Dg + dl
  | 5 => -dl
  | _ => 0

/-- At these values every line holds, if the two lines that read the bytes alone do. -/
theorem idnP_hid (h2 : (2 : E) ≠ 0) (np : NormPar) (Dg : ℕ → E) (dl : E)
    (h12 : l1 Dg + h1 Dg - 2 * sig Dg = 0) (h16 : rr Dg + rq Dg - sig Dg + 1 = 0) (k : ℕ) :
    idnP np (hidW Dg) Dg (hidP np Dg dl) k = 0 := by
  by_cases hk : k < 9
  · rw [Inst.Model.Ledger.idnP_j1 np _ _ _ hk]
    unfold hidW
    ring
  · by_cases hk17 : 17 ≤ k
    · exact Inst.Model.Ledger.idnP_of_le np _ _ _ hk17
    · have hc : k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show hidP np Dg dl 1 - Blo Dg - 2 ^ 23 * Bhi Dg = 0
        show Blo Dg + 2 ^ 23 * Bhi Dg - Blo Dg - 2 ^ 23 * Bhi Dg = 0
        ring
      · show Vlo Dg + (np.eps : E) - hidP np Dg dl 0 - 2 ^ 25 * Blo Dg - l1 Dg + 2 ^ 48 * kc Dg = 0
        show Vlo Dg + (np.eps : E) -
          (Vlo Dg + (np.eps : E) - 2 ^ 25 * Blo Dg - l1 Dg + 2 ^ 48 * kc Dg) - 2 ^ 25 * Blo Dg -
          l1 Dg + 2 ^ 48 * kc Dg = 0
        ring
      · show Vhi Dg - Bhi Dg - (Vhi Dg - Bhi Dg - kc Dg) - kc Dg = 0
        ring
      · exact h12
      · show q1 Dg + dl + -dl - q1 Dg = 0
        ring
      · rfl
      · show 2 ^ (np.M + 1) + sig Dg - s0 Dg -
          2 * ((2 ^ (np.M + 1) + sig Dg - s0 Dg - 2 ^ 25 * q1 Dg - 2 * rr Dg) / 2) -
          2 ^ 25 * q1 Dg - 2 * rr Dg = 0
        have e : ∀ X : E, 2 * (X / 2) = X := fun X => by field_simp
        rw [e]
        ring
      · exact h16

end Cb.Pv.Lay.End
