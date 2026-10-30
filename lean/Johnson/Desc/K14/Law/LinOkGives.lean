-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LinOkGives.lean: two more fruits of the public shape's conditions
(OnBytes/Iop/Lin.lean:
linOk), which a yes of "LIN point" holds (Johnson/Desc/K14/Law/Condition.lean: linPoint_ok): beside
index_ok_of_linOk (Johnson/Desc/K14/Law/Run.lean).

  room_of_linOk   the places that hold the matrix lie in a row's plain part.
  layW_of_linOk   the other vector's layout bears the columns.
What is not claimed. Nothing on a draw. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Placed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params

/-- The places that hold the matrix lie in a row's plain part. -/
theorem room_of_linOk (codes : Codes) (S : LinShape) (hok : linOk codes S = true) :
    S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain := by
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hS : S.ok = true := by tauto
  simp only [LinShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hS
  tauto

/-- The other vector's layout bears the columns. -/
theorem layW_of_linOk (codes : Codes) (S : LinShape) (hok : linOk codes S = true) :
    S.kCol ≤ (linLayW codes S).bits := by
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have h : 2 ^ S.kCol ≤ vectorRoom codes S.w S.wRowsHigh := by tauto
  exact (Nat.pow_le_pow_iff_right (by decide)).1 (Nat.le_trans h (vectorRoom_le codes S.w
      S.wRowsHigh))

end Desc.K14.Law
