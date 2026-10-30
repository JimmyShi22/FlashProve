-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/SmallJoin.lean: the largest round-by-round error after a join (Iop/Join.lean).

An error of a round is a count of challenge values. `Small D ε` (Blocks/Small.lean): every count of
the list, times D, is at most the number of values of the verifier message; so each error is ≤ 1/D.
A join adds the errors of the two rounds. So a bound 1/D on all errors still holds if the two rounds
have errors at most 1/D1 and 1/D2 with 1/D1 + 1/D2 ≤ 1/D. (Words of this library: lean/GLOSSARY.md.)
 * `small_two`: that statement for the counts e1 * n2 + n1 * e2 of a joined round, for D1, D2 > 0;
   `small_two_half`: the case D1 = D2 = 2 D.
 * `small_two_unit`: the first verifier message has one value and the error 0.
 * `two_w`: with a factor w: from e1 * m ≤ w * n1 and e2 * m ≤ n2: (e1 * n2 + n1 * e2) * m ≤
   (w + 1) * (n1 * n2).
 * `unitZero_of_small`: 1 < D and `Small D ε`: a round whose verifier message has one value has the
   error 0 (`Iop.Err.UnitZero`, a hypothesis of the statements on Batch's soundness, (Snd-B)
   (Iop/Batch.lean), after a join).
 * `below_of_small`: 0 < D and `Small D ε` give `Err.Below ε (1/D)`, the form in which the interface
   asks for the bound.

Notation: in `two_w`: `w`: a natural number: where rounds are joined one after the other, the number
of rounds that the first round already represents; `m`: a natural number. Its sister with
proof-of-work bits: `two_wG` (Blocks/GrindSmall.lean).
Limit: nothing on the errors of a given protocol.
These errors are natural numbers (e1, e2) or any list of counts `ε : Err s` (Iop/Rbr.lean): that
rounds, before or after a join, are sound at them is no statement of this file; that tie is
`Doomed.two` (Iop/JoinProofs.lean) for the count e1 * n2 + n1 * e2 of a joined round, and
`InteractiveOracleProof.Sound.recut` (Iop/RecutProofs.lean) for a protocol's list (`Err.recut`, Iop/Recut.lean), each
from soundness at the counts before the join (its hypothesis `h`).
-/
import Blocks.Small
import Iop.JoinKit
import Iop.JoinProofs

set_option autoImplicit false

namespace Blocks
open Iop Prob
open scoped ENNReal

/-- The count of a joined round. -/
theorem small_two {e1 e2 n1 n2 D1 D2 D : ℕ} (p1 : 0 < D1) (p2 : 0 < D2) (h1 : e1 * D1 ≤ n1)
    (h2 : e2 * D2 ≤ n2) (hD : D * (D1 + D2) ≤ D1 * D2) :
    (e1 * n2 + n1 * e2) * D ≤ n1 * n2 := by
  have hpos : 0 < D1 * D2 := Nat.mul_pos p1 p2
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc
    (e1 * n2 + n1 * e2) * D * (D1 * D2) =
        (e1 * D1) * n2 * (D * D2) + n1 * (e2 * D2) * (D * D1) := by ring
    _ ≤ n1 * n2 * (D * D2) + n1 * n2 * (D * D1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1))
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2))
    _ = n1 * n2 * (D * (D1 + D2)) := by ring
    _ ≤ n1 * n2 * (D1 * D2) := Nat.mul_le_mul_left _ hD

/-- Two rounds below half the bound. -/
theorem small_two_half {e1 e2 n1 n2 D : ℕ} (hD : 0 < D)
    (h1 : e1 * (2 * D) ≤ n1) (h2 : e2 * (2 * D) ≤ n2) :
    (e1 * n2 + n1 * e2) * D ≤ n1 * n2 :=
  small_two (Nat.mul_pos (by decide) hD) (Nat.mul_pos (by decide) hD) h1 h2 (le_of_eq (by ring))

/-- If the first verifier message has one value and the error 0, the joined round's count is that of
the second round, so h2 is its bound. -/
theorem small_two_unit {e2 n2 D : ℕ} (h2 : e2 * D ≤ n2) : (0 * n2 + 1 * e2) * D ≤ n2 := by
  rw [Nat.zero_mul, Nat.zero_add, Nat.one_mul]
  exact h2

/-! ## A joined round, with a factor w -/


theorem two_w {e1 e2 n1 n2 w m : ℕ} (h1 : e1 * m ≤ w * n1) (h2 : e2 * m ≤ n2) :
    (e1 * n2 + n1 * e2) * m ≤ (w + 1) * (n1 * n2) :=
  calc (e1 * n2 + n1 * e2) * m = (e1 * m) * n2 + n1 * (e2 * m) := by ring
    _ ≤ (w * n1) * n2 + n1 * n2 :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (w + 1) * (n1 * n2) := by ring


/-! ## What the statements of Iop/ ask for -/

theorem unitZero_of_small {D : ℕ} (hD : 1 < D) : ∀ {s : Shape} {ε : Err s}, Small D ε → ε.UnitZero
  | [], _, _ => trivial
  | _ :: _, (e, _), h => ⟨fun hc => by
      have h1 : e * D ≤ 1 := hc ▸ h.1
      by_contra he
      have : D ≤ e * D := Nat.le_mul_of_pos_left D (Nat.pos_of_ne_zero he)
      omega, unitZero_of_small hD h.2⟩

theorem below_of_small {D : ℕ} (hD : 0 < D) :
    ∀ {s : Shape} {ε : Err s}, Small D ε → Err.Below ε (D : ℝ≥0∞)⁻¹
  | [], _, _ => trivial
  | r :: _, (e, _), h => ⟨by
      have h1 : (e : ℝ≥0∞) * D ≤ (Fintype.card r.Chal : ℝ≥0∞) := by exact_mod_cast h.1
      have hD0 : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hD.ne'
      calc
        (e : ℝ≥0∞) = e * D * (D : ℝ≥0∞)⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hD0 (ENNReal.natCast_ne_top D), mul_one]
        _ ≤ (Fintype.card r.Chal : ℝ≥0∞) * (D : ℝ≥0∞)⁻¹ := mul_le_mul' h1 le_rfl
        _ = (D : ℝ≥0∞)⁻¹ * (Fintype.card r.Chal : ℝ≥0∞) := mul_comm _ _, below_of_small hD h.2⟩

end Blocks
