-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/IndexM.lean: the integer matrix that holds the model's index is 0 outside its range, and
the test of WF on a matrix is decidable.

The index of the model is the family of its tensors (Inst/Model/Program.lean: `Index ppref`).
 * `matrixRef_zero`: the integer matrix that holds the tensors (Inst/Model/MatrixOf.lean:
   `matrixRef`) is 0 outside the h rows and 2^k columns.
 * `WFP`: the form of WF with numbered pairs of rows (`wfp_iff`; `Bridge.wfw_iff_pairs`), a
   statement with bounded quantifiers, so it is decidable.
Notation:
  `ppref`: `Params`; the reference parameters (Inst/Model/Program.lean).
  `hRef`, `kRef`: natural numbers; the h and k of this head (Inst/Model/Layout.lean).
  in range, of an entry: at a row y < `hRef` and a column c < 2^`kRef`.
-/
import Inst.Model.MatrixOf
import Inst.Model.LayoutBridge
import Inst.Model.LayoutSanity
import Code.Circle
import Code.FieldEnum

set_option autoImplicit false

namespace Inst.Model

open Layout Blocks Code

/-! ## 1. The integer matrix is 0 outside its range -/

namespace IndexM

theorem tOf_le (c : Coord) (left : ℕ) : tOf c left ≤ left := by
  unfold tOf
  cases c.kind
  · exact Nat.min_le_right _ _
  · exact Nat.min_le_right _ _
  · show (if Nat.clog 2 c.R ≤ left then Nat.clog 2 c.R else 0) ≤ left
    split_ifs with h
    · exact h
    · exact Nat.zero_le _

theorem sum_bits_le : ∀ (cs : List Coord) (left : ℕ), (bits cs left).sum ≤ left
  | [], _ => Nat.zero_le _
  | c :: cs, left => by
      have h1 := tOf_le c left
      have h2 := sum_bits_le cs (left - tOf c left)
      simp only [bits, List.sum_cons]
      omega

theorem findUnit_none (k : ℕ) :
    ∀ (us : List Tagged) (y : ℕ), MatrixOf.offT k us us.length ≤ y → findUnit k us y = none
  | [], _, _ => rfl
  | U :: us, y, h => by
      have e : MatrixOf.offT k (U :: us) (U :: us).length =
          rows k U.1 + MatrixOf.offT k us us.length := by
        simp [MatrixOf.offT]
      rw [e] at h
      rw [findUnit, if_neg (by omega)]
      exact findUnit_none k us _ (by omega)

/-- The matrix that holds the tensors is 0 outside the h rows and 2^k columns. -/
theorem matrixRef_zero (i : Index ppref) (y c : ℕ) (h : ¬ (y < hRef ∧ c < 2 ^ kRef)) :
    matrixRef i y c = 0 := by
  unfold matrixRef matrixOf
  by_cases hy : y < hRef
  · have hc : ¬ c < 2 ^ kRef := fun hc => h ⟨hy, hc⟩
    cases findUnit kRef (tagged ppref i.val) y with
    | none => rfl
    | some Ur =>
      obtain ⟨U, r⟩ := Ur
      show (if c < 2 ^ (bits U.1.coords kRef).sum then _ else 0) = 0
      rw [if_neg]
      intro hlt
      exact hc (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (sum_bits_le _ _)))
  · have hlen : (tagged ppref i.val).length = (units ppref).length := by
      rw [← MatrixOf.tagged_fst ppref i.val, List.length_map]
    have hoff : MatrixOf.offT kRef (tagged ppref i.val) (tagged ppref i.val).length ≤ y := by
      rw [MatrixOf.offT_eq, MatrixOf.tagged_fst, hlen, Sanity.units_total.1, Sanity.units_total.2]
      have : (3076080 : ℕ) ≤ hRef := by decide
      omega
    rw [findUnit_none kRef _ y hoff]

/-! ## 2. WF with numbered pairs of rows -/

/-- WF with numbered pairs of rows: a statement with bounded quantifiers. As in `WFW`
(Inst/Model/Layout.lean), of the entries in range: all lie in [−2^7, 2^7), and b0 + 256 b1 ∈ [−2^12,
2^12) for the entries b0, b1 in every column of every pair of rows that holds the bytes of two-byte
weights; here the pair with the number q < `m2` has the rows `Bridge.y0`, `Bridge.y1`. -/
def WFP (W : Mat) : Prop :=
  (∀ y < hRef, ∀ c < 2 ^ kRef, -2 ^ 7 ≤ W y c ∧ W y c < 2 ^ 7) ∧
  ∀ q < m2 kRef (units ppref), ∀ c < 2 ^ kRef,
    -2 ^ 12 ≤ W (Bridge.y0 ppref kRef q) c + 256 * W (Bridge.y1 ppref kRef q) c ∧
    W (Bridge.y0 ppref kRef q) c + 256 * W (Bridge.y1 ppref kRef q) c < 2 ^ 12

/-- The test is decided by going through the rows, columns and pairs. It is never unfolded in a
proof: the numbers are too large. -/
@[irreducible] def decWFP (W : Mat) : Decidable (WFP W) := by
  unfold WFP
  infer_instance

instance (W : Mat) : Decidable (WFP W) := decWFP W

theorem wfp_iff (W : Mat) : WFP W ↔ WFW ppref kRef W hRef := (Bridge.wfw_iff_pairs W).symm

theorem total_le : off kRef (units ppref) (units ppref).length ≤ hRef := by
  rw [Sanity.units_total.1, Sanity.units_total.2]
  decide

/-- `WFP` is about the entries in range only. -/
theorem wfp_congr {W V : Mat} (h : ∀ y < hRef, ∀ c < 2 ^ kRef, W y c = V y c) (hW : WFP W) :
    WFP V := by
  refine ⟨fun y hy c hc => h y hy c hc ▸ hW.1 y hy c hc, fun q hq c hc => ?_⟩
  have hp := Bridge.pair_lt ppref kRef hRef total_le q hq
  rw [← h _ hp.1 c hc, ← h _ hp.2 c hc]
  exact hW.2 q hq c hc

end IndexM

end Inst.Model
