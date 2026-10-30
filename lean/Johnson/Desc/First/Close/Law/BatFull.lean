-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BatFull.lean: THE BATCHING's PLACE AT A LINK's GROUP AS IT IS CLOSED,
AT THE FULL SIZE, IS PRICED UP TO 2^57 ROWS. A definition, statements and proofs.

`k10_piece_priced` (AtPiecePriced.lean, beside this file) asks a place of
Johnson/Bridge/BatPriced.lean (`BatPlace`: a stage, a radius, a number of rows) that is paid.
  `batFull k n`: the stage and the radius of `placeFull k` (GroupFull.lean), n rows. `batFull_good`:
    it passes the test on sizes and radius. `batFull_lst`: the Johnson bound's list there is 54.
    `batFull_priced`, `batFull_paid`: the count 54 (n - 1) meets the comparison of `BatPlace.priced`
    for every n up to 2^57. By evaluation in the kernel at the numbers, and monotony in n.
Limits. That n is the number of rows that the closing batches is not said here. BatPriced.lean's
own: below two rows the count is 0. Through its imports it stands above the files under ThirdParty/
(lean/LIMITS.md, L15). Nothing on soundness of the protocol.

-/
import Johnson.Bridge.BatPriced
import Johnson.Desc.First.Close.Law.GroupFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb

/-- The batching's place at a link's group as it is closed, at the full size: k row variables, n
rows batched. -/
def batFull (k n : ℕ) : Johnson.Bridge.BatPlace :=
  ⟨⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 0, k, 219⟩, 2433820, n⟩

theorem batFull_stage (k n : ℕ) : (batFull k n).s = (placeFull k).s := rfl

theorem batFull_good (k n : ℕ) : (batFull k n).good = true := by
  show (Johnson.Top.H.sizedB (batFull 0 0).s && Johnson.Top.H.inJB (batFull 0 0).s 2433820) = true
  decide +kernel

theorem batFull_lst (k n : ℕ) : (batFull k n).s.lstJ (batFull k n).e = 54 := by
  show listMax (2 ^ 23) (batFull 0 0).s.d 2433820 = 54
  decide +kernel

/-- Up to 2^57 rows the count is priced. -/
theorem batFull_priced (k n : ℕ) (hn : n ≤ 2 ^ 57) : (batFull k n).priced = true := by
  unfold Johnson.Bridge.BatPlace.priced Johnson.Bridge.BatPlace.cnt
  rw [batFull_lst]
  refine decide_eq_true ?_
  show 54 * (n - 1) * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65)
  have h1 : n - 1 ≤ 2 ^ 57 := le_trans (Nat.sub_le _ _) hn
  have h2 : 54 * (n - 1) * 2 ^ 193 ≤ 54 * 2 ^ 57 * 2 ^ 193 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  have h3 : 54 * 2 ^ 57 * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65) := by
    decide +kernel
  exact le_trans (Nat.add_le_add_right h2 _) h3

theorem batFull_paid (k n : ℕ) (hn : n ≤ 2 ^ 57) : (batFull k n).Paid :=
  Johnson.Bridge.BatPlace.paid (batFull_good k n) (batFull_priced k n hn)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.batFull_good
#print axioms VerifiableInference.Desc.First.Close.batFull_lst
#print axioms VerifiableInference.Desc.First.Close.batFull_paid
