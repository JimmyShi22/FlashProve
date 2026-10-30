-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/BatSmall.lean: THE BATCHING's PLACE AT A LINK's GROUP AS IT IS CLOSED,
AT THE SMALL SIZE, IS PRICED UP TO 2^56 ROWS. A definition, statements and proofs.

`k10_piece_priced` (AtPiecePriced.lean, beside this file) asks a place of
Johnson/Bridge/BatPriced.lean (`BatPlace`: a stage, a radius, a number of rows) that is paid.
  `batSmall k n`: the stage and the radius of `placeSmall k` (GroupSmall.lean), n rows.
    `batSmall_good`: it passes the test on sizes and radius. `batSmall_lst`: the Johnson bound's
    list there is 107. `batSmall_priced`, `batSmall_paid`: the count 107 (n - 1) meets the
    comparison of `BatPlace.priced` for every n up to 2^56. By evaluation in the kernel at the
    numbers, and monotony in n.
Limits. That n is the number of rows that the closing batches is not said here. BatPriced.lean's
own: below two rows the count is 0. Through its imports it stands above the files under ThirdParty/
(lean/LIMITS.md, L15). Nothing on soundness of the protocol.

-/
import Johnson.Bridge.BatPriced
import Johnson.Desc.First.Close.Law.GroupSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb

/-- The batching's place at a link's group as it is closed, at the small size: k row variables, n
rows batched. -/
def batSmall (k n : ℕ) : Johnson.Bridge.BatPlace :=
  ⟨⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, k, 218⟩, 76267, n⟩

theorem batSmall_stage (k n : ℕ) : (batSmall k n).s = (placeSmall k).s := rfl

theorem batSmall_good (k n : ℕ) : (batSmall k n).good = true := by
  show (Johnson.Top.H.sizedB (batSmall 0 0).s && Johnson.Top.H.inJB (batSmall 0 0).s 76267) = true
  decide +kernel

theorem batSmall_lst (k n : ℕ) : (batSmall k n).s.lstJ (batSmall k n).e = 107 := by
  show listMax (2 ^ 18) (batSmall 0 0).s.d 76267 = 107
  decide +kernel

/-- Up to 2^56 rows the count is priced. -/
theorem batSmall_priced (k n : ℕ) (hn : n ≤ 2 ^ 56) : (batSmall k n).priced = true := by
  unfold Johnson.Bridge.BatPlace.priced Johnson.Bridge.BatPlace.cnt
  rw [batSmall_lst]
  refine decide_eq_true ?_
  show 107 * (n - 1) * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65)
  have h1 : n - 1 ≤ 2 ^ 56 := le_trans (Nat.sub_le _ _) hn
  have h2 : 107 * (n - 1) * 2 ^ 193 ≤ 107 * 2 ^ 56 * 2 ^ 193 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  have h3 : 107 * 2 ^ 56 * 2 ^ 193 + 3 * (1 + 0) * Cb.Gl.p ^ 3 ≤ Cb.Gl.p ^ 3 * 2 ^ (0 + 65) := by
    decide +kernel
  exact le_trans (Nat.add_le_add_right h2 _) h3

theorem batSmall_paid (k n : ℕ) (hn : n ≤ 2 ^ 56) : (batSmall k n).Paid :=
  Johnson.Bridge.BatPlace.paid (batSmall_good k n) (batSmall_priced k n hn)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.batSmall_good
#print axioms VerifiableInference.Desc.First.Close.batSmall_lst
#print axioms VerifiableInference.Desc.First.Close.batSmall_paid
