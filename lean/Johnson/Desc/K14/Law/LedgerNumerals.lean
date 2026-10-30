-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerNumerals.lean: THE CONDITIONS ON NUMBERS THAT THE LAW AT "LIN point" ASKS
OF THE STORED TABLE's CODE, AT THE RELEASE's TABLE AND THE WRITTEN RADIUS 2852142980. Theorems.

WHY. ledger_whole (Johnson/Desc/K14/Law/LedgerWhole.lean) hands through five premises that speak of
numbers alone: ha, hk, hr, hJ, and, on the decoder's radius eM, hle and hM. Under indexB S = true
(the table has 2 ^ 32 positions and messages of 446693375 words, in 11 row variables) they are
comparisons of numerals.
  numerals_of_index   ha, hk, hr, hJ.
  radius_room         hle and hM at eM := 2852142980: the written radius is itself a radius at which
                      the decoder may stand (it lies below the code's distance 3848273922).
What is not claimed. That eM has to be that number: every eM from 2852142980 to 3848273921 meets
hle and hM. That the seated shape passes indexB. Nothing on soundness.

-/
import Johnson.HB.LLHARD.K14Bad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice Cb

/-- **The four conditions on the code's numbers.** -/
theorem numerals_of_index {S : LinShape} (h : indexB S = true) :
    S.fold.index.code.logN ≤ 32 ∧
    0 < (codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l - 1 ∧
    (codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l ≤
      2 ^ (codeOf S.fold.index.code).a ∧
    InJohnson (2 ^ (codeOf S.fold.index.code).a)
      (2 ^ (codeOf S.fold.index.code).a -
        ((codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l) + 1) 2852142980 := by
  obtain ⟨e1, e2, -⟩ := indexB_sound h
  have e0 : S.fold.index.code.logN = 32 := e1
  refine ⟨Nat.le_of_eq e0, ?_, ?_, ?_⟩
  · rw [e2]
    decide
  · rw [e1, e2]
    decide
  · rw [e1, e2]
    unfold InJohnson
    decide

/-- **The written radius is a radius for the decoder.** -/
theorem radius_room {S : LinShape} (h : indexB S = true) :
    2852142980 ≤ 2852142980 ∧
    2852142980 < 2 ^ (codeOf S.fold.index.code).a -
      ((codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l) + 1 := by
  obtain ⟨e1, e2, -⟩ := indexB_sound h
  refine ⟨Nat.le_refl _, ?_⟩
  rw [e1, e2]
  decide

end Desc.K14.Law

#print axioms Desc.K14.Law.numerals_of_index
#print axioms Desc.K14.Law.radius_room
