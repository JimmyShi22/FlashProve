-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerFiveApartOwed.lean: ONE TEST ON THE NUMBERING OF THE WITNESS's MESSAGES,
AND WHAT IS OWED FROM ITS ACCEPT, AS A PROPOSITION BY def: NO PROOF HERE. The shared chain's laws
ask five things of the numbering arr: that the three messages of the shared chain (o_u, o_omega,
o_sp) bear three numbers, and that neither W's message nor the index masks' message of the first
chain bears the number of o_u or of o_sp. All five follow where the five seats bear five numbers.
That is one Bool: harrB (Johnson/P5T/ArrApart.lean) at five names.

  fiveTen N       the seat of each of the five names: W's, the index masks', the three tenants
  fiveAll         the five names
  FiveApartOwed   harrB arr (fiveTen N) fiveAll = true gives the five sentences in the form in which
                  ledger_whole asks them
What is not claimed. That the test accepts at a real list of rounds. Nothing on soundness.

-/
import Johnson.P5T.ArrApart
import Johnson.Desc.Shared.BordersShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc.Shared

/-- The seat of each of the five names. -/
def fiveTen (N : NumbersS) : Option (Option Msg2) → ℕ × ℕ
  | none => N.w
  | some none => N.index
  | some (some m) => N.tenant m

/-- The five names. -/
def fiveAll : List (Option (Option Msg2)) :=
  [none, some none, some (some .oU), some (some .oOmega), some (some .oSp)]

/-- OWED: where the five seats bear five numbers, the five sentences that the ledger's top asks. -/
def FiveApartOwed : Prop :=
  ∀ (arr : ℕ → ℕ → ℕ) (N : NumbersS), P5T.harrB arr (fiveTen N) fiveAll = true →
    (∀ m m' : Msg2, arr (N.tenant m).1 (N.tenant m).2 = arr (N.tenant m').1 (N.tenant m').2 →
      m = m') ∧
    arr N.w.1 N.w.2 ≠ arr (N.tenant .oU).1 (N.tenant .oU).2 ∧
    arr N.w.1 N.w.2 ≠ arr (N.tenant .oSp).1 (N.tenant .oSp).2 ∧
    arr N.index.1 N.index.2 ≠ arr (N.tenant .oU).1 (N.tenant .oU).2 ∧
    arr N.index.1 N.index.2 ≠ arr (N.tenant .oSp).1 (N.tenant .oSp).2

end Desc.K14.Law
