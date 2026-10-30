-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatCoins.lean.

What is here. THE OFFSET LAW: the coin that a masked sumcheck's part spends for the hiding
polynomial's coefficient number i (`hidingCoin`, Honest/SumLaw/Statement.lean), and its end values'
mask entries (`endRun`), are members of the list of all coins that the row spends (`spentOf`), at
the place where the part's stretch begins (`spentTo`, RowKit.lean beside this file). Statements and
proofs.

  `sum_coinsIn`   how many coins the part spends
  `hidingCoin_spent`   **the hiding polynomial's coefficients**
  `endRun_spent`   **the end values' mask entries**

Limits. A word on lists of coins alone, general in the row; BUT THE PART STANDS BARE IN THE ROW
HERE: in the row that the frame plays each part is seated in the chain's input (lifted), so these
two laws have no instance there: the like at a seated part is typed in SlotsOwn.lean beside this
file. That a mask row's entry under a slot is the row's coin of that number, that a part's first
slot lies as far behind the row's first as the coins in front of it are many, and what a world holds
under a slot, are not said here. It stands on `spentOf_at`, `runsE_first` and `runsE_length` of
RowKit.lean. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowKit
import Johnson.Desc.ProofFile.Honest.SumLaw.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (Ends ownSlots)
open ProofFile.Honest.SumLaw

variable {V W X : Type}

/-- The part spends its first stretch and, where the call has end values, as many coins more. -/
theorem sum_coinsIn (name endName : String) (J : SumJob W X) (e : Ends)
    (he : J.shape.ends = some e) :
    coinsIn (sumPart (V := V) name endName J) = ownRun J.shape + e.n := by
  show (((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends).map (·.2.e)).sum = _
  rw [he]
  simp [endRuns]

/-- **The coin for the hiding polynomial's coefficient number i is the row's coin number
`spentTo` + the call's lead + i.** k: the part's number in the row. -/
theorem hidingCoin_spent (ps : List (Part V W X)) (c : RowCoins ps) (k : ℕ) (name endName : String)
    (J : SumJob W X) (cp : SumCoins name endName J)
    (hp : rowAt? ps c k = some ⟨sumPart name endName J, cp⟩) (i : ℕ)
    (hi : i < ownSlots J.shape.all) :
    hidingCoin cp i =
      Reading.gl.val ((spentOf ps c).getD (spentTo ps k + (J.shape.lead + i)) zeroE) := by
  have hlt : J.shape.lead + i < ownRun J.shape := by
    unfold ownRun
    omega
  have hc : J.shape.lead + i < coinsIn (sumPart (V := V) name endName J) := by
    show J.shape.lead + i <
      (((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends).map (·.2.e)).sum
    rw [List.map_cons, List.sum_cons]
    show J.shape.lead + i < ownRun J.shape + _
    omega
  rw [spentOf_at ps c k _ cp hp _ hc]
  show Reading.gl.val ((firstRun cp).getD (J.shape.lead + i) zeroE) = _
  exact congrArg Reading.gl.val (runsE_first _ _ _ _ hlt).symm

/-- **The mask entry of end value number i is the row's coin number `spentTo` + the first stretch's
length + i.** -/
theorem endRun_spent (ps : List (Part V W X)) (c : RowCoins ps) (k : ℕ) (name endName : String)
    (J : SumJob W X) (cp : SumCoins name endName J)
    (hp : rowAt? ps c k = some ⟨sumPart name endName J, cp⟩) (e : Ends)
    (he : J.shape.ends = some e) (i : ℕ) (hi : i < e.n) :
    (endRun cp).getD i zeroE = (spentOf ps c).getD (spentTo ps k + (ownRun J.shape + i)) zeroE := by
  have hc : ownRun J.shape + i < coinsIn (sumPart (V := V) name endName J) := by
    rw [sum_coinsIn name endName J e he]
    omega
  rw [spentOf_at ps c k _ cp hp _ hc]
  have e1 : runsE ((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends) cp.2.1 =
      coinsE cp.2.1.1 ++ runsE (endRuns endName J.shape.ends) cp.2.1.2 := rfl
  show _ = (runsE ((name, (⟨0, ownRun J.shape⟩ : Due)) :: endRuns endName J.shape.ends)
    cp.2.1).getD (ownRun J.shape + i) zeroE
  have hl : (coinsE cp.2.1.1).length = ownRun J.shape := by simp [coinsE]
  rw [e1, List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
  unfold endRun
  generalize cp.2.1.2 = q
  revert q
  rw [he]
  intro q
  show (coinsE q.1).getD i zeroE = (coinsE q.1 ++ runsE [] q.2).getD i zeroE
  rw [List.getD_append _ _ _ _ (by simp [coinsE]; exact hi)]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sum_coinsIn
#print axioms ProofFile.Honest.K4.hidingCoin_spent
#print axioms ProofFile.Honest.K4.endRun_spent
