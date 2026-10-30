-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OkOutLaws.lean: what a yes of the test on a chain as read (`okOut`,
OnBytes/Maker/OkOut.lean) says, word by word; and that one word that is not below the prime makes it
say no.

Main names:
  `okRoundOut_iff`, `okOut_iff`: the tests, item by item and word by word. What `okGot` says of an
    item as inequalities of words: `okGot_f`, `okGot_e`, `okGot_answer`
    (OnBytes/Maker/OkViewLaws.lean). `pW` is the prime as a word (OnBytes/Field/Word.lean).
  `okOut_no_of_item`, `okOut_no_of_word`: one item that fails `okGot`, or one word of an opened
    column that is not below the prime, in any round: no.
No letter stands under "there is".

What is not claimed. What OnBytes/Maker/OkOut.lean's head lists as not tested. Nothing on the typed
string that is made of a chain as read. Nothing on soundness.


-/
import OnBytes.Maker.OkOut
import OnBytes.Maker.OkViewLaws

set_option autoImplicit false

namespace OnBytes.Maker

theorem okRoundOut_iff (r : Fmt.RoundOut) :
    okRoundOut r = true ↔
      (∀ g ∈ r.vals, okGot g = true) ∧ ∀ y ∈ r.opens, ∀ c ∈ y.2.2.cols, ∀ w ∈ c, w < pW := by
  unfold okRoundOut
  simp only [Bool.and_eq_true, List.all_eq_true, okF_iff]

/-- **The test on a chain as read, item by item and word by word.** -/
theorem okOut_iff (o : Fmt.ChainOut) :
    okOut o = true ↔
      ∀ r ∈ o.rounds.toList, (∀ g ∈ r.vals, okGot g = true) ∧
        ∀ y ∈ r.opens, ∀ c ∈ y.2.2.cols, ∀ w ∈ c, w < pW := by
  unfold okOut
  simp only [List.all_eq_true, okRoundOut_iff]

/-- **One item that fails the test: no.** -/
theorem okOut_no_of_item {o : Fmt.ChainOut} {r : Fmt.RoundOut} (hr : r ∈ o.rounds.toList)
    {g : Fmt.ItemValue} (hg : g ∈ r.vals) (hn : okGot g = false) : okOut o = false := by
  cases h : okOut o with
  | false => rfl
  | true =>
    rw [((okOut_iff o).1 h r hr).1 g hg] at hn
    cases hn

/-- **One word of an opened column that is not below the prime: no.** -/
theorem okOut_no_of_word {o : Fmt.ChainOut} {r : Fmt.RoundOut} (hr : r ∈ o.rounds.toList)
    {y : Fmt.Shape × List Nat × Fmt.OpenOut} (hy : y ∈ r.opens) {c : List UInt64}
    (hc : c ∈ y.2.2.cols) {w : UInt64} (hw : w ∈ c) (hn : pW ≤ w) : okOut o = false := by
  cases h : okOut o with
  | false => rfl
  | true => exact absurd (((okOut_iff o).1 h r hr).2 y hy c hc w hw) (UInt64.not_lt.2 hn)

end OnBytes.Maker
