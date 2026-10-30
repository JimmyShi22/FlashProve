-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/LinkPricesRecord.lean: at the full-size lines of the setting "record with work" the
price of a link's fold point covers the proof library's numbers at the typed radius.

By evaluations of the planner in Lean's kernel at `recordSet` and `recordTable`
(OnBytes/Params/EntryStagesRecord.lean): the table's two integers are the same; a later test's count
is not marked bad; the price of a link's fold point is not marked bad, nor are the two prices of a
link's lists of 62 columns (`rl_facts`). So by `link_point_covers_johnson`
(OnBytes/Params/LinkPrices.lean), at `recordRadius` (OnBytes/Params/RecordRound.lean) for both
tables, the price of the fold point covers (v + 2 (v B + L v)) / q with B the library's
`Cb.bchksBound (2 ^ 32) 446693374 recordRadius` and L its `Cb.listMax (2 ^ 32) 3848273922
recordRadius` (`record_link_point_covers`).

Main theorems: `rl_facts`, `record_link_point_covers`.
What is not claimed: what the heads of OnBytes/Params/LinkPrices.lean and
OnBytes/Params/RecordRound.lean do not claim. The law on the two lists of columns is not drawn here
(OnBytes/Params/EntryCoveredRecord.lean draws it); its marks are evaluated. That the entry's plan
has a round at this price (OnBytes/Params/EntryPricesRecord.lean shows it). The small files. For
proofs only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.LinkPrices
import OnBytes.Params.RecordRound

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- At the full-size lines of the setting "record with work": the two integers of the table are the
same; a later test's count is not marked bad; the price of a link's fold point is not marked bad;
and the two prices of a link's lists of 62 columns are not. -/
theorem rl_facts : recordTable.distances.mLater = recordTable.distances.mOnce ∧
    (tableAnalysis recordSet recordTable).later.count.bad = false ∧
    (fieldError recordSet recordTable.v +
      tableFoldError recordSet recordTable (tableAnalysis recordSet recordTable).once +
      tableFoldError recordSet recordTable
        (tableAnalysis recordSet recordTable).later).bad = false ∧
    (Bound.pow (tableAnalysis recordSet recordTable).later.agree 62).bad = false ∧
    (Bound.pow (tableAnalysis recordSet recordTable).once.agree 62).bad = false := by
  decide +kernel

/-- **At these lines the price of a link's fold point covers the library's numbers at the typed
radius, for both tables.** -/
theorem record_link_point_covers :
    ((recordTable.v : ℝ) +
        ((recordTable.v : ℝ) * Cb.bchksBound (2 ^ 32) 446693374 recordRadius +
          (Cb.listMax (2 ^ 32) 3848273922 recordRadius : ℝ) * (recordTable.v : ℝ)) +
        ((recordTable.v : ℝ) * Cb.bchksBound (2 ^ 32) 446693374 recordRadius +
          (Cb.listMax (2 ^ 32) 3848273922 recordRadius : ℝ) * (recordTable.v : ℝ))) /
        (recordSet.cardE : ℝ) ≤
      (((fieldError recordSet recordTable.v +
        tableFoldError recordSet recordTable (tableAnalysis recordSet recordTable).once +
        tableFoldError recordSet recordTable
          (tableAnalysis recordSet recordTable).later).error.val : ℚ) : ℝ) := by
  obtain ⟨m0, g0, g, _, _⟩ := rl_facts
  have hk : 0 < (wordOf recordTable.code).k := by
    rw [rr_word]
    decide
  have h0 : (recordRadius : ℝ) ≤
      (1 - (wordOf recordTable.code).agreeAt recordTable.distances.mLater true) *
        ((wordOf recordTable.code).n : ℝ) := by
    rw [m0]
    exact record_radius_le
  have h := link_point_covers_johnson (s := recordSet) (T := recordTable) (e1 := recordRadius)
    (e0 := recordRadius) (by decide) rr_set.1 rr_once.1 g0 hk record_radius_le h0 g
  rw [rr_word] at h
  exact h

end OnBytes.Params

#print axioms OnBytes.Params.rl_facts
#print axioms OnBytes.Params.record_link_point_covers
