-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/RowsShapedOf.lean: «THE ROWS' SHAPES ARE THE PLAN's SEATS'»
(P1Opts.RowsShaped, Johnson/Top/H0/Opts/SomeAtRows.lean) FROM ITS FORM LIST BY LIST. General. NO
BLOCK IMPORTS THIS FILE.
  rowsShaped_of   where at every sending k that has a seat with a sample the first chain's k-th
                  row's sampled shapes are that sending's seats' shapes, in order: RowsShaped
The premise is the end of P1Opts.rows_at_plan (Johnson/Top/H0/Opts/RowsAtPlan.lean). No soundness
is claimed.
-/
import Johnson.Top.H0.Opts.SomeAtRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open P5T (PSeat mineAt firstRows)

theorem rowsShaped_of {rows : List Johnson.G.SendRow} {ps : List PSeat}
    (h : ∀ k, mineAt ps k ≠ [] →
      ((firstRows rows)[k]?).map (fun r => r.sampled.map fun z => z.1) =
        some ((mineAt ps k).map (·.shape))) : RowsShaped rows ps := by
  intro k j p hp
  have hne : mineAt ps k ≠ [] := by
    intro e
    rw [e] at hp
    cases hp
  obtain ⟨row, hrow, e⟩ := Option.map_eq_some_iff.1 (h k hne)
  have e2 : (row.sampled[j]?).map (fun z => z.1) = some p.shape := by
    have e1 := congrArg (fun L => L[j]?) e
    simp only [List.getElem?_map, hp, Option.map_some] at e1
    exact e1
  obtain ⟨y, hy, e3⟩ := Option.map_eq_some_iff.1 e2
  refine ⟨y.2, ?_⟩
  rw [hrow]
  show row.sampled[j]? = some (p.shape, y.2)
  rw [hy, ← e3]

end P1Opts

#print axioms P1Opts.rowsShaped_of
