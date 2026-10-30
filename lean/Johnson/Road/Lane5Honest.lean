-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5Honest.lean

The matrices of the honest trace of a true request are small at every place, also where no cell
stands.

"Cm.Seg.toMat" lays a trace's cells at their places and puts 0 everywhere else. The library bounds
the honest trace's matrices inside the shapes ("Cm.Seg.TS.model_true"). Together: every entry is
below 129.

Main theorem:
* "honest_small": at a lawful table and a true request, for all (segment, row, column).

Why. A witness for the statements of Lane5Top.lean reads lists of matrices back out of these
matrices. Some of those statements ask a bound, or an equation between two lists, at all rows and
columns: with this lemma the lists need not be cut to any shape.

Not claimed: anything on matrices other than the honest trace's.
-/
import Johnson.Road.Lane5Plain

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-- **Every entry of the honest trace's matrices is below 129 in absolute value.** -/
theorem honest_small {s : Cm.Scales} {i : Cm.Idx} {x : Instance ppref} (hs : s.Lawful)
    (ht : Cm.TrueAt s.kap s.nf i x) (a r c : ℕ) :
    |Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 s i x) a r c| < 129 := by
  by_cases e : ∃ n : Cm.Seg.Name, n.Valid Cm.Seg.Hd.plain ∧ n.place = (a, r, c)
  · obtain ⟨n, hn, hp⟩ := e
    have hI : Cm.Seg.InShape (a, r, c) := hp ▸ Cm.lay_inShape _ (laws_plain s).ok n hn
    exact ((Cm.Seg.TS.model_true s hs i x).2 ht).1 (a, r, c) hI
  · have h0 : Cm.Seg.at' (Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 s i x)) (a, r, c) = 0 :=
      Cm.lay_toMat_off Cm.Seg.Hd.plain (Cm.trace2 s i x) (a, r, c) e
    have h1 : Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 s i x) a r c = 0 := h0
    rw [h1]
    norm_num

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.honest_small
